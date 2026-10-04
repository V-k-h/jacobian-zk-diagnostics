// adversarial.go — generate ADVERSARIAL witnesses, not just honest ones.
//
// WHY THIS EXISTS. The determinacy oracles (sparse Jacobian rank, inertness) are evaluated AT A
// WITNESS, so they see only the freedom present on the branch that witness lies on. Every witness
// this project ever fed them came from gnark's own solver running honest hints — which by
// construction never visits a degenerate branch. Measured on the isolated fake-GLV scalar
// multiplication: at the honest witness 0 free wires and the defect is invisible; at the
// degenerate one (all halfGCD outputs zero) 5 free and 5 COUPLED, and the gate fails. The analysis
// was adequate; the sampling was not. See docs/postmortem-trusted-leaves.md.
//
// So this is the missing half: a witness GENERATOR. Hints are prover-supplied and non-binding, so
// hint degeneracies are exactly the branches a prover can steer onto, and unlike general branch
// enumeration they are a small, structurally-enumerable set. `solver.OverrideHint` is public API —
// no library patching.
//
// INFEASIBLE VARIANTS ARE A SUCCESS SIGNAL. Forcing a degenerate hint output often makes the system
// unsatisfiable and Solve fails. That means the constraints REJECT the degeneracy, which is what a
// sound gadget should do. Such variants are recorded as "infeasible", not as errors.
//
//	go run . adversarial <circuit> <outdir>
//
// Writes <outdir>/circuit.r1cs.json, one witness per feasible variant, and manifest.json listing
// every variant with its outcome. compose/gnark_sweep.py consumes the manifest.
package main

import (
	"encoding/json"
	"fmt"
	"math/big"
	"os"
	"path/filepath"
	"sync"

	"github.com/consensys/gnark-crypto/ecc"
	cs "github.com/consensys/gnark/constraint/bn254"
	csolver "github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/backend/witness"
	"github.com/consensys/gnark/frontend/cs/r1cs"
)

// A degeneracy strategy rewrites one hint's outputs. Each targets a branch a prover could choose.
type strategy struct {
	name string
	// apply fills `out` degenerately; returns false to skip (e.g. wrong arity for this strategy).
	apply func(out []*big.Int) bool
	// derive replaces apply when set. Some degeneracies are only expressible relative to the
	// HONEST output -- a non-canonical bit decomposition is the honest value plus the modulus,
	// which cannot be written without first knowing the value -- so derive receives the original
	// hint and may run it. Returning an error skips the variant.
	derive func(mod *big.Int, in, out []*big.Int, orig csolver.Hint) error
}

// bitsOf / valueOf treat an output tuple as a little-endian bit vector, the shape produced by
// math/bits.nBits and rangecheck.DecomposeHint.
func valueOf(out []*big.Int) (*big.Int, bool) {
	v := new(big.Int)
	for i := len(out) - 1; i >= 0; i-- {
		if out[i].BitLen() > 1 {
			return nil, false // not a bit vector
		}
		v.Lsh(v, 1)
		v.Or(v, out[i])
	}
	return v, true
}

var strategies = []strategy{
	{"zero", func(out []*big.Int) bool { // the branch that broke fake-GLV: vacuous verification
		for i := range out {
			out[i].SetUint64(0)
		}
		return true
	}, nil},
	{"one", func(out []*big.Int) bool {
		for i := range out {
			out[i].SetUint64(1)
		}
		return true
	}, nil},
	{"edwards-identity", func(out []*big.Int) bool { // (0,1) is the neutral element
		if len(out) != 2 {
			return false
		}
		out[0].SetUint64(0)
		out[1].SetUint64(1)
		return true
	}, nil},
	{"first-zero", func(out []*big.Int) bool { // perturb a single output, not the whole tuple
		if len(out) == 0 {
			return false
		}
		out[0].SetUint64(0)
		return true
	}, nil},
	// The curve-shaped strategies above cannot reach a bit-decomposition hint: zeroing every bit is
	// simply the decomposition of 0, which a correct circuit accepts. The classic under-constraint
	// on such a hint is a NON-CANONICAL decomposition -- bits of v+p, congruent to v but a different
	// vector -- which is only rejected if the circuit range-checks the recomposition.
	{"noncanonical-bits", nil, func(mod *big.Int, in, out []*big.Int, orig csolver.Hint) error {
		if err := orig(mod, in, out); err != nil {
			return err
		}
		v, ok := valueOf(out)
		if !ok {
			return fmt.Errorf("not a bit vector")
		}
		alt := new(big.Int).Add(v, mod)
		if alt.BitLen() > len(out) {
			return fmt.Errorf("v+p does not fit in %d bits", len(out))
		}
		for i := range out {
			out[i].SetUint64(uint64(alt.Bit(i)))
		}
		return nil
	}},
	{"bit-lsb-flip", nil, func(mod *big.Int, in, out []*big.Int, orig csolver.Hint) error {
		if err := orig(mod, in, out); err != nil {
			return err
		}
		if len(out) == 0 || out[0].BitLen() > 1 {
			return fmt.Errorf("not a bit vector")
		}
		out[0].Sub(big.NewInt(1), out[0]) // 0 <-> 1
		return nil
	}},
}

type variant struct {
	Name     string `json:"name"`
	Witness  string `json:"witness,omitempty"`
	Solved   bool   `json:"solved"`
	Outcome  string `json:"outcome"` // "solved" | "infeasible"
	Detail   string `json:"detail,omitempty"`
	HintID   uint32 `json:"hint_id,omitempty"`
	Strategy string `json:"strategy,omitempty"`
}

type manifest struct {
	Circuit     string    `json:"circuit"`
	R1CS        string    `json:"r1cs"`
	NbWires     int       `json:"n_wires"`
	NbConstrain int       `json:"n_constraints"`
	UsedHints   int       `json:"used_hints"`
	Variants    []variant `json:"variants"`
}

func adversarialSweep(name, outDir string) {
	if err := os.MkdirAll(outDir, 0o755); err != nil {
		fmt.Fprintf(os.Stderr, "mkdir: %v\n", err)
		os.Exit(1)
	}
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, pick(name))
	if err != nil {
		fmt.Fprintf(os.Stderr, "compile %s: %v\n", name, err)
		os.Exit(1)
	}
	r := ccs.(*cs.R1CS)
	r1csPath := filepath.Join(outDir, "circuit.r1cs.json")
	if err := writeR1CSJSON(r, r1csPath); err != nil {
		fmt.Fprintf(os.Stderr, "write r1cs: %v\n", err)
		os.Exit(1)
	}
	asg := sample(name)
	if asg == nil {
		fmt.Fprintf(os.Stderr, "no sample assignment for %q (add one to sample()/extraAssign)\n", name)
		os.Exit(2)
	}
	w, err := frontend.NewWitness(asg, ecc.BN254.ScalarField())
	if err != nil {
		fmt.Fprintf(os.Stderr, "witness: %v\n", err)
		os.Exit(1)
	}
	// Every registered hint, so the honest solve works and every hint is a sweep target.
	all := csolver.GetRegisteredHints()
	base := []csolver.Option{csolver.WithHints(all...)}

	m := manifest{Circuit: name, R1CS: filepath.Base(r1csPath),
		NbWires: r.GetNbInternalVariables() + r.GetNbPublicVariables() + r.GetNbSecretVariables()}
	m.NbConstrain = r.GetNbConstraints()

	solveTo := func(v variant, opts []csolver.Option) variant {
		sol, err := r.Solve(w, opts...)
		if err != nil {
			v.Solved = false
			if v.Name == "honest" {
				// No baseline => the sweep is meaningless. NOT a sound-gadget signal: it means
				// the harness cannot solve the circuit at all (a missing hint, an unsupported
				// field, a commitment scheme this path does not set up). Must fail loudly.
				v.Outcome = "harness-error"
				v.Detail = "honest solve failed: " + err.Error()
			} else {
				v.Outcome = "infeasible"
				v.Detail = "constraints reject this degeneracy (a sound-gadget signal)"
			}
			return v
		}
		path := filepath.Join(outDir, "wit."+v.Name+".json")
		if err := writeWitnessJSON(sol.(*cs.R1CSSolution).W, path); err != nil {
			v.Solved, v.Outcome, v.Detail = false, "infeasible", "write: "+err.Error()
			return v
		}
		v.Solved, v.Outcome, v.Witness = true, "solved", filepath.Base(path)
		return v
	}

	m.Variants = append(m.Variants, solveTo(variant{Name: "honest"}, base))

	// Only the hints this circuit actually invokes. Overriding one it never calls re-solves to the
	// identical witness, producing a variant that counts as "solved" while testing nothing -- which
	// is how a sweep reports 77 solved and 0 effective. Restricting here makes the variant count a
	// coverage figure instead of a property of gnark's global hint registry.
	used := invokedHints(r, w, all)
	targets := make([]csolver.Hint, 0, len(used))
	for _, h := range all {
		if used[csolver.GetHintID(h)] > 0 {
			targets = append(targets, h)
		}
	}
	fmt.Fprintf(os.Stderr, "%s: %d of %d registered hints invoked; sweeping those\n",
		name, len(targets), len(all))
	m.UsedHints = len(targets)

	// one variant per (hint, strategy): the prover controls each hint independently
	for _, h := range targets {
		id, orig := csolver.GetHintID(h), h
		for _, st := range strategies {
			fn := func(mod *big.Int, in []*big.Int, out []*big.Int) error {
				if st.derive != nil {
					return st.derive(mod, in, out, orig)
				}
				if !st.apply(out) {
					return fmt.Errorf("strategy %s not applicable", st.name)
				}
				return nil
			}
			v := variant{Name: fmt.Sprintf("h%d-%s", uint32(id), st.name),
				HintID: uint32(id), Strategy: st.name}
			m.Variants = append(m.Variants,
				solveTo(v, append(append([]csolver.Option{}, base...), csolver.OverrideHint(id, fn))))
		}
	}
	// and one variant zeroing EVERY hint at once
	zeroAll := func(_ *big.Int, _ []*big.Int, out []*big.Int) error {
		for i := range out {
			out[i].SetUint64(0)
		}
		return nil
	}
	opts := append([]csolver.Option{}, base...)
	for _, h := range targets {
		opts = append(opts, csolver.OverrideHint(csolver.GetHintID(h), zeroAll))
	}
	m.Variants = append(m.Variants, solveTo(variant{Name: "all-hints-zero", Strategy: "zero"}, opts))

	blob, _ := json.MarshalIndent(m, "", "  ")
	if err := os.WriteFile(filepath.Join(outDir, "manifest.json"), blob, 0o644); err != nil {
		fmt.Fprintf(os.Stderr, "write manifest: %v\n", err)
		os.Exit(1)
	}
	solved, infeasible := 0, 0
	for _, v := range m.Variants {
		if v.Solved {
			solved++
		} else {
			infeasible++
		}
	}
	fmt.Fprintf(os.Stderr, "%s: %d constraints, %d variants (%d solved, %d infeasible) -> %s\n",
		name, m.NbConstrain, len(m.Variants), solved, infeasible, outDir)
}

// usedHints reports which registered hints a circuit actually invokes during an honest solve.
//
// WHY THIS MATTERS FOR COVERAGE. `adversarialSweep` targets every *registered* hint, which is a
// global set, not a per-circuit one. Overriding a hint the circuit never calls re-solves to the
// identical witness, so the variant is counted as "solved" while testing nothing. That is how a
// sweep can report 77 solved variants and 0 effective ones, and why the solved count must never be
// quoted as coverage. Knowing the used set turns "0 effective" from a puzzle into a measurement:
// the degeneracies enumerated simply did not intersect what this circuit calls.
//
// Each hint is wrapped in a recorder that delegates to the original, so the solve stays honest.
//
//	go run . hints <circuit>
func usedHints(name string) {
	asg := sample(name)
	if asg == nil {
		fmt.Fprintf(os.Stderr, "no sample assignment for %q\n", name)
		os.Exit(2)
	}
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, pick(name))
	if err != nil {
		fmt.Fprintf(os.Stderr, "compile: %v\n", err)
		os.Exit(1)
	}
	r := ccs.(*cs.R1CS)
	w, err := frontend.NewWitness(asg, ecc.BN254.ScalarField())
	if err != nil {
		fmt.Fprintf(os.Stderr, "witness: %v\n", err)
		os.Exit(1)
	}

	all := csolver.GetRegisteredHints()
	// The solver runs hints from several goroutines, so the recorder must be synchronised; a plain
	// map here panics with a concurrent write partway through a large circuit.
	var mu sync.Mutex
	fired := map[csolver.HintID]int{}
	opts := []csolver.Option{csolver.WithHints(all...)}
	for _, h := range all {
		id, orig := csolver.GetHintID(h), h
		opts = append(opts, csolver.OverrideHint(id,
			func(mod *big.Int, in, out []*big.Int) error {
				mu.Lock()
				fired[id]++
				mu.Unlock()
				return orig(mod, in, out)
			}))
	}
	if _, err := r.Solve(w, opts...); err != nil {
		fmt.Fprintf(os.Stderr, "honest solve failed: %v\n", err)
		os.Exit(1)
	}

	type row struct {
		Name  string `json:"name"`
		ID    uint32 `json:"id"`
		Calls int    `json:"calls"`
	}
	var used []row
	for _, h := range all {
		id := csolver.GetHintID(h)
		if n := fired[id]; n > 0 {
			used = append(used, row{Name: csolver.GetHintName(h), ID: uint32(id), Calls: n})
		}
	}
	fmt.Fprintf(os.Stderr, "%s: %d of %d registered hints are actually invoked\n",
		name, len(used), len(all))
	enc := json.NewEncoder(os.Stdout)
	enc.SetIndent("", "  ")
	_ = enc.Encode(used)
}


// invokedHints reports how many times each registered hint fires during an honest solve, by wrapping
// every one in a recorder that delegates to the original. The solver runs hints from several
// goroutines, so the counter map must be synchronised.
func invokedHints(r *cs.R1CS, w witness.Witness, all []csolver.Hint) map[csolver.HintID]int {
	var mu sync.Mutex
	fired := map[csolver.HintID]int{}
	opts := []csolver.Option{csolver.WithHints(all...)}
	for _, h := range all {
		id, orig := csolver.GetHintID(h), h
		opts = append(opts, csolver.OverrideHint(id,
			func(mod *big.Int, in, out []*big.Int) error {
				mu.Lock()
				fired[id]++
				mu.Unlock()
				return orig(mod, in, out)
			}))
	}
	if _, err := r.Solve(w, opts...); err != nil {
		fmt.Fprintf(os.Stderr, "invokedHints: honest solve failed: %v\n", err)
		os.Exit(1)
	}
	return fired
}
