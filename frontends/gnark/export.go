// export.go — compile a gnark circuit to R1CS and dump it as JSON for the
// soundness checker (compose/gnark_verify.py). This is the gnark analog of the
// Noir->ACIR->LLZK->R1CS front-half: gnark hands us the R1CS in-process, so
// there is no external lowering pipeline.
//
//	go run . <circuit> <outfile>   # -> writes R1CS JSON to <outfile>
//	  portable toys: linear, bilinear, freesecret, sqrthint
//	  real backend circuits (poseidon, merkle) live in backend_circuits.go,
//	  gated behind `-tags backend` (needs the private backend via go.work).
//	(gnark logs to stdout, so JSON goes to a file to keep it clean.)
//
// JSON shape:
//
//	{ prime, n_public, n_secret, n_internal, n_wires,
//	  public_wire_ids: [...],           // wire 0 is the ONE constant
//	  constraints: [ {L,R,O} ] }        // each of L/R/O is [[coeffDecimal, wireID], ...]
//
// meaning, per constraint: (sum L_i) * (sum R_i) == (sum O_i).
// Wire layout: [public (incl ONE@0)] [secret] [internal].
package main

import (
	"encoding/json"
	"fmt"
	"math/big"
	"os"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/backend/witness"
	"github.com/consensys/gnark/constraint"
	cs "github.com/consensys/gnark/constraint/bn254"
	csolver "github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
)

// witnessHints are the hint functions the solver must know about to solve the
// sample assignments. Toy hints live here; backend files append their own.
var witnessHints = []csolver.Hint{zeroHint, sqrtHint}

// extra is populated by build-tagged files (e.g. backend_circuits.go) so the
// default build stays free of any private-backend dependency.
var extra = map[string]func() frontend.Circuit{}

// extraAssign is the witness analog of `extra`: a name -> fully-populated
// ASSIGNMENT (a circuit struct with concrete values) that gnark's solver can
// solve to a satisfying wire vector. Populated by build-tagged files for the
// real backend gadgets; the toys are handled inline in sample().
var extraAssign = map[string]func() frontend.Circuit{}

// ---- portable toy circuits --------------------------------------------------

// Linear: Y == 2*X + 3.  X (secret) is uniquely determined by Y (public) => SAFE.
type Linear struct {
	X frontend.Variable `gnark:",secret"`
	Y frontend.Variable `gnark:",public"`
}

func (c *Linear) Define(api frontend.API) error {
	api.AssertIsEqual(c.Y, api.Add(api.Mul(c.X, 2), 3))
	return nil
}

// Bilinear: Y == X*W.  X,W are declared secrets the prover legitimately chooses;
// the internal product is determined by them => SAFE under the advice target.
type Bilinear struct {
	X frontend.Variable `gnark:",secret"`
	W frontend.Variable `gnark:",secret"`
	Y frontend.Variable `gnark:",public"`
}

func (c *Bilinear) Define(api frontend.API) error {
	api.AssertIsEqual(c.Y, api.Mul(c.X, c.W))
	return nil
}

// FreeSecret: Out == X, with an unused secret Y. Y is a legitimately-free
// DECLARED input; it must NOT count as under-constraint (advice target => SAFE;
// witness target => false positive).
type FreeSecret struct {
	X   frontend.Variable
	Y   frontend.Variable
	Out frontend.Variable `gnark:",public"`
}

func (c *FreeSecret) Define(api frontend.API) error {
	api.AssertIsEqual(c.Out, c.X)
	_ = c.Y // intentionally unconstrained
	return nil
}

// sqrtHint is a placeholder hint (never executed — we only compile, never solve).
func sqrtHint(_ *big.Int, _ []*big.Int, out []*big.Int) error {
	out[0].SetInt64(0)
	return nil
}

// SqrtHint: an advice wire w (from a hint) with only w*w == X. The sign of w is
// NOT pinned, so w is genuinely under-constrained — a real soundness bug the
// advice target must catch (=> UNSAFE?).
type SqrtHint struct {
	X frontend.Variable `gnark:",public"`
}

func (c *SqrtHint) Define(api frontend.API) error {
	ws, err := api.NewHint(sqrtHint, 1, c.X)
	if err != nil {
		return err
	}
	api.AssertIsEqual(api.Mul(ws[0], ws[0]), c.X)
	return nil
}

// Range: decompose public X into Bits bits (api.ToBinary adds booleanity +
// recomposition). The bits are advice; given X they are pinned iff 2^Bits <= p —
// the bit-decomposition uniqueness THEOREM (lean/BitDecomp.lean), not an SMT
// query. Small Bits: SMT confirms SAFE; large Bits: SMT hits the wall, theorem
// discharges instantly.
type Range struct {
	X    frontend.Variable `gnark:",public"`
	Bits int
}

func (c *Range) Define(api frontend.API) error {
	api.ToBinary(c.X, c.Bits)
	return nil
}

// zeroHint gives an advice wire the value 0 (a valid witness for the mask in
// both branches; the sign/value is irrelevant — the Jacobian reads freedom off
// the constraint gradient, not the witness value).
func zeroHint(_ *big.Int, _ []*big.Int, out []*big.Int) error {
	out[0].SetInt64(0)
	return nil
}

// Mask reproduces gnark's exact F-2 residual pattern on REAL gnark R1CS: an
// advice wire x (from a hint) constrained ONLY by the mask x*(Sel-1)==0.
//
//	Sel=1 : x*0==0  -> x is UNCONSTRAINED (under-determined) — the dangerous branch
//	Sel=0 : x*(-1)==0 -> x==0 (pinned/determined)
//
// Determinacy of x given {Sel} is thus a per-branch fact; the Jacobian, evaluated
// at the branch-active witness, must flag x FREE at Sel=1 and determined at Sel=0.
type Mask struct {
	Sel frontend.Variable `gnark:",public"`
}

func (c *Mask) Define(api frontend.API) error {
	api.AssertIsBoolean(c.Sel)
	xs, err := api.NewHint(zeroHint, 1)
	if err != nil {
		return err
	}
	api.AssertIsEqual(api.Mul(xs[0], api.Sub(c.Sel, 1)), 0)
	return nil
}

func pick(name string) frontend.Circuit {
	if f, ok := extra[name]; ok {
		return f()
	}
	switch name {
	case "linear":
		return &Linear{}
	case "bilinear":
		return &Bilinear{}
	case "freesecret":
		return &FreeSecret{}
	case "sqrthint":
		return &SqrtHint{}
	case "range8":
		return &Range{Bits: 8}
	case "range96":
		return &Range{Bits: 96}
	case "mask", "mask1", "mask0":
		return &Mask{}
	default:
		fmt.Fprintf(os.Stderr, "unknown circuit %q (toys: linear, bilinear, freesecret, sqrthint; -tags backend: poseidon, merkle)\n", name)
		os.Exit(2)
		return nil
	}
}

// sample returns a fully-populated ASSIGNMENT (concrete values) for `name` that
// gnark's solver can solve to a satisfying wire vector, for the Jacobian
// determinacy test (compose/gnark_jacobian.py). Toys are inline; real backend
// gadgets come from extraAssign. Returns nil if no sample is available.
func sample(name string) frontend.Circuit {
	if f, ok := extraAssign[name]; ok {
		return f()
	}
	switch name {
	case "linear":
		return &Linear{X: 5, Y: 13} // 2*5+3
	case "bilinear":
		return &Bilinear{X: 2, W: 3, Y: 6}
	case "freesecret":
		return &FreeSecret{X: 7, Y: 0, Out: 7} // Y legitimately free
	case "sqrthint":
		return &SqrtHint{X: 0} // hint returns 0; 0*0==0 holds
	case "range8":
		return &Range{X: 100, Bits: 8}
	case "range96":
		return &Range{X: 1234567, Bits: 96}
	case "mask1":
		return &Mask{Sel: 1} // dangerous branch: advice wire x is free
	case "mask0":
		return &Mask{Sel: 0} // safe branch: x pinned to 0
	default:
		return nil
	}
}

// witnessJSON is the satisfying wire vector, indexed by wire id (aligned to the
// R1CS layout emitted by the R1CS-export path).
type witnessJSON struct {
	Prime  string   `json:"prime"`
	NWires int      `json:"n_wires"`
	Values []string `json:"values"` // decimal, values[i] = wire i
}

// exportWitness compiles `name`, solves a sample assignment, and writes the full
// wire vector (gnark's R1CSSolution.W = solver.values) to outPath.
func exportWitness(name, outPath string) {
	asg := sample(name)
	if asg == nil {
		fmt.Fprintf(os.Stderr, "no sample assignment for %q (add one to sample()/extraAssign)\n", name)
		os.Exit(2)
	}
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, pick(name))
	if err != nil {
		fmt.Fprintln(os.Stderr, "compile:", err)
		os.Exit(1)
	}
	w, err := frontend.NewWitness(asg, ecc.BN254.ScalarField())
	if err != nil {
		fmt.Fprintln(os.Stderr, "witness:", err)
		os.Exit(1)
	}
	sol, err := ccs.(*cs.R1CS).Solve(w, csolver.WithHints(witnessHints...))
	if err != nil {
		fmt.Fprintln(os.Stderr, "solve (assignment not satisfying?):", err)
		os.Exit(1)
	}
	vec := sol.(*cs.R1CSSolution).W // full wire vector, indexed by wire id
	if err := writeWitnessJSON(vec, outPath); err != nil {
		fmt.Fprintln(os.Stderr, "write witness:", err)
		os.Exit(1)
	}
	fmt.Fprintf(os.Stderr, "wrote %s (%d wires)\n", outPath, len(vec))
}

// ---- R1CS -> JSON -----------------------------------------------------------

type termJSON [2]string // [coeffDecimal, wireID]
type consJSON struct {
	L []termJSON `json:"L"`
	R []termJSON `json:"R"`
	O []termJSON `json:"O"`
}
type r1csJSON struct {
	Prime         string `json:"prime"`
	NPublic       int    `json:"n_public"`
	NSecret       int    `json:"n_secret"`
	NInternal     int    `json:"n_internal"`
	NWires        int    `json:"n_wires"`
	PublicWireIDs []int  `json:"public_wire_ids"`
	// OutputWireIDs is emitted EMPTY and that is a claim, not a placeholder.
	//
	// The inertness argument for a free wire (lean/Inertness.lean::residual_benign) needs two
	// premises: the wire is inert, and it is not an output. A compiled gnark circuit proven with
	// Groth16 reveals only its public inputs to the verifier; every internal wire is committed
	// inside the proof and read by nothing outside this constraint system. So Out = {} holds, and
	// the second premise is discharged rather than assumed.
	//
	// This is sound ONLY because what is exported here is a WHOLE circuit. Export a gadget's R1CS
	// and Out = {} is false, because the caller reads its outputs -- which is exactly how
	// Veridise's Edwards2Montgomery finding evades an inertness-only argument. Any future exporter
	// that emits a sub-circuit must leave this field absent so the audit reports the assumption
	// instead of silently discharging it.
	OutputWireIDs []int      `json:"output_wire_ids"`
	Note          string     `json:"note,omitempty"`
	Constraints   []consJSON `json:"constraints"`
}

// writeR1CSJSON serializes any bn254 R1CS to the checker's JSON shape. Reusable by
// the compile path and the circuit-agnostic `load` path.
func writeR1CSJSON(r *cs.R1CS, outPath string) error {
	nPub, nSec, nInt := r.GetNbPublicVariables(), r.GetNbSecretVariables(), r.GetNbInternalVariables()
	coeff := func(cID int) string {
		var b big.Int
		r.Coefficients[cID].BigInt(&b)
		return b.String()
	}
	le := func(l constraint.LinearExpression) []termJSON {
		out := make([]termJSON, 0, len(l))
		for _, t := range l {
			out = append(out, termJSON{coeff(t.CoeffID()), fmt.Sprintf("%d", t.WireID())})
		}
		return out
	}
	out := r1csJSON{
		Prime:   ecc.BN254.ScalarField().String(),
		NPublic: nPub, NSecret: nSec, NInternal: nInt, NWires: nPub + nSec + nInt,
		// declared, not omitted -- see the field comment. [] is the claim Out = {}.
		OutputWireIDs: []int{},
		Note: "output_wire_ids is deliberately empty: a whole gnark circuit proven with Groth16 " +
			"exposes only its public inputs, so no internal wire is read outside this constraint " +
			"system. Sub-circuit exports must omit the field instead.",
	}
	for i := 0; i < nPub; i++ {
		out.PublicWireIDs = append(out.PublicWireIDs, i) // wire 0 == ONE
	}
	for _, c := range r.GetR1Cs() {
		out.Constraints = append(out.Constraints, consJSON{L: le(c.L), R: le(c.R), O: le(c.O)})
	}
	f, err := os.Create(outPath)
	if err != nil {
		return err
	}
	defer f.Close()
	enc := json.NewEncoder(f)
	enc.SetIndent("", " ")
	return enc.Encode(out)
}

// writeWitnessJSON writes a solved wire vector (R1CSSolution.W) to the witness JSON shape.
func writeWitnessJSON(vec fr.Vector, outPath string) error {
	out := witnessJSON{Prime: ecc.BN254.ScalarField().String(), NWires: len(vec)}
	for i := range vec {
		var b big.Int
		vec[i].BigInt(&b)
		out.Values = append(out.Values, b.String())
	}
	f, err := os.Create(outPath)
	if err != nil {
		return err
	}
	defer f.Close()
	return json.NewEncoder(f).Encode(out)
}

// loadAndExport is the CIRCUIT-AGNOSTIC path: it reads gnark's own serialized artifacts —
// a compiled constraint system (`ccs.WriteTo`) and a full witness (`w.WriteTo`), which any
// gnark user already produces — solves, and emits the R1CS + solved wire vector. No circuit
// definition, no per-circuit assignment builders. (Custom-hint circuits: the user instead
// calls writeR1CSJSON/writeWitnessJSON from their own harness where their hints are in scope;
// std-hint / hint-free circuits work fully standalone here via witnessHints.)
func loadAndExport(ccsPath, witPath, r1csOut, witOut string) {
	cf, err := os.Open(ccsPath)
	if err != nil {
		fmt.Fprintln(os.Stderr, "open ccs:", err)
		os.Exit(1)
	}
	defer cf.Close()
	ccs := groth16.NewCS(ecc.BN254)
	if _, err := ccs.ReadFrom(cf); err != nil {
		fmt.Fprintln(os.Stderr, "read ccs:", err)
		os.Exit(1)
	}
	r := ccs.(*cs.R1CS)

	wf, err := os.Open(witPath)
	if err != nil {
		fmt.Fprintln(os.Stderr, "open witness:", err)
		os.Exit(1)
	}
	defer wf.Close()
	w, err := witness.New(ecc.BN254.ScalarField())
	if err != nil {
		fmt.Fprintln(os.Stderr, "witness:", err)
		os.Exit(1)
	}
	if _, err := w.ReadFrom(wf); err != nil {
		fmt.Fprintln(os.Stderr, "read witness:", err)
		os.Exit(1)
	}
	sol, err := r.Solve(w, csolver.WithHints(witnessHints...))
	if err != nil {
		fmt.Fprintln(os.Stderr, "solve (witness not satisfying, or missing hints):", err)
		os.Exit(1)
	}
	if err := writeR1CSJSON(r, r1csOut); err != nil {
		fmt.Fprintln(os.Stderr, "write r1cs:", err)
		os.Exit(1)
	}
	if err := writeWitnessJSON(sol.(*cs.R1CSSolution).W, witOut); err != nil {
		fmt.Fprintln(os.Stderr, "write witness:", err)
		os.Exit(1)
	}
	fmt.Fprintf(os.Stderr, "wrote %s + %s (%d wires)\n", r1csOut, witOut, len(sol.(*cs.R1CSSolution).W))
}

// serialize writes gnark's own serialized artifacts (ccs.bin, wit.bin) for a built-in
// circuit — the reference for what a user emits from their harness (`ccs.WriteTo`,
// `fullWitness.WriteTo`) to feed the circuit-agnostic `load` path.
func serialize(name, ccsPath, witPath string) {
	asg := sample(name)
	if asg == nil {
		fmt.Fprintf(os.Stderr, "no sample assignment for %q\n", name)
		os.Exit(2)
	}
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, pick(name))
	if err != nil {
		fmt.Fprintln(os.Stderr, "compile:", err)
		os.Exit(1)
	}
	w, err := frontend.NewWitness(asg, ecc.BN254.ScalarField())
	if err != nil {
		fmt.Fprintln(os.Stderr, "witness:", err)
		os.Exit(1)
	}
	cf, _ := os.Create(ccsPath)
	defer cf.Close()
	if _, err := ccs.WriteTo(cf); err != nil {
		fmt.Fprintln(os.Stderr, "write ccs:", err)
		os.Exit(1)
	}
	wf, _ := os.Create(witPath)
	defer wf.Close()
	if _, err := w.WriteTo(wf); err != nil {
		fmt.Fprintln(os.Stderr, "write wit:", err)
		os.Exit(1)
	}
	fmt.Fprintf(os.Stderr, "wrote %s + %s\n", ccsPath, witPath)
}

func main() {
	if len(os.Args) < 3 {
		fmt.Fprintln(os.Stderr, "usage: go run . <circuit> <outfile>                     # R1CS JSON (built-in circuit)")
		fmt.Fprintln(os.Stderr, "       go run . witness <circuit> <outfile>             # satisfying wire vector (built-in)")
		fmt.Fprintln(os.Stderr, "       go run . load <ccs.bin> <wit.bin> <r1cs.json> <wit.json>  # circuit-agnostic (serialized gnark artifacts)")
		os.Exit(2)
	}
	if os.Args[1] == "adversarial" {
		if len(os.Args) < 4 {
			fmt.Fprintln(os.Stderr, "usage: go run . adversarial <circuit> <outdir>")
			os.Exit(2)
		}
		adversarialSweep(os.Args[2], os.Args[3])
		return
	}
	if os.Args[1] == "plonk" {
		if len(os.Args) < 4 {
			fmt.Fprintln(os.Stderr, "usage: go run . plonk <circuit> <outdir>")
			os.Exit(2)
		}
		plonkSweep(os.Args[2], os.Args[3])
		return
	}
	if os.Args[1] == "hints" {
		if len(os.Args) < 3 {
			fmt.Fprintln(os.Stderr, "usage: go run . hints <circuit>")
			os.Exit(2)
		}
		usedHints(os.Args[2])
		return
	}
	if os.Args[1] == "witness" {
		if len(os.Args) < 4 {
			fmt.Fprintln(os.Stderr, "usage: go run . witness <circuit> <outfile>")
			os.Exit(2)
		}
		exportWitness(os.Args[2], os.Args[3])
		return
	}
	if os.Args[1] == "load" {
		if len(os.Args) < 6 {
			fmt.Fprintln(os.Stderr, "usage: go run . load <ccs.bin> <wit.bin> <r1cs.json> <wit.json>")
			os.Exit(2)
		}
		loadAndExport(os.Args[2], os.Args[3], os.Args[4], os.Args[5])
		return
	}
	if os.Args[1] == "serialize" {
		if len(os.Args) < 5 {
			fmt.Fprintln(os.Stderr, "usage: go run . serialize <circuit> <ccs.bin> <wit.bin>")
			os.Exit(2)
		}
		serialize(os.Args[2], os.Args[3], os.Args[4])
		return
	}
	circuit := pick(os.Args[1])
	outPath := os.Args[2]

	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, circuit)
	if err != nil {
		fmt.Fprintln(os.Stderr, "compile:", err)
		os.Exit(1)
	}
	if err := writeR1CSJSON(ccs.(*cs.R1CS), outPath); err != nil {
		fmt.Fprintln(os.Stderr, "write r1cs:", err)
		os.Exit(1)
	}
	fmt.Fprintf(os.Stderr, "wrote %s (%d constraints)\n", outPath, ccs.GetNbConstraints())
}
