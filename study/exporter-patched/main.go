// Patched-pair exporter: the identical ScalarMul experiments of ../exporter/main.go
// compiled against gnark v0.16.2 (the advisory-fix release), so the vulnerable/patched
// halves of RQ6 run on the same gadget, query, and witness variants.
//
// Expected contrast with v0.14.0: the degenerate hint overrides should either fail to
// solve (the patched decomposition rejects the zero branch) or produce witnesses at
// which the diagnostic reports rigidity. Every outcome, including solve errors, is
// recorded rather than skipped.
package main

import (
	"encoding/json"
	"fmt"
	"math/big"
	"os"
	"path/filepath"
	"runtime"
	"time"

	edid "github.com/consensys/gnark-crypto/ecc/twistededwards"
	ednative "github.com/consensys/gnark-crypto/ecc/bn254/twistededwards"
	ed "github.com/consensys/gnark/std/algebra/native/twistededwards"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/constraint"
	csbn "github.com/consensys/gnark/constraint/bn254"
	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	frontendcs "github.com/consensys/gnark/frontend/cs"
	"github.com/consensys/gnark/frontend/cs/r1cs"
)

type ScalarCircuit struct {
	S      frontend.Variable `gnark:",public"`
	QX, QY frontend.Variable
}

func (c *ScalarCircuit) Define(api frontend.API) error {
	curve, err := ed.NewEdCurve(api, edid.BN254)
	if err != nil {
		return err
	}
	q := curve.ScalarMul(ed.Point{X: curve.Params().Base[0], Y: curve.Params().Base[1]}, c.S)
	api.AssertIsEqual(q.X, c.QX)
	api.AssertIsEqual(q.Y, c.QY)
	return nil
}

func zeroHint(_ *big.Int, _ []*big.Int, outs []*big.Int) error {
	for _, x := range outs {
		x.SetInt64(0)
	}
	return nil
}

type Term struct {
	Wire  int    `json:"wire"`
	Coeff string `json:"coefficient"`
}
type Row struct {
	L []Term `json:"l"`
	R []Term `json:"r"`
	O []Term `json:"o"`
}
type Export struct {
	Name           string   `json:"name"`
	Source         string   `json:"source"`
	Scope          string   `json:"scope"`
	GoVersion      string   `json:"go_version"`
	Gnark          string   `json:"gnark"`
	Prime          string   `json:"prime"`
	Names          []string `json:"names"`
	Values         []string `json:"values"`
	Fixed          []int    `json:"fixed"`
	Targets        []int    `json:"targets"`
	Rows           []Row    `json:"rows"`
	Public         []string `json:"public_names"`
	Secret         []string `json:"secret_names"`
	Solved         bool     `json:"gnark_solve_passed"`
	SolveError     string   `json:"solve_error,omitempty"`
	CompileSeconds float64  `json:"compile_seconds"`
	SolveSeconds   float64  `json:"solve_seconds"`
}

func export(name, scope string, circuit, assignment frontend.Circuit, targetNames []string, options ...solver.Option) error {
	started := time.Now()
	generic, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, circuit)
	if err != nil {
		return err
	}
	compileSeconds := time.Since(started).Seconds()
	cs := generic.(*csbn.R1CS)
	e := Export{CompileSeconds: compileSeconds, Name: name,
		Source: "gnark v0.16.2 native/twistededwards ScalarMul", Scope: scope,
		GoVersion: runtime.Version(), Gnark: "v0.16.2",
		Prime: fr.Modulus().String(), Public: cs.Public, Secret: cs.Secret}

	witness, err := frontend.NewWitness(assignment, ecc.BN254.ScalarField())
	if err != nil {
		return err
	}
	started = time.Now()
	raw, solveErr := cs.Solve(witness, options...)
	e.SolveSeconds = time.Since(started).Seconds()
	if solveErr != nil {
		// The patched circuit rejecting a degenerate override is a result, not a failure.
		e.Solved = false
		e.SolveError = solveErr.Error()
	} else {
		e.Solved = true
		solution := raw.(*csbn.R1CSSolution)
		for i := range solution.W {
			var value big.Int
			solution.W[i].BigInt(&value)
			e.Values = append(e.Values, value.String())
			var wireName string
			if i < len(cs.Public) {
				wireName = cs.Public[i]
				e.Fixed = append(e.Fixed, i)
			} else if i < len(cs.Public)+len(cs.Secret) {
				wireName = cs.Secret[i-len(cs.Public)]
			} else {
				wireName = fmt.Sprintf("internal_%d", i)
			}
			e.Names = append(e.Names, wireName)
			for _, t := range targetNames {
				if wireName == t {
					e.Targets = append(e.Targets, i)
				}
			}
		}
	}
	terms := func(expression constraint.LinearExpression) []Term {
		result := []Term{}
		for _, t := range expression {
			index := t.WireID()
			if t.IsConstant() {
				index = -1
			}
			result = append(result, Term{Wire: index, Coeff: cs.ToBigInt(cs.GetCoefficient(t.CoeffID())).String()})
		}
		return result
	}
	for _, row := range cs.GetR1Cs() {
		e.Rows = append(e.Rows, Row{terms(row.L), terms(row.R), terms(row.O)})
	}
	data, err := json.Marshal(e)
	if err != nil {
		return err
	}
	outDir := os.Getenv("PATCHED_EXPORT_DIR")
	if outDir == "" {
		outDir = "exports-patched"
	}
	if err := os.MkdirAll(outDir, 0755); err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(outDir, name+".json"), append(data, '\n'), 0644); err != nil {
		return err
	}
	fmt.Printf("EXPORTED %s: solved=%v constraints=%d fixed=%v targets=%v err=%q\n",
		name, e.Solved, len(e.Rows), e.Fixed, e.Targets, e.SolveError)
	return nil
}

func must(err error) {
	if err != nil {
		fmt.Fprintln(os.Stderr, "FATAL:", err)
		os.Exit(1)
	}
}

// adviceCommit returns a hint that sets every commitment output to a fixed
// field element, turning the backend-computed challenge into free prover
// advice. The relation analysed under this override is R1CS-with-advice-
// challenge: a strictly stronger prover than the deployed one, which cannot
// choose the challenge. Rigidity verdicts under this override are therefore
// sound for the deployed system; freedom verdicts need not be.
func adviceCommit(value string) func(*big.Int, []*big.Int, []*big.Int) error {
	v, ok := new(big.Int).SetString(value, 10)
	if !ok {
		panic("bad advice constant")
	}
	return func(mod *big.Int, _ []*big.Int, outs []*big.Int) error {
		for _, x := range outs {
			x.Mod(v, mod)
		}
		return nil
	}
}

func runAdviceExports() {
	hints := ed.GetHints()
	base := ednative.GetEdwardsCurve().Base
	commitID := solver.GetHintID(frontendcs.Bsb22CommitmentComputePlaceholder)
	// Two distinct fixed challenges, to expose any challenge-dependence of the
	// rank; both deterministic for reproducibility.
	advice := map[string]string{
		"c1": "12345678910111213141516171819202122232425",
		"c2": "9876543210987654321098765432109876543210987654321",
	}
	for _, scalar := range []int64{0, 12345} {
		var q ednative.PointAffine
		q.ScalarMultiplication(&base, big.NewInt(scalar))
		var qx, qy big.Int
		q.X.BigInt(&qx)
		q.Y.BigInt(&qy)
		honest := &ScalarCircuit{S: scalar, QX: &qx, QY: &qy}
		for tag, val := range advice {
			must(export(fmt.Sprintf("patched_advice_%s_scalar_%d_honest", tag, scalar),
				"Patched relation with the commitment challenge as free advice (fixed value); honest hints",
				&ScalarCircuit{}, honest, []string{"QX", "QY"},
				solver.OverrideHint(commitID, adviceCommit(val))))
			must(export(fmt.Sprintf("patched_advice_%s_scalar_%d_zero_decomp", tag, scalar),
				"Patched relation with the commitment challenge as free advice; decomposition hint zeroed",
				&ScalarCircuit{}, honest, []string{"QX", "QY"},
				solver.OverrideHint(commitID, adviceCommit(val)),
				solver.OverrideHint(solver.GetHintID(hints[0]), zeroHint)))
		}
	}
}

func main() {
	if len(os.Args) > 1 && os.Args[1] == "prove" {
		runProveChecks()
		return
	}
	if len(os.Args) > 1 && os.Args[1] == "advice" {
		runAdviceExports()
		return
	}
	if len(os.Args) > 1 && os.Args[1] == "modmul" {
		runModMulChecks()
		return
	}
	hints := ed.GetHints()
	base := ednative.GetEdwardsCurve().Base
	for _, scalar := range []int64{0, 1, 12345, 54321} {
		var q ednative.PointAffine
		q.ScalarMultiplication(&base, big.NewInt(scalar))
		var qx, qy big.Int
		q.X.BigInt(&qx)
		q.Y.BigInt(&qy)
		assign := &ScalarCircuit{S: scalar, QX: &qx, QY: &qy}
		must(export(fmt.Sprintf("patched_scalar_%d_honest", scalar),
			"Fix S; target unconditioned QX,QY", &ScalarCircuit{}, assign, []string{"QX", "QY"}))
		must(export(fmt.Sprintf("patched_scalar_%d_zero_decomp", scalar),
			"Same relation and statement; decomposition hint outputs zeroed",
			&ScalarCircuit{}, assign, []string{"QX", "QY"},
			solver.OverrideHint(solver.GetHintID(hints[0]), zeroHint)))
		var forged ednative.PointAffine
		forged.ScalarMultiplication(&base, big.NewInt(scalar+1))
		var fx, fy big.Int
		forged.X.BigInt(&fx)
		forged.Y.BigInt(&fy)
		forgedHint := func(_ *big.Int, _ []*big.Int, outs []*big.Int) error {
			outs[0].Set(&fx)
			outs[1].Set(&fy)
			return nil
		}
		if len(hints) > 1 {
			must(export(fmt.Sprintf("patched_scalar_%d_forged", scalar),
				"Same relation and S; Q forged to [S+1]G, decomposition hint zeroed, result hint overridden",
				&ScalarCircuit{}, &ScalarCircuit{S: scalar, QX: &fx, QY: &fy}, []string{"QX", "QY"},
				solver.OverrideHint(solver.GetHintID(hints[0]), zeroHint),
				solver.OverrideHint(solver.GetHintID(hints[1]), forgedHint)))
		}
	}
}
