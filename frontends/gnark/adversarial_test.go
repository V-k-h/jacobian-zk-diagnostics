package main

import (
	"math/big"
	"os"
	"path/filepath"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	cs "github.com/consensys/gnark/constraint/bn254"
	csolver "github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	tedwards "github.com/consensys/gnark/std/algebra/native/twistededwards"
)

// TestAdversarialWitness emits satisfying wire vectors for the isolated ScalarMul gadget at
// TWO points: one from gnark's honest hint solver, and one from the DEGENERATE halfGCD
// branch (s1 = s2 = k = bit = 0).
//
// WHY. The Jacobian finder measures freedom LOCALLY, at whichever witness it is handed. In
// scalarMulFakeGLV the result point is unconstrained only on the degenerate branch, so at an
// honest witness the local rank is (plausibly) full and the output looks determined — which
// is exactly why a whole-circuit run at honest witnesses saw nothing. Feeding the SAME engine
// a witness on the degenerate branch tests whether the analysis was ever the limitation, or
// only the witness supply was.
//
// `solver.OverrideHint` is public gnark API, so this needs nothing but gnark-std: no client
// code, no private backend. Emits <ADV_OUT>/scalarmul.r1cs.json plus honest/degenerate
// witness JSONs for compose/gnark_jacobian.py.
//
//	ADV_OUT=/tmp/adv GOWORK=off go test -run TestAdversarialWitness -v .
func TestAdversarialWitness(t *testing.T) {
	outDir := os.Getenv("ADV_OUT")
	if outDir == "" {
		t.Skip("set ADV_OUT=<dir> to emit R1CS + witnesses")
	}
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &ScalarMulGadget{})
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	r := ccs.(*cs.R1CS)
	if err := writeR1CSJSON(r, filepath.Join(outDir, "scalarmul.r1cs.json")); err != nil {
		t.Fatalf("write r1cs: %v", err)
	}

	w, err := frontend.NewWitness(&ScalarMulGadget{S: 42}, ecc.BN254.ScalarField())
	if err != nil {
		t.Fatalf("witness: %v", err)
	}
	hints := tedwards.GetHints() // [halfGCD, scalarMulHint, decomposeScalar]
	halfGCDID := csolver.GetHintID(hints[0])

	// --- honest: gnark's real hints
	solH, err := r.Solve(w, csolver.WithHints(hints...))
	if err != nil {
		t.Fatalf("honest solve: %v", err)
	}
	if err := writeWitnessJSON(solH.(*cs.R1CSSolution).W,
		filepath.Join(outDir, "scalarmul.honest.wit.json")); err != nil {
		t.Fatalf("write honest witness: %v", err)
	}
	t.Logf("HONEST    : solved, %d wires", len(solH.(*cs.R1CSSolution).W))

	// --- degenerate: the branch gnark's own halfGCD hint documents as broken
	//     ("it doesn't work in case the scalar is zero"). With s1=s2=k=bit=0 the
	//     decomposition constraint collapses to 0==0 for ANY scalar and the
	//     double-and-add loop only ever selects the identity, so the final
	//     res==(0,1) check never references the hinted result point.
	zeroHalfGCD := func(_ *big.Int, _ []*big.Int, out []*big.Int) error {
		for i := range out {
			out[i].SetUint64(0)
		}
		return nil
	}
	solD, err := r.Solve(w, csolver.WithHints(hints...),
		csolver.OverrideHint(halfGCDID, zeroHalfGCD))
	if err != nil {
		t.Fatalf("degenerate solve did NOT satisfy the R1CS: %v", err)
	}
	if err := writeWitnessJSON(solD.(*cs.R1CSSolution).W,
		filepath.Join(outDir, "scalarmul.degenerate.wit.json")); err != nil {
		t.Fatalf("write degenerate witness: %v", err)
	}
	t.Logf("DEGENERATE: solved with s1=s2=k=bit=0, %d wires — the vacuous branch is reachable",
		len(solD.(*cs.R1CSSolution).W))
}
