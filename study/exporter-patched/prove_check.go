// Prove-level check for the patched gadget: the v0.16.2 ScalarMul binds its hints
// through a commitment, so plain R1CS witness export stops at the commitment
// placeholder. The deployed semantics live at the proving layer, where the backend
// computes the commitment — so the vulnerable/patched contrast is measured there:
// honest proving must succeed and verify; the degenerate hint overrides must fail.
//
// Run with: go run . prove
package main

import (
	"fmt"
	"math/big"
	"time"

	ednative "github.com/consensys/gnark-crypto/ecc/bn254/twistededwards"
	ed "github.com/consensys/gnark/std/algebra/native/twistededwards"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
)

func proveCase(name string, assignment frontend.Circuit, expectSuccess bool, opts ...solver.Option) {
	cs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &ScalarCircuit{})
	if err != nil {
		fmt.Printf("PROVE %s: compile error: %v\n", name, err)
		return
	}
	pk, vk, err := groth16.Setup(cs)
	if err != nil {
		fmt.Printf("PROVE %s: setup error: %v\n", name, err)
		return
	}
	full, err := frontend.NewWitness(assignment, ecc.BN254.ScalarField())
	if err != nil {
		fmt.Printf("PROVE %s: witness error: %v\n", name, err)
		return
	}
	started := time.Now()
	proof, err := groth16.Prove(cs, pk, full, backend.WithSolverOptions(opts...))
	elapsed := time.Since(started).Seconds()
	if err != nil {
		fmt.Printf("PROVE %s: prove REJECTED after %.2fs: %.120s (expected success=%v)\n",
			name, elapsed, err.Error(), expectSuccess)
		return
	}
	public, err := full.Public()
	if err != nil {
		fmt.Printf("PROVE %s: public witness error: %v\n", name, err)
		return
	}
	verr := groth16.Verify(proof, vk, public)
	fmt.Printf("PROVE %s: proof produced in %.2fs, verify error=%v (expected success=%v)\n",
		name, elapsed, verr, expectSuccess)
}

func runProveChecks() {
	hints := ed.GetHints()
	base := ednative.GetEdwardsCurve().Base
	for _, scalar := range []int64{0, 12345} {
		var q ednative.PointAffine
		q.ScalarMultiplication(&base, big.NewInt(scalar))
		var qx, qy big.Int
		q.X.BigInt(&qx)
		q.Y.BigInt(&qy)
		honest := &ScalarCircuit{S: scalar, QX: &qx, QY: &qy}
		proveCase(fmt.Sprintf("patched_honest_S=%d", scalar), honest, true)
		proveCase(fmt.Sprintf("patched_zero_decomp_S=%d", scalar), honest, false,
			solver.OverrideHint(solver.GetHintID(hints[0]), zeroHint))
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
			proveCase(fmt.Sprintf("patched_forged_S=%d", scalar),
				&ScalarCircuit{S: scalar, QX: &fx, QY: &fy}, false,
				solver.OverrideHint(solver.GetHintID(hints[0]), zeroHint),
				solver.OverrideHint(solver.GetHintID(hints[1]), forgedHint))
		}
	}
}
