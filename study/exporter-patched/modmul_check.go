// Patched-side check for the variable-modulus remainder issue: at gnark
// v0.16.2 the shifted hint (q-1, r+m) against ModMul is expected to STILL
// produce a verifying proof (the fix is documentation plus a canonical
// variant), while ModMulCanonical is expected to reject it through
// assertLessThanModulus. Run with: go run . modmul
package main

import (
	"fmt"
	"math/big"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/std/math/emulated"
	"github.com/consensys/gnark/std/math/emulated/emparams"
)

type ModMulCircuit struct {
	A emulated.Element[emparams.Mod1e512] `gnark:",public"`
	B emulated.Element[emparams.Mod1e512] `gnark:",public"`
	M emulated.Element[emparams.Mod1e512] `gnark:",public"`
	R emulated.Element[emparams.Mod1e512] `gnark:",public"`
}

func (c *ModMulCircuit) Define(api frontend.API) error {
	f, err := emulated.NewField[emparams.Mod1e512](api)
	if err != nil {
		return err
	}
	res := f.ModMul(&c.A, &c.B, &c.M)
	f.AssertIsEqual(res, &c.R)
	return nil
}

type ModMulCanonicalCircuit struct {
	A emulated.Element[emparams.Mod1e512] `gnark:",public"`
	B emulated.Element[emparams.Mod1e512] `gnark:",public"`
	M emulated.Element[emparams.Mod1e512] `gnark:",public"`
	R emulated.Element[emparams.Mod1e512] `gnark:",public"`
}

func (c *ModMulCanonicalCircuit) Define(api frontend.API) error {
	f, err := emulated.NewField[emparams.Mod1e512](api)
	if err != nil {
		return err
	}
	res := f.ModMulCanonical(&c.A, &c.B, &c.M)
	f.AssertIsEqual(res, &c.R)
	return nil
}

func recompose(limbs []*big.Int, nb uint) *big.Int {
	out := new(big.Int)
	for i := len(limbs) - 1; i >= 0; i-- {
		out.Lsh(out, nb)
		out.Add(out, limbs[i])
	}
	return out
}

func decompose(v *big.Int, nb uint, limbs []*big.Int) {
	mask := new(big.Int).Lsh(big.NewInt(1), nb)
	mask.Sub(mask, big.NewInt(1))
	rest := new(big.Int).Set(v)
	for i := range limbs {
		limbs[i].And(rest, mask)
		rest.Rsh(rest, nb)
	}
}

func limbMul(a, b []*big.Int) []*big.Int {
	out := make([]*big.Int, len(a)+len(b)-1)
	for i := range out {
		out[i] = new(big.Int)
	}
	for i := range a {
		for j := range b {
			out[i+j].Add(out[i+j], new(big.Int).Mul(a[i], b[j]))
		}
	}
	return out
}

func shiftedMulHint(shiftTarget *big.Int) solver.Hint {
	return func(field *big.Int, inputs, outputs []*big.Int) error {
		nb := uint(inputs[0].Int64())
		nbLimbs := int(inputs[1].Int64())
		nbALen := int(inputs[2].Int64())
		nbQuoLen := int(inputs[3].Int64())
		ptr := 4
		plimbs := inputs[ptr : ptr+nbLimbs]
		ptr += nbLimbs
		alimbs := inputs[ptr : ptr+nbALen]
		ptr += nbALen
		blimbs := inputs[ptr:]
		quoLimbs := outputs[:nbQuoLen]
		remLimbs := outputs[nbQuoLen : nbQuoLen+nbLimbs]
		carryLimbs := outputs[nbQuoLen+nbLimbs:]

		p := recompose(plimbs, nb)
		a := recompose(alimbs, nb)
		b := recompose(blimbs, nb)
		quo, rem := new(big.Int), new(big.Int)
		ab := new(big.Int).Mul(a, b)
		if p.Sign() != 0 {
			quo.QuoRem(ab, p, rem)
		}
		if shiftTarget != nil && p.Cmp(shiftTarget) == 0 {
			if quo.Sign() <= 0 {
				return fmt.Errorf("shift requires quotient >= 1")
			}
			quo.Sub(quo, big.NewInt(1))
			rem.Add(rem, p)
		}
		decompose(quo, nb, quoLimbs)
		decompose(rem, nb, remLimbs)
		lhs := limbMul(alimbs, blimbs)
		rhs := limbMul(quoLimbs, plimbs)
		for i := range remLimbs {
			if i < len(rhs) {
				rhs[i].Add(rhs[i], remLimbs[i])
			} else {
				rhs = append(rhs, new(big.Int).Set(remLimbs[i]))
			}
		}
		carry := new(big.Int)
		for i := range carryLimbs {
			if i < len(lhs) {
				carry.Add(carry, lhs[i])
			}
			if i < len(rhs) {
				carry.Sub(carry, rhs[i])
			}
			carry.Rsh(carry, nb)
			carryLimbs[i].Mod(carry, field)
		}
		return nil
	}
}

var (
	mmM, _ = new(big.Int).SetString("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f", 16)
	mmA, _ = new(big.Int).SetString("123456789abcdef0fedcba9876543210deadbeefcafebabe1234", 16)
	mmB, _ = new(big.Int).SetString("f0e1d2c3b4a5968778695a4b3c2d1e0f1122334455667788aabb", 16)
)

func modmulProve(name string, circuit, assign frontend.Circuit, opts ...solver.Option) {
	sys, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, circuit)
	if err != nil {
		fmt.Printf("PROVE %s: compile error: %v\n", name, err)
		return
	}
	pk, vk, err := groth16.Setup(sys)
	if err != nil {
		fmt.Printf("PROVE %s: setup error: %v\n", name, err)
		return
	}
	full, err := frontend.NewWitness(assign, ecc.BN254.ScalarField())
	if err != nil {
		fmt.Printf("PROVE %s: witness error: %v\n", name, err)
		return
	}
	proof, err := groth16.Prove(sys, pk, full, backend.WithSolverOptions(opts...))
	if err != nil {
		fmt.Printf("PROVE %s: prove REJECTED: %.140s\n", name, err.Error())
		return
	}
	public, _ := full.Public()
	verr := groth16.Verify(proof, vk, public)
	fmt.Printf("PROVE %s: proof produced, verify error=%v (constraints=%d)\n",
		name, verr, sys.GetNbConstraints())
}

func runModMulChecks() {
	el := func(v *big.Int) emulated.Element[emparams.Mod1e512] {
		return emulated.ValueOf[emparams.Mod1e512](v)
	}
	rHonest := new(big.Int).Mod(new(big.Int).Mul(mmA, mmB), mmM)
	rShift := new(big.Int).Add(rHonest, mmM)
	mulHintID := solver.GetHintID(emulated.GetHints()[3]) // mulHint
	honest := &ModMulCircuit{A: el(mmA), B: el(mmB), M: el(mmM), R: el(rHonest)}
	shifted := &ModMulCircuit{A: el(mmA), B: el(mmB), M: el(mmM), R: el(rShift)}
	honestC := &ModMulCanonicalCircuit{A: el(mmA), B: el(mmB), M: el(mmM), R: el(rHonest)}
	shiftedC := &ModMulCanonicalCircuit{A: el(mmA), B: el(mmB), M: el(mmM), R: el(rShift)}

	modmulProve("patched_modmul_honest", &ModMulCircuit{}, honest)
	modmulProve("patched_modmul_shifted", &ModMulCircuit{}, shifted,
		solver.OverrideHint(mulHintID, shiftedMulHint(mmM)))
	modmulProve("patched_modmul_canonical_honest", &ModMulCanonicalCircuit{}, honestC)
	modmulProve("patched_modmul_canonical_shifted", &ModMulCanonicalCircuit{}, shiftedC,
		solver.OverrideHint(mulHintID, shiftedMulHint(mmM)))
}
