// gadgets.go — LIBRARY gadgets isolated as standalone circuits, so a gadget can be
// CERTIFIED on its own before it is granted trusted-leaf status.
//
// Rationale (docs/postmortem-trusted-leaves.md): a trust boundary drawn at a
// SOURCE-CODE boundary ("it came from gnark-std") is meaningless in R1CS, which is one
// flat constraint system. A gadget's soundness lives entirely in the constraints it emits
// into the caller's R1CS — exactly the object the monitor reads. So a gadget is just a
// small circuit, and it should earn leaf status by passing the same audit as a circuit,
// at its own (tiny) scale.
//
// ENCODING. For a FUNCTION-shaped gadget the contract is "outputs are a function of the
// inputs". We declare the gadget's input as the ONLY declared wire and leave the result
// INTERNAL. The determinacy question the engines already ask — "is every internal wire
// determined by the declared inputs?" — is then precisely the gadget's contract, and it
// is answered PROVER-side: an unsound gadget shows up as an inability to prove, with no
// need to discover the attack witness. (GATE-shaped gadgets, whose contract is "rejects
// bad inputs", need adversarial-hint non-vacuity instead — determinacy on a gadget with
// no outputs is vacuously true, which is how "no outputs ⇒ safe" misled us.)
//
// These wrappers use gnark-std only — no private/client dependencies — so they build on
// the DEFAULT target (no `-tags backend`) and are portable. Build with GOWORK=off to
// keep any local go.work out of the picture.
package main

import (
	edcurve "github.com/consensys/gnark-crypto/ecc/twistededwards"
	"github.com/consensys/gnark/frontend"
	tedwards "github.com/consensys/gnark/std/algebra/native/twistededwards"
	"github.com/consensys/gnark/std/hash/mimc"
	"github.com/consensys/gnark/std/hash/poseidon2"
	"github.com/consensys/gnark/std/rangecheck"
	"github.com/consensys/gnark/std/selector"
)

// ScalarMulGadget isolates gnark-std `twistededwards.ScalarMul` (which dispatches to
// `scalarMulFakeGLV`) over BabyJubJub/BN254.
//
// In gnark <= v0.14.0 that routine takes its result point from a HINT and is supposed to
// verify it via a half-GCD decomposition `s1 + s2*S = k*Order` plus a final `res == (0,1)`
// check over the bits of s1,s2. Hints are not binding, and gnark's own halfGCD hint
// documents the hole ("it doesn't work in case the scalar is zero"): with
// s1 = s2 = k = bits = 0 the decomposition constraint degenerates to 0 == 0 for ANY
// scalar, the double-and-add loop only ever selects the identity and never references the
// hinted point, so the final check holds regardless of it. The result point is therefore
// unconstrained — and, being internal here, that is exactly what the determinacy engines
// report as unprovable.
type ScalarMulGadget struct {
	S frontend.Variable `gnark:",secret"` // the scalar — the ONLY declared input
}

func (c *ScalarMulGadget) Define(api frontend.API) error {
	curve, err := tedwards.NewEdCurve(api, edcurve.BN254)
	if err != nil {
		return err
	}
	params := curve.Params()
	base := tedwards.Point{X: params.Base[0], Y: params.Base[1]}
	// The gadget's constraints are emitted by this call; the result wires stay internal
	// and are deliberately not asserted against anything, so nothing but ScalarMul itself
	// can pin them. A sound implementation determines them from S; v0.14.0 does not.
	_ = curve.ScalarMul(base, c.S)
	return nil
}

// DoubleBaseScalarMulGadget is the CONTROL for ScalarMulGadget: the same package, the
// same curve, the same output shape — but HINT-FREE. gnark's `doubleBaseScalarMul` is a
// plain bit-based double-and-add (`api.ToBinary` + `api.Lookup2`), so nothing in it is
// prover-supplied advice.
//
// Its purpose is discriminating power. A certification test that fails on every EC gadget
// is a false-positive machine, not a check: if the control does not certify, then
// ScalarMulGadget's failure says nothing about the halfGCD hole and everything about the
// engine's reach. Comparing the two failures — and their REASONS — is what makes the
// verdict meaningful.
type DoubleBaseScalarMulGadget struct {
	S1 frontend.Variable `gnark:",secret"`
	S2 frontend.Variable `gnark:",secret"`
}

func (c *DoubleBaseScalarMulGadget) Define(api frontend.API) error {
	curve, err := tedwards.NewEdCurve(api, edcurve.BN254)
	if err != nil {
		return err
	}
	params := curve.Params()
	base := tedwards.Point{X: params.Base[0], Y: params.Base[1]}
	dbl := curve.Double(base)
	_ = curve.DoubleBaseScalarMul(base, dbl, c.S1, c.S2)
	return nil
}

// ScalarMul253Gadget is the SECOND control, and it tests the engine rather than gnark.
//
// The hint-free control (DoubleBaseScalarMulGadget) also fails to certify, but its residual
// is entirely attributable to one named cause: `api.ToBinary(s)` defaults to the FIELD
// width (254 bits), which trips the `2^n > p` premise, so the bit-decomposition leaf
// declines and the ladder never gets a pinned starting point. That raises the question the
// whole approach hinges on: can the engines certify ANY sound EC scalar multiplication, or
// is EC arithmetic simply out of reach?
//
// So: the same double-and-add ladder, written with a CANONICAL 253-bit decomposition
// (2^253 < p, so the leaf theorem applies). If this certifies, the engines can prove a
// sound scalar-mul sound, and the certification test discriminates — provided the gadget
// is written with a canonical-width decomposition. If it does not, EC gadgets are beyond
// the current engines and must be recorded as named unverified assumptions.
type ScalarMul253Gadget struct {
	S frontend.Variable `gnark:",secret"`
}

func (c *ScalarMul253Gadget) Define(api frontend.API) error {
	curve, err := tedwards.NewEdCurve(api, edcurve.BN254)
	if err != nil {
		return err
	}
	params := curve.Params()
	base := tedwards.Point{X: params.Base[0], Y: params.Base[1]}
	bits := api.ToBinary(c.S, 253) // canonical width: 2^253 < p, leaf premise holds
	acc := tedwards.Point{X: 0, Y: 1}
	for i := len(bits) - 1; i >= 0; i-- {
		acc = curve.Double(acc)
		sum := curve.Add(acc, base)
		acc = tedwards.Point{
			X: api.Select(bits[i], sum.X, acc.X),
			Y: api.Select(bits[i], sum.Y, acc.Y),
		}
	}
	_ = acc
	return nil
}

// ToBinGadget isolates `api.ToBinary(x, Bits)` alone, to settle what gnark actually emits
// at each width.
//
// gnark's `bits.OmitModulusCheck` documents that a comparison against the native modulus is
// added BY DEFAULT when the requested digit count equals the modulus bitlength, "as there
// are possibly multiple correct binary decompositions ... both a or a+r". If that check is
// present in the R1CS at n=254, then a 254-bit decomposition IS canonical and our
// bit-decomposition leaf declines only because it does not RECOGNISE gnark's
// modulus-comparison pattern — an engine gap, not an unsound gadget. Counting constraints
// at 253 vs 254 settles it: a bare decomposition costs n booleanity + 1 recomposition,
// while a modulus check costs a comparator on top.
type ToBinGadget struct {
	X    frontend.Variable `gnark:",secret"`
	Bits int
}

func (c *ToBinGadget) Define(api frontend.API) error {
	_ = api.ToBinary(c.X, c.Bits)
	return nil
}

func init() {
	extra["tobin253"] = func() frontend.Circuit { return &ToBinGadget{Bits: 253} }
	extraAssign["tobin253"] = func() frontend.Circuit { return &ToBinGadget{X: 7, Bits: 253} }
	extra["tobin254"] = func() frontend.Circuit { return &ToBinGadget{Bits: 254} }
	extraAssign["tobin254"] = func() frontend.Circuit { return &ToBinGadget{X: 7, Bits: 254} }
	extra["scalarmul253"] = func() frontend.Circuit { return &ScalarMul253Gadget{} }
	extraAssign["scalarmul253"] = func() frontend.Circuit { return &ScalarMul253Gadget{S: 42} }
	extra["scalarmul"] = func() frontend.Circuit { return &ScalarMulGadget{} }
	extraAssign["scalarmul"] = func() frontend.Circuit { return &ScalarMulGadget{S: 42} }
	extra["dblscalarmul"] = func() frontend.Circuit { return &DoubleBaseScalarMulGadget{} }
	extraAssign["dblscalarmul"] = func() frontend.Circuit {
		return &DoubleBaseScalarMulGadget{S1: 42, S2: 7}
	}
}

// ─────────────────────────────────────────────────────────────────────────────
// PUBLIC-LIBRARY GADGETS (roadmap item E). Each declares its INPUTS and leaves the
// result internal, so "is every internal wire a function of the declared inputs?" is
// the gadget's actual contract. A wrapper whose declared interface does not cover its
// real input surface produces a meaningless verdict — the circom TreeHasher benchmark
// declares 6 inputs against 618,246 internal wires — so the shape below is deliberate.
// ─────────────────────────────────────────────────────────────────────────────

// MiMCGadget — gnark-std MiMC hash. Pure arithmetic, no hints.
type MiMCGadget struct {
	X frontend.Variable `gnark:",secret"`
}

func (c *MiMCGadget) Define(api frontend.API) error {
	h, err := mimc.NewMiMC(api)
	if err != nil {
		return err
	}
	h.Write(c.X)
	_ = h.Sum()
	return nil
}

// Poseidon2Gadget — gnark-std Poseidon2 (Merkle-Damgard). Pure arithmetic.
type Poseidon2Gadget struct {
	X frontend.Variable `gnark:",secret"`
	Y frontend.Variable `gnark:",secret"`
}

func (c *Poseidon2Gadget) Define(api frontend.API) error {
	h, err := poseidon2.NewMerkleDamgardHasher(api)
	if err != nil {
		return err
	}
	h.Write(c.X, c.Y)
	_ = h.Sum()
	return nil
}

// RangeCheckGadget — gnark-std range check. HINT-BASED, so a prime sweep target.
type RangeCheckGadget struct {
	V    frontend.Variable `gnark:",secret"`
	Bits int
}

func (c *RangeCheckGadget) Define(api frontend.API) error {
	rangecheck.New(api).Check(c.V, c.Bits)
	return nil
}

// MuxGadget — gnark-std selector.Mux, the branch/selector shape that defeated the
// syntactic analyses.
type MuxGadget struct {
	Sel frontend.Variable `gnark:",secret"`
	A   frontend.Variable `gnark:",secret"`
	B   frontend.Variable `gnark:",secret"`
	C   frontend.Variable `gnark:",secret"`
}

func (c *MuxGadget) Define(api frontend.API) error {
	_ = selector.Mux(api, c.Sel, c.A, c.B, c.C)
	return nil
}

func init() {
	extra["mimc"] = func() frontend.Circuit { return &MiMCGadget{} }
	extraAssign["mimc"] = func() frontend.Circuit { return &MiMCGadget{X: 42} }
	// NOTE: gnark v0.14.0's std Poseidon2 rejects BN254 ("field ... not supported"), so the
	// wrapper below is retained for other curves but not registered here.
	extra["rangecheck64"] = func() frontend.Circuit { return &RangeCheckGadget{Bits: 64} }
	extraAssign["rangecheck64"] = func() frontend.Circuit { return &RangeCheckGadget{V: 100, Bits: 64} }
	extra["mux"] = func() frontend.Circuit { return &MuxGadget{} }
	extraAssign["mux"] = func() frontend.Circuit { return &MuxGadget{Sel: 1, A: 10, B: 20, C: 30} }
}
