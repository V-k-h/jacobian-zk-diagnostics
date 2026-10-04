// plonk_export.go — compile a circuit to gnark's PLONKish arithmetization
// (SparseR1CS: gates qL*xa + qR*xb + qO*xc + qM*(xa*xb) + qC == 0, plus wiring by
// shared wire id) and dump it in the SAME (L,R,O) JSON the R1CS path uses, so the
// unchanged Jacobian tool consumes it. A PLONK gate maps exactly onto the tool's
// (L.x)(R.x)-(O.x) form:
//
//	L = {xa: qM}, R = {xb: 1}, O = {xa: -qL, xb: -qR, xc: -qO, ONE: -qC}
//	=> (L.x)(R.x) - (O.x) = qM*xa*xb + qL*xa + qR*xb + qO*xc + qC   (the gate)
//
// so the tool's Jacobian row IS the gate gradient. Copy constraints are implicit:
// wires are shared by id across gates. Selectors (qL..qC) are fixed coefficients.
//
//	go run . plonk <circuit> <outdir>
package main

import (
	"encoding/json"
	"fmt"
	"math/big"
	"os"
	"path/filepath"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/backend/witness"
	cs "github.com/consensys/gnark/constraint/bn254"
	csolver "github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/scs"
)

// gnark SCS folds constants into the qC coefficient and reserves no ONE wire, so we add
// a synthetic ONE at wire 0 and shift every original wire id by +1. The declared inputs
// (originally [public, secret, internal] contiguous from 0) then occupy [1 .. nPub+nSec],
// and with ONE at 0 the tool's fixed set range(nPublic+nSecret) = {0..nPub+nSec} pins
// exactly ONE + public + secret.
func writeSCSJSON(r *cs.SparseR1CS, outPath string) error {
	nPub, nSec, nInt := r.GetNbPublicVariables(), r.GetNbSecretVariables(), r.GetNbInternalVariables()
	P := ecc.BN254.ScalarField()
	coeff := func(cID uint32) *big.Int {
		var b big.Int
		r.Coefficients[cID].BigInt(&b)
		return &b
	}
	neg := func(b *big.Int) *big.Int {
		if b.Sign() == 0 {
			return big.NewInt(0)
		}
		return new(big.Int).Sub(P, b)
	}
	id := func(w uint32) string { return fmt.Sprintf("%d", w+1) } // +1 shift; ONE at 0
	out := r1csJSON{
		Prime: P.String(), NPublic: nPub + 1, NSecret: nSec, NInternal: nInt,
		NWires: nPub + nSec + nInt + 1, OutputWireIDs: []int{},
		Note: "PLONKish (gnark SparseR1CS) gates emitted as (L,R,O) triples: a gate " +
			"qL*xa+qR*xb+qO*xc+qM*(xa*xb)+qC=0 becomes L={xa:qM},R={xb:1}," +
			"O={xa:-qL,xb:-qR,xc:-qO,ONE:-qC}; copy constraints are wire-id sharing. " +
			"A synthetic ONE wire is added at id 0 and all gnark wire ids are shifted +1.",
	}
	for i := 0; i <= nPub; i++ {
		out.PublicWireIDs = append(out.PublicWireIDs, i) // 0 == ONE, then declared publics
	}
	for _, c := range r.GetSparseR1Cs() {
		qL, qR, qO, qM, qC := coeff(c.QL), coeff(c.QR), coeff(c.QO), coeff(c.QM), coeff(c.QC)
		L, R, O := []termJSON{}, []termJSON{}, []termJSON{} // empty -> JSON [], not null
		if qM.Sign() != 0 {
			L = append(L, termJSON{qM.String(), id(c.XA)})
			R = append(R, termJSON{"1", id(c.XB)})
		}
		if qL.Sign() != 0 {
			O = append(O, termJSON{neg(qL).String(), id(c.XA)})
		}
		if qR.Sign() != 0 {
			O = append(O, termJSON{neg(qR).String(), id(c.XB)})
		}
		if qO.Sign() != 0 {
			O = append(O, termJSON{neg(qO).String(), id(c.XC)})
		}
		if qC.Sign() != 0 {
			O = append(O, termJSON{neg(qC).String(), "0"}) // ONE == wire 0
		}
		out.Constraints = append(out.Constraints, consJSON{L: L, R: R, O: O})
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

// scsSolveWitness solves the SCS and reconstructs a wire-id-indexed vector by scattering
// the per-gate (L,R,O) column values back onto their (XA,XB,XC) wire ids, then verifies
// every gate vanishes on the reconstructed vector before writing it.
func scsSolveWitness(r *cs.SparseR1CS, w witness.Witness, opts []csolver.Option, outPath string) (int, error) {
	sol, err := r.Solve(w, opts...)
	if err != nil {
		return 0, err
	}
	ss := sol.(*cs.SparseR1CSSolution)
	// +1 shift: synthetic ONE at wire 0, original gnark wire w at index w+1.
	n := r.GetNbPublicVariables() + r.GetNbSecretVariables() + r.GetNbInternalVariables()
	vec := make(fr.Vector, n+1)
	vec[0].SetOne() // ONE
	cons := r.GetSparseR1Cs()
	for i := range cons {
		vec[cons[i].XA+1] = ss.L[i]
		vec[cons[i].XB+1] = ss.R[i]
		vec[cons[i].XC+1] = ss.O[i]
	}
	// self-check: qL*xa + qR*xb + qO*xc + qM*xa*xb + qC == 0 for every gate
	var bad int
	for i := range cons {
		c := cons[i]
		var t, acc, prod fr.Element
		acc.Mul(&r.Coefficients[c.QL], &vec[c.XA+1])
		t.Mul(&r.Coefficients[c.QR], &vec[c.XB+1])
		acc.Add(&acc, &t)
		t.Mul(&r.Coefficients[c.QO], &vec[c.XC+1])
		acc.Add(&acc, &t)
		prod.Mul(&vec[c.XA+1], &vec[c.XB+1])
		t.Mul(&r.Coefficients[c.QM], &prod)
		acc.Add(&acc, &t)
		acc.Add(&acc, &r.Coefficients[c.QC])
		if !acc.IsZero() {
			bad++
		}
	}
	if bad != 0 {
		return bad, fmt.Errorf("reconstruction self-check failed: %d/%d gates nonzero", bad, len(cons))
	}
	return 0, writeWitnessJSON(vec, outPath)
}

func plonkSweep(name, outDir string) {
	if err := os.MkdirAll(outDir, 0o755); err != nil {
		fmt.Fprintf(os.Stderr, "mkdir: %v\n", err)
		os.Exit(1)
	}
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), scs.NewBuilder, pick(name))
	if err != nil {
		fmt.Fprintf(os.Stderr, "compile %s (scs): %v\n", name, err)
		os.Exit(1)
	}
	r := ccs.(*cs.SparseR1CS)
	if err := writeSCSJSON(r, filepath.Join(outDir, "circuit.r1cs.json")); err != nil {
		fmt.Fprintf(os.Stderr, "write scs json: %v\n", err)
		os.Exit(1)
	}
	asg := sample(name)
	if asg == nil {
		fmt.Fprintf(os.Stderr, "no sample assignment for %q\n", name)
		os.Exit(2)
	}
	w, err := frontend.NewWitness(asg, ecc.BN254.ScalarField())
	if err != nil {
		fmt.Fprintf(os.Stderr, "witness: %v\n", err)
		os.Exit(1)
	}
	all := csolver.GetRegisteredHints()

	if _, err := scsSolveWitness(r, w, []csolver.Option{csolver.WithHints(all...)},
		filepath.Join(outDir, "wit.honest.json")); err != nil {
		fmt.Fprintf(os.Stderr, "honest solve: %v\n", err)
		os.Exit(1)
	}

	zeroAll := func(_ *big.Int, _ []*big.Int, out []*big.Int) error {
		for i := range out {
			out[i].SetUint64(0)
		}
		return nil
	}
	opts := []csolver.Option{csolver.WithHints(all...)}
	for _, h := range all {
		opts = append(opts, csolver.OverrideHint(csolver.GetHintID(h), zeroAll))
	}
	if _, err := scsSolveWitness(r, w, opts, filepath.Join(outDir, "wit.degenerate.json")); err != nil {
		fmt.Fprintf(os.Stderr, "degenerate solve: %v (a sound-gadget signal for this circuit)\n", err)
	}

	fmt.Fprintf(os.Stderr, "plonk %s: %d gates, %d wires (pub=%d sec=%d int=%d) -> %s\n",
		name, r.GetNbConstraints(),
		r.GetNbPublicVariables()+r.GetNbSecretVariables()+r.GetNbInternalVariables(),
		r.GetNbPublicVariables(), r.GetNbSecretVariables(), r.GetNbInternalVariables(), outDir)
}
