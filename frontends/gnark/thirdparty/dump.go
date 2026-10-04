//go:build ignore

// dump.go — export ANY third-party gnark circuit into the monitor's R1CS JSON.
//
// The engines in compose/ read an R1CS and nothing else, so analysing someone else's circuit needs
// only their constraints. This file is a TEMPLATE you copy into THEIR module, so their gnark version
// is used and no dependency is added to ours (our go.mod must stay portable — see CLAUDE.md).
// It is `//go:build ignore` so our own build skips it.
//
// USAGE
//  1. copy this file into the target module, e.g. cp dump.go <repo>/zzdump.go
//  2. edit the two marked lines: import their package and construct the circuit (+ an optional
//     assignment for a witness)
//  3. cd <repo> && go run zzdump.go            # writes circuit.r1cs.json [and circuit.wit.json]
//  4. python3 compose/gnark_bound.py circuit.r1cs.json
//     python3 compose/gnark_audit.py circuit.r1cs.json circuit.wit.json
//
// It emits exactly the shape compose/ expects:
//
//	{ prime, n_public, n_secret, n_internal, n_wires, public_wire_ids: [...],
//	  constraints: [ {L,R,O} ] }   with each side [[coeffDecimal, wireID], ...]
//
// meaning (ΣL)(ΣR) == (ΣO) per constraint, over the wire layout
// [public (incl ONE@0)] [secret] [internal].
//
// Tested against gnark v0.14–v0.15. Older lines may need the constraint iterator adjusted; if
// GetR1Cs() is absent, use r.GetR1CIterator().
package main

import (
	"encoding/json"
	"fmt"
	"math/big"
	"os"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/constraint"
	cs "github.com/consensys/gnark/constraint/bn254"
	csolver "github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	// >>> EDIT 1: import the package holding the circuit <<<
)

type termJSON [2]string
type consJSON struct {
	L []termJSON `json:"L"`
	R []termJSON `json:"R"`
	O []termJSON `json:"O"`
}
type r1csJSON struct {
	Prime         string     `json:"prime"`
	NPublic       int        `json:"n_public"`
	NSecret       int        `json:"n_secret"`
	NInternal     int        `json:"n_internal"`
	NWires        int        `json:"n_wires"`
	PublicWireIDs []int      `json:"public_wire_ids"`
	Constraints   []consJSON `json:"constraints"`
}
type witJSON struct {
	Prime  string   `json:"prime"`
	NWires int      `json:"n_wires"`
	Values []string `json:"values"`
}

func main() {
	// >>> EDIT 2: the circuit, and optionally a fully-populated assignment for a witness <<<
	var circuit frontend.Circuit = nil   // e.g. &theirpkg.MerkleCircuit{}
	var assignment frontend.Circuit = nil // e.g. &theirpkg.MerkleCircuit{RootHash: ..., ...}

	if circuit == nil {
		fmt.Fprintln(os.Stderr, "edit EDIT 1 and EDIT 2 first")
		os.Exit(2)
	}
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, circuit)
	if err != nil {
		fmt.Fprintf(os.Stderr, "compile: %v\n", err)
		os.Exit(1)
	}
	r := ccs.(*cs.R1CS)
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
	out := r1csJSON{Prime: ecc.BN254.ScalarField().String(),
		NPublic: nPub, NSecret: nSec, NInternal: nInt, NWires: nPub + nSec + nInt}
	for i := 0; i < nPub; i++ {
		out.PublicWireIDs = append(out.PublicWireIDs, i)
	}
	for _, c := range r.GetR1Cs() {
		out.Constraints = append(out.Constraints, consJSON{L: le(c.L), R: le(c.R), O: le(c.O)})
	}
	f, _ := os.Create("circuit.r1cs.json")
	enc := json.NewEncoder(f)
	enc.SetIndent("", " ")
	if err := enc.Encode(out); err != nil {
		fmt.Fprintf(os.Stderr, "encode: %v\n", err)
		os.Exit(1)
	}
	f.Close()
	fmt.Fprintf(os.Stderr, "wrote circuit.r1cs.json (%d constraints, %d wires)\n",
		len(out.Constraints), out.NWires)

	if assignment == nil {
		fmt.Fprintln(os.Stderr, "no assignment given: skipping witness (determinacy + multiplicity still work)")
		return
	}
	w, err := frontend.NewWitness(assignment, ecc.BN254.ScalarField())
	if err != nil {
		fmt.Fprintf(os.Stderr, "witness: %v\n", err)
		os.Exit(1)
	}
	sol, err := r.Solve(w, csolver.WithHints(csolver.GetRegisteredHints()...))
	if err != nil {
		fmt.Fprintf(os.Stderr, "solve: %v\n", err)
		os.Exit(1)
	}
	vec := sol.(*cs.R1CSSolution).W
	wj := witJSON{Prime: ecc.BN254.ScalarField().String(), NWires: len(vec)}
	for i := 0; i < len(vec); i++ {
		var b big.Int
		vec[i].BigInt(&b)
		wj.Values = append(wj.Values, b.String())
	}
	g, _ := os.Create("circuit.wit.json")
	json.NewEncoder(g).Encode(wj)
	g.Close()
	fmt.Fprintf(os.Stderr, "wrote circuit.wit.json (%d wires)\n", len(vec))
}
