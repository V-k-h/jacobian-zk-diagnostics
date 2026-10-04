# End-to-end gnark v0.14.0 measurement (real std gadget)

Gadget: `github.com/consensys/gnark/std/algebra/native/twistededwards` `curve.ScalarMul`
on BN254, driven by `frontends/gnark` `ScalarMulGadget` (declared input: the scalar S).
gnark v0.14.0 (< 0.16.2; the vulnerable era). Compiles to **2396 constraints, 2398 wires**.

Pipeline (from `zk-soundness-monitor/`):

    cd frontends/gnark && GOWORK=off go build -o /tmp/zksm-gnark .
    /tmp/zksm-gnark adversarial scalarmul /tmp/out      # gnark compile -> R1CS + witnesses
    python3 compose/gnark_jacobian.py /tmp/out/circuit.r1cs.json /tmp/out/wit.<W>.json inputs

Tool = the augmented-Jacobian rank diagnostic; fix = declared inputs (the scalar S);
question = are the 2396 advice/internal wires determined by S?

| Witness                                   | Under-determined advice wires |
|-------------------------------------------|-------------------------------|
| honest (halfGCD solves normally)          | none — all 2396 determined    |
| halfGCD hint zeroed (s1=s2=k=bits=0)      | 5: [261, 262, 264, 265, 266]  |
| all hints zeroed                          | 4: [261, 262, 265, 266]       |

The halfGCD-degenerate branch is the scalar-decomposition hole gnark's own hint documents
("it doesn't work in case the scalar is zero"): the decomposition constraint degenerates to
0 == 0, the double-and-add loop only selects the identity, and the hinted result point is
never referenced, leaving it unconstrained. Honest 0 -> degenerate 5 is the paper's case-study
signature, here reproduced entirely from public gnark source.

## Adversarial-witness ablation (paper Table: locality)

Full sweep = 20 hint-degeneracy variants (per hint: zeroed, one, edwards-identity, first-zero,
noncanonical-bits, bit-lsb-flip; plus all-hints-zero). 16 are rejected by the constraints
(infeasible — a sound-gadget signal), 4 are satisfiable:

| Witness family                          | Free target wires |
|-----------------------------------------|-------------------|
| honest                                  | 0                 |
| halfGCD hint zeroed                     | 5: [261,262,264,265,266] |
| halfGCD hint, first output zeroed       | 5: same ids       |
| all hints zeroed jointly                | 4: [261,262,265,266] |

## Second-witness confirmation (precision 5/5, no false alarms)

`second_witness_flagged.py circuit.r1cs.json wit.h726531982-zero.json 261 262 264 265 266`

At the degenerate witness exactly 3 rows stay live on the flagged wires (a twisted-Edwards
addition slice; every other row touching them is vacuous 0*(...)=0 on this branch). Re-seeding
wire 261 (+1) and propagating through the live rows yields a full assignment satisfying all
2,396 constraints, identical on the declared input, differing on wires [261,264,265,266] —
an exact two-witness counterexample (same public scalar, different accepted result point).
Naive single-wire perturbation is rejected: the freedom is 2-parameter and coupled.
Negative control: the same constructor fails at the honest witness (rows are binding there).
