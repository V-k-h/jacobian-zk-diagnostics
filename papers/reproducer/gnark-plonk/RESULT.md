# PLONKish end-to-end measurement (gnark SparseR1CS)

Same gadget as gnark-scalarmul/, but compiled to gnark's PLONK arithmetization
(SparseR1CS: gates qL*xa + qR*xb + qO*xc + qM*(xa*xb) + qC == 0, wiring by shared
wire id). gnark v0.14.0. Compiles to **4293 gates, 4294 wires**.

Each PLONK gate is emitted as one (L,R,O) triple consumed unchanged by the R1CS-form
Jacobian tool: L={xa:qM}, R={xb:1}, O={xa:-qL, xb:-qR, xc:-qO, ONE:-qC}, so
(L.x)(R.x)-(O.x) = qM*xa*xb + qL*xa + qR*xb + qO*xc + qC is exactly the gate, and the
tool's Jacobian row is the gate gradient. A synthetic ONE wire is added at id 0
(gnark folds constants into qC and reserves no ONE wire); all gnark wire ids shift +1.
Copy constraints are wire-id sharing; selectors qL..qC are fixed coefficients.
Witness reconstructed by scattering the per-gate (L,R,O) column values onto (XA,XB,XC),
verified gate-by-gate in Go before export.

Pipeline (from zk-soundness-monitor/):

    cd frontends/gnark && GOWORK=off go build -o /tmp/zksm-gnark .
    /tmp/zksm-gnark plonk scalarmul /tmp/out
    python3 compose/gnark_jacobian.py /tmp/out/circuit.r1cs.json /tmp/out/wit.<W>.json inputs

| Witness                     | Under-determined advice wires |
|-----------------------------|-------------------------------|
| honest (hints solve)        | none — all 4293 determined     |
| degenerate (hints zeroed)   | 14: [517,518,520,521,523,525,526,527,529,530,531,537,538,542] |

Same bug, same tool, PLONKish arithmetization: honest 0 -> degenerate nonzero, exactly
as in the R1CS case study. Standard PLONK gates (degree 2); custom higher-degree gates
scale the degree budget to the product of gate degrees, and lookups are future work.
