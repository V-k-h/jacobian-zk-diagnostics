#!/usr/bin/env python3
"""r1cs_to_iden3 — write the monitor's R1CS JSON as an iden3 binary `.r1cs` file.

The exact inverse of `r1cs_iden3.py`, and the missing half of the common input
layer for head-to-head comparisons: the gnark harness exports our benchmark
instances as monitor JSON, this writer re-emits them in circom's native binary
format, and solver-based tools that consume `.r1cs` (Picus/QED^2 and the
computer-algebra route of AC^4) can then run on the *same* compiled instances
the paper measures — no Circom re-implementation of the circuits, no second
compilation that could change the constraint system under comparison.

WIRE CLASSES. The monitor orders wires [public incl ONE@0][secret][internal];
iden3 orders [ONE=0][public outputs][public inputs][private inputs][internal].
Both start with ONE and agree on the relative order, so emission needs no
permutation — only a split of the monitor's public block (after ONE) into
outputs|inputs. `--pubout K` declares the first K wires after ONE as public
outputs (default 0). For a Picus uniqueness query, make the target wires the
public outputs and the conditioned wires the public inputs; Picus asks exactly
"are the outputs uniquely determined by the inputs?".

FORMAT written (little-endian, version 1, three sections):
    magic "r1cs" | u32 1 | u32 3
    type 1 header : u32 fieldSize | prime[fieldSize] | u32 nWires
                    u32 nPubOut | u32 nPubIn | u32 nPrvIn | u64 nLabels | u32 nConstraints
    type 2 cons   : per constraint, LCs A,B,C — u32 nnz then nnz*(u32 wire, coeff[fieldSize])
                    meaning (A.x)*(B.x) == (C.x)
    type 3 w2l    : u64 identity map wire -> label

Coefficients are reduced into [0, p); the monitor's occasional negative decimal
strings land on the canonical representative. Round-trip equality against
`r1cs_iden3.load` (up to zero-coefficient dropping and term order) is asserted
by `--check`, and `self_test()` runs a small synthetic system through a full
write/read cycle.
"""
import json
import struct
import sys

import r1cs_iden3

MAGIC = b"r1cs"


def _field_size(prime):
    """Bytes per coefficient: prime length rounded up to a multiple of 8 (circom uses 32)."""
    return ((prime.bit_length() + 7) // 8 + 7) // 8 * 8


def _emit_lc(out, terms, prime, fs):
    terms = [(int(w), int(c) % prime) for c, w in terms]
    terms = [(w, c) for w, c in terms if c]
    out.append(struct.pack("<I", len(terms)))
    for w, c in terms:
        out.append(struct.pack("<I", w))
        out.append(c.to_bytes(fs, "little"))


def permute_for_query(sys_, out_wires, in_wires):
    """Reorder wires into iden3 query classes [ONE][outputs][inputs][rest].

    Takes the monitor system plus the wire ids that should act as the public
    outputs (the targets T) and public inputs (the conditioned set F minus ONE)
    of a uniqueness query, and returns an equivalent system with those wires
    moved into the leading blocks and every constraint reindexed. The returned
    dict is ready for dump(..., pubout=len(out_wires)); downstream tools then
    ask precisely "are the targets determined by the conditioned wires?".
    """
    out_wires, in_wires = list(out_wires), list(in_wires)
    if 0 in out_wires or 0 in in_wires:
        raise ValueError("wire 0 is the constant ONE and cannot be an output/input")
    if set(out_wires) & set(in_wires):
        raise ValueError("output and input wire sets overlap")
    head = [0] + out_wires + in_wires
    rest = [w for w in range(sys_["n_wires"]) if w not in set(head)]
    old2new = {old: new for new, old in enumerate(head + rest)}
    cons = [{side: [[c, str(old2new[int(w)])] for c, w in cn[side]]
             for side in ("L", "R", "O")} for cn in sys_["constraints"]]
    n_public = 1 + len(out_wires) + len(in_wires)
    return {
        "prime": sys_["prime"],
        "n_public": n_public, "n_secret": 0,
        "n_internal": sys_["n_wires"] - n_public,
        "n_wires": sys_["n_wires"],
        "public_wire_ids": list(range(n_public)),
        "constraints": cons,
    }


def dump(sys_, path, pubout=0):
    """Write a monitor R1CS dict as an iden3 .r1cs file."""
    prime = int(sys_["prime"])
    fs = _field_size(prime)
    n_wires = sys_["n_wires"]
    n_public = sys_["n_public"]          # includes ONE at wire 0
    if not 0 <= pubout <= n_public - 1:
        raise ValueError(f"pubout {pubout} exceeds the {n_public - 1} non-ONE public wires")
    n_pub_in = n_public - 1 - pubout
    n_prv_in = sys_.get("n_secret", 0)

    header = b"".join([
        struct.pack("<I", fs),
        prime.to_bytes(fs, "little"),
        struct.pack("<IIII", n_wires, pubout, n_pub_in, n_prv_in),
        struct.pack("<Q", n_wires),                       # nLabels: identity labelling
        struct.pack("<I", len(sys_["constraints"])),
    ])

    cons = []
    for c in sys_["constraints"]:
        for side in ("L", "R", "O"):
            _emit_lc(cons, c[side], prime, fs)
    cons = b"".join(cons)

    w2l = b"".join(struct.pack("<Q", w) for w in range(n_wires))

    with open(path, "wb") as f:
        f.write(MAGIC + struct.pack("<II", 1, 3))
        for ty, payload in ((1, header), (2, cons), (3, w2l)):
            f.write(struct.pack("<IQ", ty, len(payload)) + payload)


def _canon(sys_):
    """Canonical form for round-trip comparison: coeffs mod p, zeros dropped, terms sorted."""
    p = int(sys_["prime"])
    cs = []
    for c in sys_["constraints"]:
        cs.append(tuple(
            tuple(sorted((int(w), int(co) % p) for co, w in c[side] if int(co) % p))
            for side in ("L", "R", "O")))
    return p, sys_["n_wires"], sys_["n_public"], tuple(cs)


def check_roundtrip(sys_, path):
    back = r1cs_iden3.load(path)
    assert _canon(sys_) == _canon(back), "round-trip mismatch"


def self_test():
    toy = {
        "prime": "21888242871839275222246405745257275088548364400416034343698204186575808495617",
        "n_public": 2, "n_secret": 1, "n_internal": 1, "n_wires": 4,
        "public_wire_ids": [0, 1],
        "constraints": [
            {"L": [["1", "2"]], "R": [["1", "2"]], "O": [["1", "3"]]},
            {"L": [["-1", "3"], ["5", "0"]], "R": [["1", "1"]], "O": []},
        ],
    }
    import tempfile, os
    with tempfile.NamedTemporaryFile(suffix=".r1cs", delete=False) as f:
        tmp = f.name
    try:
        dump(toy, tmp, pubout=1)
        check_roundtrip(toy, tmp)
        back = r1cs_iden3.load(tmp)
        assert back["n_public"] == 2 and back["n_secret"] == 1
    finally:
        os.unlink(tmp)
    print("self_test OK")


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    opts = [a for a in sys.argv[1:] if a.startswith("--")]
    if not args:
        print("usage: r1cs_to_iden3.py <in.json> <out.r1cs> [--pubout=K] [--check]\n"
              "       r1cs_to_iden3.py <in.json> <out.r1cs> --outputs=ID,.. [--inputs=ID,..] [--check]\n"
              "       r1cs_to_iden3.py --selftest")
        sys.exit(2)
    if "--selftest" in opts:
        self_test()
        return
    pubout = next((int(o.split("=", 1)[1]) for o in opts if o.startswith("--pubout=")), 0)
    outs = next((o.split("=", 1)[1] for o in opts if o.startswith("--outputs=")), None)
    ins = next((o.split("=", 1)[1] for o in opts if o.startswith("--inputs=")), "")
    with open(args[0]) as f:
        sys_ = json.load(f)
    if outs is not None:
        out_wires = [int(w) for w in outs.split(",") if w]
        in_wires = [int(w) for w in ins.split(",") if w]
        sys_ = permute_for_query(sys_, out_wires, in_wires)
        pubout = len(out_wires)
    dump(sys_, args[1], pubout=pubout)
    if "--check" in opts:
        check_roundtrip(sys_, args[1])
        print("round-trip check OK")
    print(f"wrote {args[1]}: {sys_['n_wires']} wires, "
          f"{len(sys_['constraints'])} constraints, pubout={pubout}")


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        self_test()
    else:
        main()
