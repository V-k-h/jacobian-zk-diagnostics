#!/usr/bin/env python3
"""r1cs_iden3 — read the iden3 binary `.r1cs` format into the monitor's R1CS JSON shape.

WHY THIS EXISTS. Every engine in `compose/` — the leaf closure, the derivation certificate,
the multiplicity bounds, the Jacobian finder, the inertness check, the two-engine differential
audit — consumes one thing: an R1CS. They were built against the gnark exporter's JSON, but
nothing in them is gnark-specific. This reader makes that concrete by admitting the OTHER
producer of R1CS in this project:

  * **LLZK / Noir** — `ronin-llzk/r1cs-export` lowers LLZK `r1cs`-dialect MLIR and emits
    iden3 `.r1cs` (`emit_r1cs`). So the whole engine suite now runs on the LLZK frontend
    WITHOUT waiting on the upstream `llzk-opt` `scf.if` work, which blocks the PCL/Picus
    route but not this one.
  * **circom** — iden3 `.r1cs` is circom's native output, so circom circuits come along free.

FORMAT (little-endian throughout):
    magic "r1cs" | u32 version | u32 nSections
    per section: u32 type | u64 size | payload
      type 1 header : u32 fieldSize | prime[fieldSize] | u32 nWires
                      u32 nPubOut | u32 nPubIn | u32 nPrvIn | u64 nLabels | u32 nConstraints
      type 2 cons   : per constraint, three LCs A,B,C — each u32 nnz then nnz*(u32 wire,
                      coeff[fieldSize]) — meaning (A.x)*(B.x) == (C.x)
      type 3 w2l    : wire -> label map (ignored; we key on wire id)

WIRE CLASSES. iden3 orders wires [ONE=0][public outputs][public inputs][private inputs]
[internal], which is exactly the monitor's [public incl ONE@0][secret][internal]. So
n_public = 1 + nPubOut + nPubIn and n_secret = nPrvIn, with no permutation needed. Note the
LLZK exporter writes nPubOut=0, nPubIn=<its public wires>, nPrvIn=0 and lumps the remainder
as internal — which lands correctly under the same rule.
"""
import json
import struct
import sys

MAGIC = b"r1cs"
S_HEADER, S_CONSTRAINTS = 1, 2


def _sections(buf):
    """Yield (type, memoryview payload) for each section."""
    if bytes(buf[:4]) != MAGIC:
        raise ValueError(f"not an iden3 .r1cs file (magic {bytes(buf[:4])!r})")
    version, nsec = struct.unpack_from("<II", buf, 4)
    if version != 1:
        raise ValueError(f"unsupported .r1cs version {version}")
    off = 12
    for _ in range(nsec):
        ty, size = struct.unpack_from("<IQ", buf, off)
        off += 12
        yield ty, buf[off:off + size]
        off += size


def _header(payload):
    field_size, = struct.unpack_from("<I", payload, 0)
    prime = int.from_bytes(bytes(payload[4:4 + field_size]), "little")
    o = 4 + field_size
    n_wires, n_pub_out, n_pub_in, n_prv_in = struct.unpack_from("<IIII", payload, o)
    n_cons, = struct.unpack_from("<I", payload, o + 16 + 8)   # skip u64 nLabels
    return {"field_size": field_size, "prime": prime, "n_wires": n_wires,
            "n_pub_out": n_pub_out, "n_pub_in": n_pub_in, "n_prv_in": n_prv_in,
            "n_constraints": n_cons}


def _constraints(payload, hdr):
    """Parse the constraint section into the monitor's [[coeffDecimal, wireID], ...] shape."""
    fs, off = hdr["field_size"], 0
    out = []
    for _ in range(hdr["n_constraints"]):
        sides = []
        for _side in range(3):
            nnz, = struct.unpack_from("<I", payload, off)
            off += 4
            terms = []
            for _t in range(nnz):
                wire, = struct.unpack_from("<I", payload, off)
                coeff = int.from_bytes(bytes(payload[off + 4:off + 4 + fs]), "little")
                off += 4 + fs
                if coeff:                       # drop explicit zero coefficients
                    terms.append([str(coeff), str(wire)])
            sides.append(terms)
        out.append({"L": sides[0], "R": sides[1], "O": sides[2]})
    return out


def load(path):
    """Read an iden3 .r1cs file and return the monitor's R1CS dict."""
    with open(path, "rb") as f:
        buf = memoryview(f.read())
    hdr = cons = None
    for ty, payload in _sections(buf):
        if ty == S_HEADER:
            hdr = _header(payload)
        elif ty == S_CONSTRAINTS:
            cons_payload = payload
    if hdr is None:
        raise ValueError("no header section")
    cons = _constraints(cons_payload, hdr)
    n_public = 1 + hdr["n_pub_out"] + hdr["n_pub_in"]     # wire 0 (ONE) is public
    n_secret = hdr["n_prv_in"]
    return {
        "prime": str(hdr["prime"]),
        "n_public": n_public,
        "n_secret": n_secret,
        "n_internal": hdr["n_wires"] - n_public - n_secret,
        "n_wires": hdr["n_wires"],
        "public_wire_ids": list(range(n_public)),
        "constraints": cons,
    }


def load_any(path):
    """Dispatch on extension: .r1cs = iden3 binary, anything else = monitor JSON.
    Lets every engine accept either producer with no caller changes."""
    if str(path).endswith(".r1cs"):
        return load(path)
    with open(path) as f:
        return json.load(f)


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("usage: r1cs_iden3.py <in.r1cs> [out.json]")
        sys.exit(2)
    sys_ = load(sys.argv[1])
    if len(sys.argv) > 2:
        with open(sys.argv[2], "w") as f:
            json.dump(sys_, f)
        print(f"wrote {sys.argv[2]}")
    print(f"prime      : {sys_['prime'][:20]}...")
    print(f"wires      : {sys_['n_wires']}  "
          f"(public {sys_['n_public']} incl ONE, secret {sys_['n_secret']}, "
          f"internal {sys_['n_internal']})")
    print(f"constraints: {len(sys_['constraints'])}")
