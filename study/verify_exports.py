#!/usr/bin/env python3
"""Pin and verify the regenerated exports by canonical digest.

The raw export files embed timing fields (compile_seconds, solve_seconds) and
the Go toolchain version, which vary across machines; the circuit, witness,
and query content is deterministic. The canonical digest is the SHA-256 of
the JSON with those volatile fields removed, serialized with sorted keys.

  python3 verify_exports.py        # verify exports/ against the pinned digests
  python3 verify_exports.py pin    # rewrite results/export-canonical-sha256.json
"""
import json
import hashlib
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PINS = ROOT / "results" / "export-canonical-sha256.json"
VOLATILE = {"compile_seconds", "solve_seconds", "go_version"}


def canonical_digest(path):
    obj = json.loads(Path(path).read_text())
    for key in VOLATILE:
        obj.pop(key, None)
    blob = json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(blob).hexdigest()


def main():
    exports = sorted((ROOT / "exports").glob("*.json"))
    if not exports:
        sys.exit("no exports found; run the exporter first (see Makefile 'study')")
    digests = {f.name: canonical_digest(f) for f in exports}
    if len(sys.argv) > 1 and sys.argv[1] == "pin":
        PINS.write_text(json.dumps(digests, indent=1, sort_keys=True) + "\n")
        print(f"pinned {len(digests)} canonical digests -> {PINS.relative_to(ROOT)}")
        return
    pins = json.loads(PINS.read_text())
    bad = [n for n in pins if digests.get(n) != pins[n]]
    missing = [n for n in pins if n not in digests]
    for n in bad:
        print("MISMATCH", n)
    print(f"pins={len(pins)} ok={len(pins) - len(bad)} "
          f"mismatch={len(bad) - len(missing)} missing={len(missing)}")
    if bad:
        sys.exit(1)


if __name__ == "__main__":
    main()
