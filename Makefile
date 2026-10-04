# One-command reproduction entry points. `make check` is dependency-free
# (Python 3 stdlib); everything else states its requirements.

.PHONY: check tables study advisory lean all

# Fast self-contained verification: no Go, no network. Runs the exhaustive
# F_3/F_257 self-tests of the reference checker, the parabola- and
# Groebner-certificate controls, the synthetic 20-constraint reproducer with
# its Theorem E certificate checks, the taxonomy runs, and the iden3 .r1cs
# round-trip tests.
check:
	python3 study/certificate_checker.py
	python3 -c "import sys; sys.path.insert(0,'study'); import parabola_certificate as m; m.controls()"
	python3 -c "import sys; sys.path.insert(0,'study'); import groebner_slice as m; m.controls()"
	python3 papers/reproducer/toy_hint_gadget.py
	python3 papers/reproducer/taxonomy_runs.py

# Every measured table of the main evaluation (requires Go; fetches gnark
# v0.14.0 through the module system on first run).
tables:
	bash papers/reproducer/run_all.sh

# The certificate study on the deployed ScalarMul gadget: regenerate the
# query-aware exports (gnark v0.14.0), then run the complete affine-line
# search, the parabola certificates, and the Groebner slice elimination.
study:
	cd study/exporter && go build -o /dev/null . && go run .
	cd study && python3 verify_exports.py
	cd study && STUDY_EXPORTS_DIR=exports python3 line_search.py
	cd study && STUDY_EXPORTS_DIR=exports python3 parabola_certificate.py
	cd study && STUDY_EXPORTS_DIR=exports python3 groebner_slice.py

# The vulnerable/patched advisory pairs (GHSA-3mvx-pp85-pm65): ScalarMul under
# gnark v0.14.0 vs v0.16.2 including Groth16 prove-level checks, and the
# emulated ModMul gadget with the shifted-hint override.
advisory:
	cd study/exporter-patched && go run . prove
	cd study/exporter-patched && go run . advice
	cd study/exporter-patched && go run . modmul
	cd study/exporter-advisory && go run . export && go run . prove

# Kernel-checked certificates (requires elan/Lake; first build fetches and
# compiles mathlib v4.15.0, which takes a while).
lean:
	cd lean && lake build

all: check tables study
