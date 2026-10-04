#!/usr/bin/env bash
# Full reproduction: dependency-free checks, every measured table, and the
# deployed-gadget certificate study. Requires Python 3 and Go. See README.md
# for the per-table map and the optional advisory/Lean targets.
set -euo pipefail
cd "$(dirname "$0")"
make check
make tables
make study
