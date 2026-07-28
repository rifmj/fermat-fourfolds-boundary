#!/bin/sh
# ARCHIVAL TIER — complete from-scratch regeneration of the 89-level odd census by the
# algorithmically independent implementation (census_independent.py), checked level by level
# against the pinned per-level summaries (representative count, tallies, survivor list, and the
# canonical SHA-256 of the sorted representative list). This is the long-run counterpart of
# run_all.sh, whose step 13 cross-checks a fresh sub-range (all odd 21..45) only.
# Reference machine (Apple M4 Max, Python 3.13.13): ~12 minutes total (measured 701 s); the largest
# levels dominate (the engine alone takes ~158 s at m=199). The ENGINE-side receipts regenerate
# separately with the commands in README.md ("Census receipt"); their pinned two-engine sweep
# took ~36 minutes on the same machine.
set -e
cd "$(dirname "$0")"
python3 code/l4/census_summary.py --check --independent $(python3 -c "print(' '.join(str(m) for m in range(21,200,2) if m!=23))")
echo "FULL INDEPENDENT CENSUS REGENERATED AND MATCHED (89 levels, canonical hashes verified)."
