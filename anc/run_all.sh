#!/bin/sh
# Verification runner for the shared ancillary of the companion papers "The Hodge conjecture for
# Fermat fourfolds of odd degree at most 199" and "Residual gap classes in the even-degree
# Fermat-fourfold census through degree 250". FRESH-RUN SEMANTICS: all derived logs are deleted first, so every check below is
# EXECUTED NOW — "PASSED" never means cached or skipped. ~35 s on the reference machine
# (see README). Any nonzero exit = a failed
# check (every proof-critical equality is an assert in the scripts themselves).
set -e
cd "$(dirname "$0")"
echo "== 0/13 input checksums =="
shasum -c SHA256SUMS
echo "== cleaning derived state (fresh-run semantics) =="
rm -f data/l4/*.log
echo "== 1/13 closure identities (Theorems A, A', A''; exchange instance; Prop D even-m caveat) =="
python3 verify_closure_identities.py
echo "== 2/13 census anchors m=33,39,45 (v2 engine) =="
python3 code/l4/census_scan_v2.py 33 39 45
echo "== 3/13 iterated/ledger pipeline m=33,45,66 (v3 engine) =="
python3 code/l4/census_scan_v3.py 33 45 66
echo "== 4/13 degree-210 lattice certificate (u in S_210) =="
python3 code/l4/s_lattice.py 210 1,79,109,121,151,169
echo "== 5/13 m=70 champion gap verdict (u not in S_70) =="
python3 code/l4/s_lattice.py 70 1,20,24,42,61,62
echo "== 6/13 Theorem C exact Frobenius certificate (m=33, p=67; all equalities asserted) =="
python3 code/l4/exact_jacobi_certificate.py
echo "== 7/13 closure-oracle calibration =="
python3 code/l4/fast_close.py --calibrate
echo "== 8/13 even-census calibration vs brute force =="
python3 code/l4/census_even.py --calibrate
echo "== 9/13 independent lattice verdicts (modular kernel witnesses; certificates re-summed) =="
python3 verify_lattice_witness.py
echo "== 10/13 per-orbit witness receipt re-verification (all 89 levels, stored JSON) =="
python3 code/l4/census_witnesses.py --verify
echo "== 11/13 independent census reimplementation vs the witness receipt (anchor levels) =="
python3 code/l4/census_independent.py 33 39 45 105
echo "== 12/13 independent even census (fresh, multiplicity-aware) at m=50,70 =="
python3 code/l4/census_independent.py 50 70
echo "== 13/13 level summaries: pinned table vs witness receipt; fresh independent regeneration of all odd m<=45 =="
python3 code/l4/census_summary.py --check --independent 21 25 27 29 31 33 35 37 39 41 43 45

echo "ALL CHECKS EXECUTED NOW AND PASSED."
