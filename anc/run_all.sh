#!/bin/sh
# Verification runner for the shared ancillary of the companion papers "The Hodge conjecture for
# Fermat fourfolds of odd degree at most 199" and "Residual gap classes in the even-degree
# Fermat-fourfold census through degree 250". FRESH-RUN SEMANTICS: all derived logs are deleted first, so every check below is
# EXECUTED NOW — "PASSED" never means cached or skipped. ~43 s on the reference machine
# (see README). Any nonzero exit = a failed
# check (every proof-critical equality is an assert in the scripts themselves).
set -e
cd "$(dirname "$0")"
echo "== 0/19 input checksums =="
shasum -c SHA256SUMS
echo "== cleaning derived state (fresh-run semantics) =="
rm -f data/l4/*.log
echo "== 1/19 closure identities (Theorems A, A', A''; exchange instance; Prop D even-m caveat) =="
python3 verify_closure_identities.py
echo "== 2/19 census anchors m=33,39,45 (v2 engine) =="
python3 code/l4/census_scan_v2.py 33 39 45
echo "== 3/19 iterated/ledger pipeline m=33,45,66 (v3 engine) =="
python3 code/l4/census_scan_v3.py 33 45 66
echo "== 4/19 degree-210 lattice certificate (u in S_210) =="
python3 code/l4/s_lattice.py 210 1,79,109,121,151,169
echo "== 5/19 m=70 champion gap verdict (u not in S_70) =="
python3 code/l4/s_lattice.py 70 1,20,24,42,61,62
echo "== 6/19 Theorem C exact Frobenius certificate (m=33, p=67; all equalities asserted) =="
python3 code/l4/exact_jacobi_certificate.py
echo "== 7/19 closure-oracle calibration =="
python3 code/l4/fast_close.py --calibrate
echo "== 8/19 even-census calibration vs brute force =="
python3 code/l4/census_even.py --calibrate
echo "== 9/19 independent lattice verdicts (modular kernel witnesses; certificates re-summed) =="
python3 verify_lattice_witness.py
echo "== 10/19 per-orbit witness receipt re-verification (all 89 levels, stored JSON) =="
python3 code/l4/census_witnesses.py --verify
echo "== 11/19 independent census reimplementation vs the witness receipt (anchor levels) =="
python3 code/l4/census_independent.py 33 39 45 105
echo "== 12/19 independent even census (fresh, multiplicity-aware) at m=50,70, ASSERTED against the pinned receipt =="
python3 code/l4/even_keylevels_check.py 50 70
echo "== 13/19 level summaries: pinned table vs witness receipt; fresh independent regeneration of all odd m<=45 =="
python3 code/l4/census_summary.py --check --independent 21 25 27 29 31 33 35 37 39 41 43 45
echo "== 14/19 brute-force third method (direct exhaustive enumeration) at every census level m<=45 =="
python3 code/l4/census_bruteforce.py 21 25 27 29 31 33 35 37 39 41 43 45
echo "== 15/19 even tier table: per-level base / post-depth-two counts and canonical hashes =="
python3 code/l4/even_tier_table.py --check
echo "== 16/19 even final table: every lattice verdict recomputed; 40 rows, 8 open gap classes =="
python3 code/l4/even_final_table.py --check
echo "== 17/19 m=168 closure witness: grades, the two split sums, the coset membership, non-vacuity =="
python3 verify_w168_witness.py

echo "== 18/19 Theorem C, SECOND independent implementation (different reduction basis) =="
python3 code/l4/obstruction105.py calib

echo "== 19/19 deep-closure routes: every ledger witness re-verified from the definitions =="
python3 verify_deep_routes.py > data/l4/deep_routes_check.out
tail -1 data/l4/deep_routes_check.out

echo "ALL CHECKS EXECUTED NOW AND PASSED."
