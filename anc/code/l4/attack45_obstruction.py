"""Move №3, leg (ii) — EXACT field-of-definition obstruction dossier for the m=45 open class,
reusing the parallel session's parameterized exact engine (obstruction105.analyse) via import,
with its log() redirected to OUR log file (no writes to the 105 log — collision hygiene).

Target: a = (1,19,20,28,30,37) at split primes p ≡ 1 (mod 45): 181 (numerically trivial — kernel?),
271 (numerically μ₉), 631 (numerically μ₃). Sought: the §76-analog — a prime where ALL conjugate
scalars ≠ 1 exactly ⟹ no ℚ(ζ₄₅)-cycle projects onto the class; plus the exact order profile
(certifying the ζ₉ eigenvalue field from §73/§77 measurements).
"""
import sys, os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import obstruction105 as eng

# redirect the engine's log to our own file (do NOT touch the 105 session's log)
MYLOG = os.path.join(HERE, "..", "..", "data", "l4", "attack45_obstruction.log")
MYLOG = os.path.abspath(os.path.join(HERE, "../../data/l4/attack45_obstruction.log"))


def mylog(msg, also_print=True):
    if also_print:
        print(msg)
    with open(MYLOG, "a") as f:
        f.write(msg + "\n")


eng.log = mylog
# some engines capture log by name inside report/analyse at call time — patch module dict
eng.__dict__['log'] = mylog

A45 = (1, 19, 20, 28, 30, 37)

if __name__ == "__main__":
    # calibration first (B4): the engine must reproduce the banked §76 m=33 certificate
    res33 = eng.analyse(33, 67, (7, 10, 13, 19, 22, 28), "calib33")
    eng.report(res33)
    ok = res33["all_ne1"] and res33["orders"][1] == 6
    print(f"### CALIBRATION m=33/p=67 (expect all≠1, order 6): {'PASS' if ok else 'FAIL'}")
    assert ok
    for p in (181, 271, 631):
        res = eng.analyse(45, p, A45, f"a45@p{p}")
        eng.report(res)
