#!/usr/bin/env python3
"""Assert the FRESH independent even-census run against the pinned key-level receipt.

Referee finding (external computational audit): the runner's even step printed two fresh
per-level results but asserted nothing — census_independent.py compares against the ODD witness
receipt (census_witnesses_odd.json), which contains no even level, so for m = 50, 70 its
comparison branch is simply not taken ("levels absent from the receipt are reported unverified").
This script closes that gap: it re-runs the independent implementation at the requested even
levels and asserts, line by line, agreement with the pinned receipt
data/l4/receipts_even/even_independent_key_levels.txt (representative count AND the full tally
dict). Exits nonzero on any mismatch, so the runner's `set -e` aborts.

Usage: python3 even_keylevels_check.py [m ...]     (default: 50 70)
"""
import ast
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
RECEIPT = HERE.rsplit('/code', 1)[0] + '/data/l4/receipts_even/even_independent_key_levels.txt'

sys.path.insert(0, HERE)
import census_independent as ci


def pinned():
    """{m: (n_reps, tallies)} parsed from the pinned receipt."""
    out = {}
    pat = re.compile(r"^m=(\d+):\s*reps=(\d+)\s*tallies=(\{.*\})\s*$")
    for line in open(RECEIPT):
        mo = pat.match(line.strip())
        if mo:
            out[int(mo.group(1))] = (int(mo.group(2)), ast.literal_eval(mo.group(3)))
    assert out, f"no parsable receipt lines in {RECEIPT}"
    return out


def main():
    ms = [int(x) for x in sys.argv[1:]] or [50, 70]
    ref = pinned()
    for m in ms:
        assert m in ref, f"m={m} is not in the pinned even key-level receipt"
        res = ci.classify(m)
        n_ref, t_ref = ref[m]
        assert res["n_reps"] == n_ref, \
            f"m={m}: fresh run has {res['n_reps']} representatives, receipt says {n_ref}"
        assert res["tallies"] == t_ref, \
            f"m={m}: fresh tallies {res['tallies']} != receipt {t_ref}"
        print(f"m={m}: fresh independent even census matches the pinned receipt "
              f"(reps={n_ref}, tallies={t_ref})", flush=True)
    print(f"even_keylevels_check: {len(ms)} even level(s) re-derived fresh and ASSERTED against "
          f"the pinned receipt.")


if __name__ == "__main__":
    main()
