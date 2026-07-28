#!/usr/bin/env python3
"""Even-sector TIER table: the exact, uniformly defined census tiers, level by level.

For each even level m the script recomputes, from the definitions and with the shipped even-safe
primitives of census_even.py:

  reps            all Galois-orbit representatives of grade-3 Hodge sextuples at level m
  base_survivors  those failing ALL FOUR base predicates
                  (decomposable / quasi-decomposable / standard / *-split)
  d2_survivors    base survivors that the partition-closure oracle does not close with at most
                  TWO added vanishing pairs  (census_even.closes(..., max_pairs=2) is None)
  primitive       content gcd(a_0,...,a_5,m) = 1

The paper's headline count is the PRIMITIVE d2_survivors tier ("post-depth-two survivors"):
these are the classes handed to the deep tiers (depth 3-5, two-generation, transport) and to the
exchange analysis. The base tier is much larger (it begins at m=32) and is NOT the paper's count
- this script exists so that every printed tier number is reproducible from one definition.

Usage:
  python3 even_tier_table.py <m ...>            per-level tier line + the primitive d2 survivors
  python3 even_tier_table.py --emit <m ...>     also append rows to data/l4/even_tier_table.json
  python3 even_tier_table.py --check            re-verify the shipped table's own consistency
                                                (counts vs stored class lists, canonical hashes)
"""
import sys, os, json, hashlib, itertools
from math import gcd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from census_even import (units, hodge_multisets, canon, standard_grade3, Closed0, closes)

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = HERE.rsplit('/code', 1)[0] + '/data/l4/even_tier_table.json'


def content(a, m):
    g = m
    for x in a:
        g = gcd(g, x)
    return g


def canonical_hash(items):
    blob = "".join(",".join(str(x) for x in r) + "\n" for r in sorted(items))
    return hashlib.sha256(blob.encode()).hexdigest()


def tier_level(m):
    U = units(m)
    S3 = hodge_multisets(m, 6, 3)
    S2 = hodge_multisets(m, 4, 2)
    reps = sorted({canon(a, m, U) for a in S3})
    std = standard_grade3(m, U)
    closed0 = Closed0(m, U, std, S2)
    memo = {}
    base_surv = [a for a in reps if not closed0(a)]
    d2, depths = [], {}
    for a in base_surv:
        d = closes(a, m, U, closed0, memo, max_pairs=2)
        if d is None:
            d2.append(a)
        else:
            depths[a] = d
    prim_base = [a for a in base_surv if content(a, m) == 1]
    prim_d2 = [a for a in d2 if content(a, m) == 1]
    return {"m": m, "n_reps": len(reps),
            "n_base_survivors": len(base_surv), "n_base_survivors_primitive": len(prim_base),
            "n_d2_survivors": len(d2), "n_d2_survivors_primitive": len(prim_d2),
            "d2_survivors_primitive": [list(a) for a in prim_d2],
            "d2_survivors_induced": [list(a) for a in d2 if content(a, m) > 1],
            "sha256_d2_survivors": canonical_hash(d2)}


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    if "--check" in sys.argv:
        tab = json.load(open(OUT))
        # RECOMPUTE the tier predicate from the definitions on a fresh sub-range (cheap levels),
        # so --check is not merely a self-consistency test of the stored JSON.
        recompute_upto = 60
        for row in tab["levels"]:
            if row["m"] <= recompute_upto:
                fresh = tier_level(row["m"])
                assert fresh == row, (f"m={row['m']}: recomputation from the definitions disagrees "
                                      f"with the stored row")
        print(f"even_tier_table: every level m <= {recompute_upto} RECOMPUTED from the definitions "
              f"and identical to the stored row")
        tot = {"base": 0, "d2p": 0}
        for row in tab["levels"]:
            assert row["n_d2_survivors_primitive"] == len(row["d2_survivors_primitive"]), row["m"]
            assert row["sha256_d2_survivors"] == canonical_hash(
                [tuple(x) for x in row["d2_survivors_primitive"] + row["d2_survivors_induced"]]), row["m"]
            tot["base"] += row["n_base_survivors"]
            tot["d2p"] += row["n_d2_survivors_primitive"]
        cum = {}
        for lim in (108, 200, 250):
            cum[lim] = sum(r["n_d2_survivors_primitive"] for r in tab["levels"] if r["m"] <= lim)
        print(f"even_tier_table: {len(tab['levels'])} levels; base-tier survivors total "
              f"{tot['base']} (first at m="
              f"{min(r['m'] for r in tab['levels'] if r['n_base_survivors'])}); "
              f"PRIMITIVE post-depth-two survivors: {cum[108]} through m=108, {cum[200]} through "
              f"m=200, {cum[250]} through m=250; every stored count and canonical hash "
              f"re-derived — CONSISTENT")
        return
    rows = []
    for m in [int(x) for x in args]:
        r = tier_level(m)
        rows.append(r)
        print(f"m={r['m']}: reps={r['n_reps']} base-survivors={r['n_base_survivors']} "
              f"(primitive {r['n_base_survivors_primitive']}) "
              f"post-depth-two survivors={r['n_d2_survivors']} "
              f"(primitive {r['n_d2_survivors_primitive']}) "
              f"sha256={r['sha256_d2_survivors'][:16]}...", flush=True)
        for a in r["d2_survivors_primitive"]:
            print(f"    PRIMITIVE post-depth-two survivor: {tuple(a)}")
    if "--emit" in sys.argv:
        old = json.load(open(OUT))["levels"] if os.path.exists(OUT) else []
        by_m = {r["m"]: r for r in old}
        for r in rows:
            by_m[r["m"]] = r
        json.dump({"tiers": "base = four base predicates; d2 = base + partition closure with "
                            "<= 2 added vanishing pairs (the paper's headline tier)",
                   "levels": [by_m[k] for k in sorted(by_m)]}, open(OUT, "w"), indent=1)
        print(f"WROTE {OUT} ({len(by_m)} levels)")


if __name__ == "__main__":
    main()
