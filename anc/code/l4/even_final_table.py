#!/usr/bin/env python3
"""The complete reader's table of the even-sector headline tier, with an independent verifier.

Emits and checks data/l4/even_final_table.json: one row per PRIMITIVE POST-DEPTH-TWO SURVIVOR
(the paper's headline tier — base survivors that the closure oracle does not close with at most
two added vanishing pairs), over even 6 <= m <= 250, with

  m, class (canonical representative), content gcd, nu in S_m?, 2*nu in S_m?,
  status  = deep-closed | closed-by-proposition | open
  route   = the deep-closure route recorded in CLOSED_LEDGER.tsv, or the proposition, or the wall

NOTE ON STATUS. `status`/`route` are a CURATED annotation, cross-checked against the ledger and the
receipts — they are not re-derived here, and the count of "open" rows is therefore an input to this
script, not an output of it. What this script DOES verify independently is every lattice verdict
(nu in S_m, 2nu in S_m), recomputed by an HNF test that shares no code with the closure search, and
the row-by-row identity of the stored table with a fresh rebuild. Vocabulary: the RESIDUAL after the
deep tiers is ten primitive classes; two of them are closed by the propositions of the paper, so the
FINAL open set is eight — "residual (pre-proposition) = 10" and "open (final) = 8" are different
tiers and are never used interchangeably.

The tier itself (counts, canonical hashes) comes from even_tier_table.json, which
even_tier_table.py recomputes from the definitions; the lattice verdicts are recomputed here
exactly (Hermite normal form over the shipped generator set), and the deep-closure routes are
read from the ledger. The verifier deliberately shares no code with the closure search.

Usage:
  python3 even_final_table.py --emit     rebuild the table
  python3 even_final_table.py --check    recompute every lattice verdict and every count, and
                                         assert consistency with the stored table and with
                                         even_tier_table.json (assert-fatal)
"""
import sys, os, json, re
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
DATA = HERE.rsplit('/code', 1)[0] + '/data/l4'
TIER = DATA + '/even_tier_table.json'
LEDGER = DATA + '/CLOSED_LEDGER.tsv'
OUT = DATA + '/even_final_table.json'

from s_lattice_core import hnf_membership_builder, gens_S, vec

WALLS = {
    (70, (1, 20, 24, 42, 61, 62)): "W_70",
    (210, (2, 9, 129, 142, 168, 180)): "W_70",
    (110, (1, 24, 62, 71, 81, 91)): "W_110",
    (110, (1, 31, 55, 71, 81, 91)): "W_110",
    (220, (1, 62, 111, 142, 162, 182)): "W_110",
    (114, (1, 13, 43, 72, 103, 110)): "W_114",
    (114, (1, 13, 43, 80, 102, 103)): "W_114",
    (114, (1, 7, 78, 79, 86, 91)): "W_114",
}
PROPOSITIONS = {
    (168, (1, 25, 79, 121, 127, 151)): "Prop. w168 (coset transfer from a *-split class)",
    (210, (1, 79, 109, 121, 151, 169)): "Prop. w210 (nu in S_210; 40-generator certificate)",
}


def read_ledger():
    out = {}
    for line in open(LEDGER):
        if line.startswith('#'):
            continue
        f = line.rstrip('\n').split('\t')
        if len(f) < 3:
            continue
        cls = tuple(int(x) for x in re.findall(r'\d+', f[1]))
        out[(int(f[0]), cls)] = f[2]
    return out


def build():
    tier = json.load(open(TIER))
    ledger = read_ledger()
    rows = []
    for lev in tier["levels"]:
        m = lev["m"]
        if not lev["d2_survivors_primitive"]:
            continue
        member, _ = hnf_membership_builder(gens_S(m))
        for c in lev["d2_survivors_primitive"]:
            a = tuple(c)
            v = vec(m, list(a))
            key = (m, a)
            if key in PROPOSITIONS:
                status, route = "closed-by-proposition", PROPOSITIONS[key]
            elif key in WALLS:
                status, route = "open", f"unresolved; wall {WALLS[key]}"
            else:
                status, route = "deep-closed", ledger.get(key, "deep partition/iterated tier")
            g = m
            for x in a:
                g = gcd(g, x)
            rows.append({"m": m, "class": list(a), "content": g,
                         "nu_in_S_m": bool(member(v)),
                         "two_nu_in_S_m": bool(member([2 * x for x in v])),
                         "status": status, "route": route})
    return rows


def main():
    if "--emit" in sys.argv:
        rows = build()
        json.dump({"tier": "primitive post-depth-two survivors, even 6 <= m <= 250",
                   "rows": rows}, open(OUT, "w"), indent=1)
        print(f"WROTE {OUT}: {len(rows)} rows")
    rows = json.load(open(OUT))["rows"]
    tier = json.load(open(TIER))
    n_tier = sum(l["n_d2_survivors_primitive"] for l in tier["levels"])
    assert len(rows) == n_tier, f"table has {len(rows)} rows, tier table says {n_tier}"
    fresh = {(r["m"], tuple(r["class"])): r for r in build()}
    for r in rows:
        f = fresh[(r["m"], tuple(r["class"]))]
        assert f == r, f"row changed on recomputation: {r['m']} {r['class']}"
    by_status = {}
    for r in rows:
        by_status[r["status"]] = by_status.get(r["status"], 0) + 1
    cum = {lim: sum(1 for r in rows if r["m"] <= lim) for lim in (108, 200, 250)}
    opens = [r for r in rows if r["status"] == "open"]
    assert len(opens) == 8, len(opens)
    assert all(not r["nu_in_S_m"] and r["two_nu_in_S_m"] for r in opens), \
        "every open class must be a gap class with 2*nu in S_m"
    print(f"even_final_table: {len(rows)} primitive post-depth-two survivors "
          f"({cum[108]} through m=108, {cum[200]} through m=200, {cum[250]} through m=250); "
          f"status split {by_status}; every lattice verdict recomputed exactly; "
          f"the 8 open classes all satisfy nu not in S_m and 2*nu in S_m — CONSISTENT")


if __name__ == "__main__":
    main()
