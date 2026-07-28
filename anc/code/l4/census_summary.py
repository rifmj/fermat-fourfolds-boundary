#!/usr/bin/env python3
"""Per-level census summary table + cross-checks (the completeness-certificate layer).

Emits and checks data/l4/census_level_summaries.json: for every one of the 89 odd census levels,
  m, n_reps, tallies (orbit count by kind), survivors, and sha256_reps — the SHA-256 hash of the
  canonically sorted representative list, serialized one class per line ("a0,a1,...,a5\\n").
Any full regeneration of the census, by any implementation, must reproduce the representative
COUNT and the HASH — this makes "no orbit was missed" checkable level by level, beyond the
positive per-orbit witnesses (which certify the classifications of the orbits that are there).

Usage:
  python3 census_summary.py --emit                  rebuild the JSON from the witness receipt
  python3 census_summary.py --check                 recompute from the witness receipt and require
                                                    exact equality with the pinned JSON
  python3 census_summary.py --independent m [m...]  regenerate the named levels FROM SCRATCH with
                                                    the independent implementation
                                                    (census_independent.py: its own generator,
                                                    canonizer, classifiers; no code shared with
                                                    the engine) and require count, tallies,
                                                    survivors, and canonical hash to match
Both check modes are assert-fatal on any mismatch. run_all.sh step 13 runs
"--check --independent <all odd 21..45>"; run_full_census.sh runs the full 89-level list.
"""
import sys, os, json, hashlib

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = HERE.rsplit('/code', 1)[0] + '/data/l4'
WITNESS = DATA + '/census_witnesses_odd.json'
OUT = DATA + '/census_level_summaries.json'


def canonical_hash(reps):
    reps = sorted(tuple(int(x) for x in r) for r in reps)
    blob = "".join(",".join(str(x) for x in r) + "\n" for r in reps)
    return hashlib.sha256(blob.encode()).hexdigest()


def summarize_level(m, reps, tallies, survivors):
    return {"m": int(m), "n_reps": len(reps),
            "tallies": {k: int(v) for k, v in sorted(tallies.items())},
            "survivors": sorted([list(map(int, s)) for s in survivors]),
            "sha256_reps": canonical_hash(reps)}


def from_witnesses():
    data = json.load(open(WITNESS))
    out = []
    for lev in data["levels"]:
        reps = [tuple(r["class"]) for r in lev["orbits"]]
        assert len(reps) == lev["n_reps"]
        surv = [r["class"] for r in lev["orbits"] if r["kind"] == "survivor"]
        tal = {}
        for r in lev["orbits"]:
            tal[r["kind"]] = tal.get(r["kind"], 0) + 1
        assert tal == lev["tallies"], f"witness-file internal tallies broken at m={lev['m']}"
        out.append(summarize_level(lev["m"], reps, tal, surv))
    return {"format": "sha256_reps = SHA-256 of the canonically sorted representative list, "
                      "one class per line 'a0,a1,...,a5\\n'",
            "levels": out}


def main():
    args = sys.argv[1:]
    if "--emit" in args:
        table = from_witnesses()
        json.dump(table, open(OUT, "w"), indent=1, sort_keys=True)
        print(f"census_summary: WROTE {OUT} ({len(table['levels'])} levels)")
        return
    pinned = json.load(open(OUT))
    by_m = {l["m"]: l for l in pinned["levels"]}
    if "--check" in args:
        fresh = from_witnesses()
        assert fresh["levels"] == pinned["levels"], \
            "pinned summary table disagrees with the witness receipt"
        print(f"census_summary: pinned summaries == recomputation from the witness receipt "
              f"({len(by_m)} levels, every count/tally/survivor-list/hash matches)")
    if "--independent" in args:
        ms = [int(x) for x in args if x.isdigit()]
        assert ms, "--independent needs level arguments"
        sys.path.insert(0, HERE)
        import census_independent as ci
        for m in ms:
            res = ci.classify(m)
            rec = summarize_level(m, [tuple(r) for r in res["reps"]],
                                  res["tallies"], res["survivors"])
            ref = by_m[m]
            assert rec == ref, (f"m={m}: independent from-scratch regeneration disagrees with "
                                f"the pinned summary\n got: {rec}\n ref: {ref}")
            print(f"m={m}: independent from-scratch regeneration matches the pinned summary "
                  f"(n_reps={rec['n_reps']}, sha256_reps={rec['sha256_reps'][:16]}...)")
        print(f"census_summary: {len(ms)} level(s) regenerated independently — count, tallies, "
              f"survivors, and canonical hash all match: NO MISSED ORBIT at these levels.")


if __name__ == "__main__":
    main()
