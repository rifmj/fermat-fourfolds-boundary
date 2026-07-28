#!/usr/bin/env python3
"""Direct brute-force census cross-check — a THIRD method (no meet-in-the-middle, no profile
buckets, no code shared with the engine or with census_independent.py).

For each requested census level m: enumerate ALL sorted zero-sum 6-multisets of nonzero
residues mod m DIRECTLY — the five smallest entries run over all sorted 5-multisets
(itertools.combinations_with_replacement, processed in numpy chunks) and the largest entry is
forced by the zero-sum condition (kept iff it is nonzero and >= the fifth entry, so every
zero-sum sorted sextuple arises exactly once; no meet-in-the-middle, no profile buckets) —
then test the Hodge grade-3 condition directly (the sum of least positive residues of t*a
equals 3m for EVERY unit t — no half-unit shortcut), canonize each survivor by the minimum
sorted Galois conjugate, and compare the resulting representative list — count and canonical
SHA-256 (printed IN FULL, so this log is itself an archival certificate) — against the
pinned per-level summaries (census_level_summaries.json).
Classification is deliberately NOT reimplemented here: this tier certifies the GENERATOR
(no missed and no spurious orbit); the classifications are certified by the witness tier and
the independent implementation.

Usage: python3 census_bruteforce.py m [m ...]     (assert-fatal on any mismatch)
Cost is O(binom(m+3,5)) per level: runner step 14 executes every census level m <= 45 live;
the pinned receipt data/l4/bruteforce_odd_receipt.txt records the shipped full run over ALL
census levels m <= 143 (the range quoted in the paper).
"""
import sys, os, json, hashlib, itertools
from math import gcd

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = HERE.rsplit('/code', 1)[0] + '/data/l4'
SUMM = DATA + '/census_level_summaries.json'

CHUNK = 200_000


def brute_level(m):
    units = np.array([t for t in range(1, m) if gcd(t, m) == 1], dtype=np.int32)
    ulist = units.tolist()
    reps = set()
    it = itertools.combinations_with_replacement(range(1, m), 5)
    while True:
        block = list(itertools.islice(it, CHUNK))
        if not block:
            break
        F = np.array(block, dtype=np.int32)
        a6 = (-F.sum(axis=1)) % m
        keep = (a6 != 0) & (a6 >= F[:, 4])
        if not keep.any():
            continue
        A = np.concatenate([F[keep], a6[keep, None]], axis=1)
        # direct grade test over ALL units: residues are never 0 (entries nonzero, t a unit)
        P = (A[:, None, :] * units[None, :, None]) % m
        hodge = (P.sum(axis=2) == 3 * m).all(axis=1)
        for row in A[hodge]:
            a = tuple(int(x) for x in row)
            reps.add(min(tuple(sorted((t * x) % m for x in a)) for t in ulist))
    return sorted(reps)


def canonical_hash(reps):
    blob = "".join(",".join(str(x) for x in r) + "\n" for r in reps)
    return hashlib.sha256(blob.encode()).hexdigest()


def main():
    ms = [int(x) for x in sys.argv[1:]]
    assert ms, "usage: census_bruteforce.py m [m ...]"
    by_m = {l["m"]: l for l in json.load(open(SUMM))["levels"]}
    for m in ms:
        reps = brute_level(m)
        h = canonical_hash(reps)
        ref = by_m[m]
        assert len(reps) == ref["n_reps"], \
            f"m={m}: brute-force found {len(reps)} orbits, pinned {ref['n_reps']}"
        assert h == ref["sha256_reps"], f"m={m}: canonical hash mismatch"
        print(f"m={m}: brute force reproduces the census — {len(reps)} orbits, "
              f"sha256 {h} MATCH", flush=True)
    print(f"census_bruteforce: {len(ms)} level(s) reproduced by direct enumeration "
          f"(third method): counts and canonical hashes all match.")


if __name__ == "__main__":
    main()
