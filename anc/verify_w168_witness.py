#!/usr/bin/env python3
"""Standalone checker for the m=168 closure (Proposition w168) — every displayed claim, exactly.

The proposition closes a = (1,25,79,121,127,151) on X^4_168 by the coset transfer from the
*-split witness beta = (6,54,60,108,126,150). This script re-derives, from the definitions and
from the shipped lattice generators, each of the five facts the proof uses:

  (a) a and beta are Hodge (2,2) characters of X^4_168: nonzero entries, coordinate sum 3m, and
      constant grade 3 over ALL units t mod 168 (no half-unit shortcut);
  (b) beta is *-split: 6+54+108 = 168 and 60+126+150 = 336, both = 0 mod 168;
  (c) nu(a) - nu(beta) in S_168  (the coset-transfer hypothesis);
  (d) nu(a) not in S_168 and nu(beta) not in S_168  (non-vacuity: neither is separately in the
      lattice, so the congruence is not trivially satisfied);
  (e) 2*nu(a) in S_168  (Aoki's doubling, for consistency with the gap-group remark);
and, as a NEGATIVE control, that a itself admits no zero-sum-triple split (so the *-split
theorem does not fire on a directly and the transfer is actually needed).

Every check is an assert; the script exits nonzero on any failure. Runner step 17.
"""
import sys, os, itertools
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE + '/code/l4')
from s_lattice_core import gens_S, hnf_membership_builder, vec

M = 168
A = (1, 25, 79, 121, 127, 151)
B = (6, 54, 60, 108, 126, 150)


def units(m):
    return [t for t in range(1, m) if gcd(t, m) == 1]


def res(x, m):
    r = x % m
    return r if r else m


def grade_constant(c, m, U):
    vals = {sum(res(t * x, m) for x in c) for t in U}
    return vals.pop() // m if len(vals) == 1 else None


def main():
    U = units(M)
    # (a)
    for name, c in (("a", A), ("beta", B)):
        assert all(x % M for x in c), f"{name}: a zero entry"
        assert sum(c) % M == 0 and sum(c) == 3 * M, f"{name}: coordinate sum {sum(c)} != 3m"
        g = grade_constant(c, M, U)
        assert g == 3, f"{name}: grade not constant 3 over all {len(U)} units (got {g})"
    print(f"(a) a and beta are Hodge (2,2) characters of X^4_{M}: nonzero entries, sum 504=3m, "
          f"grade 3 constant over all {len(U)} units — OK")
    # (b)
    splits = [(t1, t2) for c in itertools.combinations(range(6), 3) if 0 in c
              for t1, t2 in [(tuple(B[i] for i in c), tuple(B[i] for i in range(6) if i not in c))]
              if sum(t1) % M == 0 and sum(t2) % M == 0]
    assert splits, "beta is not *-split"
    (t1, t2) = splits[0]
    assert sum(t1) == 168 and sum(t2) == 336, (t1, t2)
    print(f"(b) beta is *-split: {t1} sums to {sum(t1)} = m and {t2} sums to {sum(t2)} = 2m — OK")
    # (c)(d)(e)
    member, rank = hnf_membership_builder(gens_S(M))
    va, vb = vec(M, list(A)), vec(M, list(B))
    diff = [x - y for x, y in zip(va, vb)]
    assert member(diff), "nu(a) - nu(beta) NOT in S_168"
    assert not member(va), "nu(a) unexpectedly in S_168 (a is claimed to be a gap class)"
    assert not member(vb), "nu(beta) unexpectedly in S_168 (non-vacuity guard failed)"
    assert member([2 * x for x in va]), "2*nu(a) NOT in S_168"
    print(f"(c) nu(a) - nu(beta) in S_168 — OK   [S_168 rank {rank}]")
    print("(d) nu(a) not in S_168 and nu(beta) not in S_168 — the congruence is NOT vacuous — OK")
    print("(e) 2*nu(a) in S_168 — OK")
    # (f) TRANSPORTABLE certificate: read the stored integer combination from disk and RE-SUM it
    import json
    cert = json.load(open(HERE + '/data/l4/w168_coset_certificate.json'))
    gens = gens_S(M)
    assert cert["a"] == list(A) and cert["beta"] == list(B), "certificate is for other classes"
    acc = [0] * (M - 1)
    for j, c in cert["coefficients"].items():
        g = gens[int(j)]
        for i in range(M - 1):
            acc[i] += c * g[i]
    assert acc == diff, "stored certificate does NOT re-sum to nu(a) - nu(beta)"
    cvals = [int(c) for c in cert["coefficients"].values()]
    print(f"(f) stored certificate re-summed from disk: {len(cvals)} nonzero coefficients in "
          f"[{min(cvals)},{max(cvals)}] over the {len(gens)} generators — reproduces "
          f"nu(a) - nu(beta) EXACTLY")
    # (g) the modular kernel witness certifies BOTH non-memberships at once
    kw = cert["kernel_witness"]; q = kw["q"]
    phi = [0] * (M - 1)
    for i in kw["phi_support"]:
        phi[i] = 1
    assert all(sum(p * g[i] for i, p in enumerate(phi)) % q == 0 for g in gens), \
        "kernel witness does not annihilate every generator"
    pa = sum(p * x for p, x in zip(phi, va)) % q
    pb = sum(p * x for p, x in zip(phi, vb)) % q
    assert pa % q and pb % q, "kernel witness fails to separate a or beta from S_168"
    print(f"(g) modular kernel witness (q={q}, support {len(kw['phi_support'])}): annihilates every "
          f"generator, phi.nu(a)={pa} and phi.nu(beta)={pb} both nonzero — a transportable proof "
          f"that NEITHER lies in S_168")
    # negative control
    asplit = [c for c in itertools.combinations(range(6), 3) if 0 in c
              and sum(A[i] for i in c) % M == 0
              and sum(A[i] for i in range(6) if i not in c) % M == 0]
    assert not asplit, f"a itself is *-split ({asplit}) — the transfer would be unnecessary"
    print("(control) a itself admits NO zero-sum-triple split, so the *-split theorem does not "
          "fire on a directly and the coset transfer is needed — OK")
    print("verify_w168_witness: every displayed fact of Proposition w168 re-derived exactly — PASS")


if __name__ == "__main__":
    main()
