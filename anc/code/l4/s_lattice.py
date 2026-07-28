"""s_lattice — the S_m-lattice membership test + certificate extractor (§§92–93 instrument).

Decides EXACTLY whether a Hodge class is reachable by Aoki's standard calculus:
u(a) ∈ S_m = Z-span{u(σ_{p,·}), u(D_m)}  ⟹  (negation-closure conversion + Lemma 4.1(iii),
Aoki CMUSP 49 (2000), unconditional in m)  V(a) is ALGEBRAIC.
u(a) ∉ S_m  ⟹  a is a GAP class (2u ∈ S_m always, Yamamoto 2-torsion) — beyond the standard
calculus by lattice obstruction; partition/monoid engines (census v3) cannot close it directly.

Catches negative-coefficient certificates invisible to all §§75–90 partition engines
(precedents: P1@210 closed with a ±1×40-generator certificate §93; 168#1's coset ≡ 6ξ₂₈ §92).

Usage: python3 s_lattice.py <m> <a0,...,a5>     (runs calibration first, then the test;
                                                 prints certificate if member)
Core (gens_S, vec, hnf_membership_builder) = referee-audited implementation (s_lattice_core.py,
provenance: §92 Opus audit; independent Sol reimplementation agreed on all nine ≤250 classes).
"""
import sys, os, json, time
import importlib.util as ilu

HERE = os.path.dirname(os.path.abspath(__file__))
import io
_buf, _old = io.StringIO(), sys.stdout
sys.stdout = _buf   # core module runs a self-demo on import (m=21/28 calibration)
_s = ilu.spec_from_file_location('core', os.path.join(HERE, 's_lattice_core.py'))
core = ilu.module_from_spec(_s); _s.loader.exec_module(core)
sys.stdout = _old
CORE_DEMO = _buf.getvalue()


def certificate(m, a, vec_override=None):
    """Return (in_S, coeffs or None). Independent echelon reduction with coefficient tracking.
    vec_override: decide membership of an explicit exponent vector (e.g. 2u) instead of vec(a)."""
    G = core.gens_S(m)
    u = vec_override if vec_override is not None else core.vec(m, list(a))
    n = m - 1
    rows = [G[i][:] + [1 if j == i else 0 for j in range(len(G))] for i in range(len(G))]
    r0 = 0
    for c in range(n):
        while True:
            idxs = [i for i in range(r0, len(rows)) if rows[i][c] != 0]
            if not idxs:
                break
            i0 = min(idxs, key=lambda i: abs(rows[i][c]))
            rows[r0], rows[i0] = rows[i0], rows[r0]
            done = True
            for i in range(r0 + 1, len(rows)):
                if rows[i][c]:
                    q = rows[i][c] // rows[r0][c]
                    rows[i] = [x - q * y for x, y in zip(rows[i], rows[r0])]
                    if rows[i][c]:
                        done = False
            if done:
                r0 += 1
                break
    coef = [0] * len(G)
    v = u[:]
    for r in rows[:r0]:
        pc = next(c for c in range(n) if r[c] != 0)
        if v[pc] == 0:
            continue
        if v[pc] % r[pc] != 0:
            return False, None
        q = v[pc] // r[pc]
        v = [x - q * y for x, y in zip(v, r[:n])]
        coef = [cc + q * rc for cc, rc in zip(coef, r[n:])]
    if any(v):
        return False, None
    # re-verify from scratch
    chk = [0] * n
    for i, c in enumerate(coef):
        if c:
            chk = [x + c * y for x, y in zip(chk, G[i])]
    assert chk == u, "certificate re-verification failed"
    return True, {i: c for i, c in enumerate(coef) if c}


def calibrate():
    ok = True
    in_s, cert = certificate(210, (1, 79, 109, 121, 151, 169))
    print(f"CALIB P1@210 (must be IN, ±1 cert): {'IN, %d gens, coeffs %s' % (len(cert), sorted(set(cert.values()))) if in_s else 'OUT'}")
    ok &= in_s and set(cert.values()) <= {1, -1}
    in_s, _ = certificate(168, (1, 25, 79, 121, 127, 151))
    print(f"CALIB 168#1 (must be OUT/gap): {'IN' if in_s else 'OUT'}"); ok &= not in_s
    in_s, _ = certificate(70, (1, 20, 24, 42, 61, 62))
    print(f"CALIB W70 (must be OUT/gap): {'IN' if in_s else 'OUT'}"); ok &= not in_s
    print(f"CALIBRATION {'PASS' if ok else 'FAIL'}")
    return ok


if __name__ == "__main__":
    if not calibrate():
        sys.exit(1)
    if len(sys.argv) > 2:
        m = int(sys.argv[1]); a = tuple(int(x) for x in sys.argv[2].split(','))
        t0 = time.time()
        in_s, cert = certificate(m, a)
        if in_s:
            print(f"*** u(a) IN S_{m} — STANDARD-CALCULUS ALGEBRAIC (Lemma 4.1(iii)) ***")
            print(f"    certificate: {len(cert)} generators, coeff range "
                  f"[{min(cert.values())},{max(cert.values())}]  [{time.time()-t0:.0f}s]")
        else:
            print(f"u(a) NOT in S_{m} — GAP class (beyond the standard calculus)  [{time.time()-t0:.0f}s]")
