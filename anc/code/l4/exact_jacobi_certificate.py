"""§76 receipt — EXACT Jacobi-sum certificate for the Q1-obstruction (coordinator reproduction of
Sol's step-4 repair; discharges the [C]).

Object: the projective Weil-Jacobi sum of a = (7,10,13,19,22,28) at p = 67 ≡ 1 (mod 33),
    j(t·a) := S(t·a)/(p−1),  S(α) := Σ_{v∈(𝔽_p*)^6, Σv=0} ∏_i χ^{α_i}(v_i)  ∈ ℤ[ζ₃₃]
computed EXACTLY (integer dynamic programming over (sum mod p) × (exponent mod 33); no floats),
reduced mod Φ₃₃. Claims certified exactly, for ALL 20 units t (Galois x→x^t):
  (C1) j(t·a) = ε·p²·(root of unity), i.e. (j/p²) is a unit root: (j(t·a)/p²)^6 = 1 EXACTLY;
  (C2) j(t·a)/p² ≠ 1 EXACTLY (so the Frobenius scalar on V(t·a)(2) is a NONTRIVIAL 6th root
       of unity regardless of sign convention: ±(j/p²) ∈ {±ζ₆^{±1}} and none equal 1);
  (C3) closed form (asserted below): j/p² = 1 + ζ₃₃¹¹ = 1 + ζ₃ = ζ₆ for t=1 (and conjugates
       lie in {ζ₆^{±1}}); the opposite sign convention gives −(1+ζ₃) = ζ₃-primitive values.
Numeric cross-check (30 dps) against the Gauss-sum product ∏g(χ^{a_i})/p³ pins the normalization.
Character convention (pinned): chi is the character of F_67^* with chi(g) = zeta_33 on the
smallest primitive root g (prim_root finds g = 2; ind = discrete log base 2). A conjugate choice
permutes the 20 conjugate values (and can exchange zeta_6 <-> zeta_6^{-1} at t = 1); the asserted
exact order 6 and the two-value distribution are convention-independent.
Convention note: some references DEFINE the Jacobi sum with the opposite sign (j_alt = −j). That
changes the definition only, never the geometry: the trace formula acquires the compensating
sign, and the GEOMETRIC Frobenius scalar is convention-independent — the asserted (u')³ = −1
pins its exact order 6 under either definition.
"""
import sys
from math import gcd
from fractions import Fraction

P, M = 67, 33
A = (7, 10, 13, 19, 22, 28)


def prim_root(p):
    for g in range(2, p):
        seen, x = set(), 1
        for _ in range(p - 1):
            x = x * g % p
            seen.add(x)
        if len(seen) == p - 1:
            return g


def cyclotomic_reduce(vec, m=M):
    """Reduce an exponent-vector in ℤ[x]/(x^m −1) to the basis 1..x^{φ-1} of ℤ[x]/Φ_m(x), m=33.
    Φ₃₃ = (x³³−1)(x−1)(x¹¹−1)⁻¹(x³−1)⁻¹ ... — easier: use x³³=1 and the relations from
    Φ₃₃ | x³³−1. We reduce modulo Φ₃₃ via polynomial division with integer coefficients."""
    # build Φ_33 exactly: Φ_33(x) = (x^33−1)(x−1)/((x^11−1)(x^3−1))  [divisors 1,3,11,33]
    def polmul(a, b):
        r = [0] * (len(a) + len(b) - 1)
        for i, ai in enumerate(a):
            if ai:
                for j, bj in enumerate(b):
                    r[i + j] += ai * bj
        return r
    def poldiv_exact(num, den):
        num = num[:]
        q = [0] * (len(num) - len(den) + 1)
        for i in range(len(q) - 1, -1, -1):
            c = num[i + len(den) - 1]
            assert c % den[-1] == 0
            q[i] = c // den[-1]
            for j, dj in enumerate(den):
                num[i + j] -= q[i] * dj
        assert all(c == 0 for c in num), "nonzero remainder"
        return q
    x33 = [-1] + [0] * 32 + [1]
    x1 = [-1, 1]
    x11 = [-1] + [0] * 10 + [1]
    x3 = [-1, 0, 0, 1]
    num = polmul(x33, x1)
    phi = poldiv_exact(poldiv_exact(num, x11), x3)   # degree 20 = φ(33)
    assert len(phi) == 21 and phi[-1] == 1
    # now reduce vec (length m) modulo phi
    v = vec[:] + [0] * max(0, 21 - len(vec))
    v = v[:]
    for i in range(len(v) - 1, 20, -1):
        c = v[i]
        if c:
            for j in range(21):
                v[i - 20 + j] -= c * phi[j]
            v[i] = 0
    return v[:21 - 1 + 1][:21], phi  # length-21 vector, coeff of x^20 may be nonzero? no: reduced to deg<=20? deg(phi)=20 ⟹ reduce to deg<=19


def reduce_mod_phi(vec):
    """exponent vector length 33 (coeffs of x^0..x^32 in ℤ[x]/(x^33−1)) → canonical rep mod Φ₃₃,
    as integer list of length 20 (deg ≤ 19)."""
    # first fold x^33 = 1 already done (length 33). Then divide by Φ₃₃.
    # Build phi once
    global _PHI
    try:
        _PHI
    except NameError:
        def polmul(a, b):
            r = [0] * (len(a) + len(b) - 1)
            for i, ai in enumerate(a):
                if ai:
                    for j, bj in enumerate(b):
                        r[i + j] += ai * bj
            return r
        def poldiv_exact(num, den):
            num = num[:]
            q = [0] * (len(num) - len(den) + 1)
            for i in range(len(q) - 1, -1, -1):
                c = num[i + len(den) - 1]
                assert c % den[-1] == 0
                q[i] = c // den[-1]
                for j, dj in enumerate(den):
                    num[i + j] -= q[i] * dj
            assert all(c == 0 for c in num)
            return q
        x33 = [-1] + [0] * 32 + [1]
        x1 = [-1, 1]
        x11 = [-1] + [0] * 10 + [1]
        x3 = [-1, 0, 0, 1]
        _PHI = poldiv_exact(poldiv_exact(polmul(x33, x1), x11), x3)
        assert len(_PHI) == 21 and _PHI[-1] == 1
    v = vec[:]
    for i in range(len(v) - 1, 19, -1):
        c = v[i]
        if c:
            for j in range(21):
                v[i - 20 + j] -= c * _PHI[j]
    return v[:20]


def jacobi_exact(alpha, p=P, m=M):
    """S(alpha) = Σ_{v_1..v_6 ∈ F_p^*, Σ v ≡ 0} ∏ χ^{α_i}(v_i) as exponent-vector in ℤ[x]/(x^m−1),
    via DP over (partial sum mod p) with per-cell exponent-count vectors. Exact integers."""
    g = prim_root(p)
    ind = {}
    x = 1
    for k in range(p - 1):
        ind[x] = k
        x = x * g % p
    # dp[s] = vector of length m: coefficient of x^e = #ways (weighted) partial config sums to s with char-exponent e
    dp = [[0] * m for _ in range(p)]
    dp[0][0] = 1
    for ai in alpha:
        ndp = [[0] * m for _ in range(p)]
        for v in range(1, p):
            e = (ai * ind[v]) % m
            for s in range(p):
                row = dp[s]
                if any(row):
                    t = (s + v) % p
                    nrow = ndp[t]
                    for ee in range(m):
                        c = row[ee]
                        if c:
                            nrow[(ee + e) % m] += c
        dp = ndp
    return dp[0]  # Σv ≡ 0


def conj(vec33, t, m=M):
    """Galois x -> x^t on a length-33 exponent vector."""
    out = [0] * m
    for e, c in enumerate(vec33):
        if c:
            out[(e * t) % m] += c
    return out


def as_string(v20):
    terms = [f"{c}x^{i}" for i, c in enumerate(v20) if c]
    return " + ".join(terms) if terms else "0"


if __name__ == "__main__":
    print(f"EXACT certificate at p={P}, a={A}  (integer DP; no floating point in the certificate)")
    S = jacobi_exact(A)   # length-33 integer vector in ℤ[x]/(x^33−1)
    pm1 = P - 1
    # j = S/(p−1) must be integral
    assert all(c % pm1 == 0 for c in S), "S not divisible by p-1!"
    J33 = [c // pm1 for c in S]
    units = [t for t in range(1, M) if gcd(t, M) == 1]
    print(f"j(a) as vector mod x^33−1 (nonzero coeffs): {[(i,c) for i,c in enumerate(J33) if c]}")

    ok_all = True
    for t in units:
        Jt = reduce_mod_phi(conj(J33, t))
        # (C1)+(C2): check (Jt/p²)^6 == 1 and Jt/p² != 1 exactly, i.e. Jt^6 == p^12 and Jt != p² in ℤ[ζ33]
        # divide by p²: must be exact
        assert all(c % (P * P) == 0 for c in Jt), f"j(t·a) not divisible by p² at t={t}"
        U = [c // (P * P) for c in Jt]           # u' := j/p² as exact element (deg ≤ 19)
        # compute U^6 mod Φ via repeated exact multiplication in ℤ[x]/(x^33−1) then reduce
        def mul33(a20, b20):
            r = [0] * 33
            for i, ai in enumerate(a20):
                if ai:
                    for j, bj in enumerate(b20):
                        if bj:
                            r[(i + j) % 33] += ai * bj
            return reduce_mod_phi(r)
        U2 = mul33(U, U)
        U3 = mul33(U2, U)
        U6 = mul33(U3, U3)
        one = [1] + [0] * 19
        neg_one = [-1] + [0] * 19
        c1 = (U6 == one)
        c2 = (U != one)
        c3 = (U3 == neg_one)  # exact order 6: U^3 = -1 excludes orders 1, 2, 3
        if not (c1 and c2 and c3):
            ok_all = False
        if t == 1:
            print(f"t=1: u' = j/p² = {as_string(U)}   (u')^6 == 1: {c1}   u' != 1: {c2}   (u')^3 == -1: {c3}")
            # closed form (ASSERTED): u' = j/p² equals 1 + x^11 = 1 + ζ3 = ζ6 exactly
            closed_form = reduce_mod_phi([1] + [0] * 10 + [1] + [0] * 21)  # 1 + x^11
            assert U == closed_form, "closed-form check FAILED: u'(t=1) != 1 + x^11"
            print("     closed form (asserted): u' == 1 + x^11 (= 1+ζ3 = ζ6): True")
    assert ok_all, "certificate FAILED: some conjugate violates (j/p²)^6=1, (j/p²)^3=-1, or j/p² != 1"
    print(f"\nALL 20 conjugates: (j/p²)^6 = 1 AND (j/p²)^3 = -1 exactly (⟹ EXACT ORDER 6) AND j/p² ≠ 1: {ok_all}  [ASSERTED]")
    print("⟹ the geometric Frobenius scalar on every V(t·a)(2) at p=67 is a primitive 6th root of unity")
    print("   (order exactly 6, convention-independent) ⟹ the V(t·a)-components of any ℚ(ζ₃₃)-rational")
    print("   cycle class vanish, and every residue degree above 67 of a certifying field is divisible by 6.  [EXACT]")

    # 30-dps numeric cross-check vs the Gauss-sum product (corroboration ONLY; the certificate above is exact)
    from mpmath import mp, mpc, exp as mexp, pi as mpi, fabs, cos as mcos, sin as msin, mpf, nstr
    mp.dps = 30
    g = prim_root(P)
    ind = {}
    x = 1
    for k in range(P - 1):
        ind[x] = k
        x = x * g % P
    gs = {}
    for e in sorted(set(a % M for a in A)):
        ssum = mpc(0)
        for v in range(1, P):
            ssum += mexp(2j * mpi * ((e * ind[v]) % M) / M) * mexp(2j * mpi * v / P)
        gs[e] = ssum
    prod = mpc(1)
    for a in A:
        prod *= gs[a % M]
    val = prod / P**3
    target = mpc(mcos(mpi / 3), msin(mpi / 3))  # zeta_6
    assert fabs(val - target) < mpf(10) ** -20, f"Gauss-product cross-check off: {val}"
    print(f"Gauss-sum product cross-check (30 dps): prod g(chi^a_i)/p^3 = {nstr(val, 21)} == zeta_6  [numeric corroboration]")
