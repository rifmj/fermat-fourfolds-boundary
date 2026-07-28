"""Route C (agentC105) — EXACT field-of-definition obstruction engine, ported to (m, p, class).

INDEPENDENT port of the §76 exact Jacobi-sum DP (code/l4/exact_jacobi_certificate.py) to arbitrary
parameters (m, p, class a).  This is Route C of a 3-route parallel race on the two OPEN Hodge classes
of the Fermat fourfold X_105^4; Route A computes related quantities by an independent implementation
(no coordination — the cross-check happens at the coordinator level).

OBJECT (mirrors the m=33 engine's normalization exactly):
    For a class a = (a_1,...,a_6), a_i in (Z/m)^*-graded, and a split prime p == 1 (mod m),
    the projective Weil-Jacobi sum
        j(a) := S(a)/(p-1),   S(a) := sum_{v in (F_p^*)^6, sum v == 0} prod_i chi^{a_i}(v_i)  in Z[zeta_m]
    is computed EXACTLY by integer dynamic programming over (partial sum mod p) x (char-exponent mod m).
    The Frobenius scalar acting on the Tate-twisted line V(t*a)(2) is
        u(t*a) := j(t*a)/p^2                     (the "+ prod g / p^3" convention, = the m=33 engine's u')
    an algebraic integer of Z[zeta_m], represented mod Phi_m(x).  (B11: the other sign convention
    negates u; the certified conclusion u != 1 for all t is convention-independent iff additionally
    u != -1 for all t — we certify BOTH.)

CLAIMS certified EXACTLY (no floats in the certificate), for ALL phi(m) units t (Galois x -> x^t):
    (C1) u(t*a) is a root of unity:  u(t*a)^ord == 1 for some ord | (2m), reported per t;
    (C2) u(t*a) != 1  exactly   (the headline obstruction);
    (C2b) u(t*a) != -1 exactly   (so the conclusion is sign-convention-independent);
    (C3) exact closed form of u(t*a) as +/- x^j when it is a signed monomial (root of unity in
         mu_{2m} = {+/- zeta_m^k}), else the full reduced vector.

CALIBRATION (mandatory, B4): reproduce the banked m=33 / p=67 certificate before any m=105 news:
    u(a,67) = 1 + x^11 = 1 + zeta_3 = zeta_6, all 20 conjugates in mu_6, none = +/-1.

Usage:
    python3 obstruction105.py calib                 # m=33 p=67 calibration
    python3 obstruction105.py run <m> <p> <class>   # class in {a1,a2} for m=105, or 'A' for m=33
    python3 obstruction105.py both <m> <p>          # run both m=105 classes at prime p
All receipts are printed AND appended+flushed live to data/l4/obstruction105.log.
"""
import sys
import os
from math import gcd

LOG = __file__.rsplit("/code/", 1)[0] + "/data/l4/obstruction105.log"

# ---- classes ----
CLASSES = {
    (33, "A"): (7, 10, 13, 19, 22, 28),          # the m=33 calibration class (banked §76)
    (105, "a1"): (1, 22, 43, 64, 90, 95),
    (105, "a2"): (3, 24, 50, 66, 85, 87),
}


def log(msg, also_print=True):
    if also_print:
        print(msg)
    with open(LOG, "a") as f:
        f.write(msg + "\n")
        f.flush()


# ---------- cyclotomic polynomial Phi_m via Moebius divisor product ----------
def _polmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                if bj:
                    r[i + j] += ai * bj
    return r


def _poldiv_exact(num, den):
    num = num[:]
    q = [0] * (len(num) - len(den) + 1)
    for i in range(len(q) - 1, -1, -1):
        c = num[i + len(den) - 1]
        assert c % den[-1] == 0, "non-exact division building Phi_m"
        q[i] = c // den[-1]
        for j, dj in enumerate(den):
            num[i + j] -= q[i] * dj
    assert all(c == 0 for c in num), "nonzero remainder building Phi_m"
    return q


def _mobius(n):
    if n == 1:
        return 1
    res, p, nn = 1, 2, n
    while p * p <= nn:
        if nn % p == 0:
            nn //= p
            if nn % p == 0:
                return 0
            res = -res
        p += 1
    if nn > 1:
        res = -res
    return res


def _divisors(n):
    ds = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            ds.append(i)
            if i != n // i:
                ds.append(n // i)
        i += 1
    return sorted(ds)


def cyclotomic_poly(m):
    """Phi_m(x) = prod_{d|m} (x^d - 1)^{mu(m/d)}, computed by exact polynomial division.
    Returns coefficient list, index 0 = constant term, length phi(m)+1."""
    def xd(d):
        v = [0] * (d + 1)
        v[0] = -1
        v[d] = 1
        return v
    num = [1]
    den = [1]
    for d in _divisors(m):
        mu = _mobius(m // d)
        if mu == 1:
            num = _polmul(num, xd(d))
        elif mu == -1:
            den = _polmul(den, xd(d))
    phi = _poldiv_exact(num, den)
    # normalise trailing zeros away (shouldn't be any) and assert monic
    while len(phi) > 1 and phi[-1] == 0:
        phi.pop()
    assert phi[-1] == 1, "Phi_m not monic"
    return phi


# ---------- reduction mod Phi_m ----------
def make_reducer(m):
    phi = cyclotomic_poly(m)
    deg = len(phi) - 1  # = phi(m)

    def reduce_mod_phi(vec):
        """vec: integer coeff list (any length, coeff of x^i). Reduce mod Phi_m, return length-deg list."""
        v = vec[:]
        for i in range(len(v) - 1, deg - 1, -1):
            c = v[i]
            if c:
                # subtract c * x^{i-deg} * phi
                base = i - deg
                for j in range(deg + 1):
                    v[base + j] -= c * phi[j]
        out = v[:deg]
        if len(out) < deg:
            out = out + [0] * (deg - len(out))
        return out

    return reduce_mod_phi, deg, phi


# ---------- exact Jacobi sum via integer DP ----------
def prim_root(p):
    for g in range(2, p):
        seen, x = set(), 1
        for _ in range(p - 1):
            x = x * g % p
            seen.add(x)
        if len(seen) == p - 1:
            return g
    raise RuntimeError("no primitive root found")


def jacobi_exact(alpha, p, m):
    """S(alpha) = sum_{v_1..v_6 in F_p^*, sum v == 0} prod chi^{alpha_i}(v_i), returned as an integer
    exponent-vector of length m (coeff of x^e in Z[x]/(x^m - 1)); chi = the char sending prim-root g -> zeta_m.
    DP over (partial sum mod p) with per-cell length-m exponent-count vectors. Exact integers only.
    Uses the standard prune (skip empty rows) and pre-tabulated exponent shifts."""
    g = prim_root(p)
    ind = [0] * p           # discrete log base g: ind[v] for v in 1..p-1
    x = 1
    for k in range(p - 1):
        ind[x] = k
        x = x * g % p
    # precompute, for each character exponent a_i, the map v -> shift = (a_i * ind[v]) mod m
    dp = [None] * p         # dp[s] = length-m list or None
    dp[0] = [0] * m
    dp[0][0] = 1
    for ai in alpha:
        # precompute shift[v] for v in 1..p-1
        shift = [0] * p
        for v in range(1, p):
            shift[v] = (ai * ind[v]) % m
        ndp = [None] * p
        for s in range(p):
            row = dp[s]
            if row is None:
                continue
            # any nonzero?
            for v in range(1, p):
                t = s + v
                if t >= p:
                    t -= p
                sh = shift[v]
                nrow = ndp[t]
                if nrow is None:
                    nrow = [0] * m
                    ndp[t] = nrow
                # add row shifted by sh (mod m) into nrow
                # nrow[(e+sh)%m] += row[e]
                if sh == 0:
                    for e in range(m):
                        c = row[e]
                        if c:
                            nrow[e] += c
                else:
                    ms = m - sh
                    for e in range(m):
                        c = row[e]
                        if c:
                            ee = e + sh
                            if ee >= m:
                                ee -= m
                            nrow[ee] += c
        dp = ndp
    res = dp[0]
    if res is None:
        return [0] * m
    return res


def conj(vec_m, t, m):
    """Galois x -> x^t on a length-m exponent vector."""
    out = [0] * m
    for e, c in enumerate(vec_m):
        if c:
            out[(e * t) % m] += c
    return out


# ---------- root-of-unity / monomial analysis ----------
def mul_mod(a, b, m, reduce_mod_phi):
    """(a*b) in Z[x]/(x^m-1) then reduced mod Phi_m. a,b are length-deg reduced vectors (or length<=m)."""
    r = [0] * m
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                if bj:
                    r[(i + j) % m] += ai * bj
    return reduce_mod_phi(r)


def order_of_unit(u, m, reduce_mod_phi, deg, maxord=None):
    """If u is a root of unity, return its multiplicative order (dividing 2m); else return None.
    We test powers up to 2m (roots of unity in Q(zeta_m) are exactly {+/- zeta_m^k}, order | 2m)."""
    if maxord is None:
        maxord = 2 * m
    one = [1] + [0] * (deg - 1)
    cur = u[:]
    if cur == one:
        return 1
    for k in range(2, maxord + 1):
        cur = mul_mod(cur, u, m, reduce_mod_phi)
        if cur == one:
            return k
    return None


def as_signed_monomial(u, m, deg):
    """If u == +/- x^j (mod Phi_m) as a reduced vector, return (sign, j); else None.
    A reduced vector of length deg represents sum c_i x^i with i<deg; +x^j for j<deg is trivial,
    but -x^j and x^j for j>=deg reduce to multi-term vectors, so we must test by comparing against
    the reduced form of +/- x^j for all j in 0..m-1."""
    # Build reduced forms of x^j and -x^j for all j, compare.
    # (cheap: deg<=48, m<=105)
    return None  # placeholder; real impl attached below via a closure that has reduce_mod_phi


def make_monomial_tester(m, deg, reduce_mod_phi):
    table = {}   # reduced-tuple -> (sign, j)
    for j in range(m):
        xj = [0] * m
        xj[j] = 1
        red = tuple(reduce_mod_phi(xj))
        table.setdefault(red, ("+", j))
        negred = tuple(reduce_mod_phi([-c for c in [0] * j + [1]]))
        table.setdefault(negred, ("-", j))

    def test(u):
        return table.get(tuple(u), None)

    return test


# ---------- driver ----------
def analyse(m, p, a, label, do_print=True):
    reduce_mod_phi, deg, phi = make_reducer(m)
    mono_test = make_monomial_tester(m, deg, reduce_mod_phi)
    one = [1] + [0] * (deg - 1)
    neg_one = reduce_mod_phi([-1])
    units = [t for t in range(1, m) if gcd(t, m) == 1]

    log(f"\n{'='*78}", do_print)
    log(f"[Route C / agentC105]  m={m}  p={p}  class {label} = {a}", do_print)
    log(f"  p == 1 mod m: {p % m == 1}   good reduction (p ∤ m): {m % p != 0}   deg Phi_{m}={deg}={ 'phi('+str(m)+')' }  #units={len(units)}", do_print)

    S = jacobi_exact(a, p, m)
    pm1 = p - 1
    assert all(c % pm1 == 0 for c in S), "S not divisible by (p-1)!"
    J = [c // pm1 for c in S]   # j(a) in Z[x]/(x^m-1), length m
    nz = [(i, c) for i, c in enumerate(J) if c]
    log(f"  j({label}) mod x^{m}-1: {len(nz)} nonzero coeffs; sample {nz[:4]}{' ...' if len(nz)>4 else ''}", do_print)

    all_ne1 = True
    all_ne_pm1 = True
    orders = {}
    monos = {}
    vals = {}
    for t in units:
        Jt = reduce_mod_phi(conj(J, t, m))
        # divide by p^2 exactly
        assert all(c % (p * p) == 0 for c in Jt), f"j(t*a) not divisible by p^2 at t={t} (label {label})"
        U = [c // (p * p) for c in Jt]      # u(t*a) = j/p^2, reduced mod Phi_m
        c_ne1 = (U != one)
        c_ne_neg1 = (U != neg_one)
        if not c_ne1:
            all_ne1 = False
        if not c_ne_neg1:
            all_ne_pm1 = False
        ordu = order_of_unit(U, m, reduce_mod_phi, deg)
        orders[t] = ordu
        mono = mono_test(U)
        monos[t] = mono
        vals[t] = U
    return {
        "m": m, "p": p, "label": label, "a": a, "deg": deg, "units": units,
        "J": J, "vals": vals, "orders": orders, "monos": monos,
        "all_ne1": all_ne1, "all_ne_pm1": all_ne_pm1,
    }


def report(res, do_print=True):
    m, p, label = res["m"], res["p"], res["label"]
    units = res["units"]
    orders, monos, vals = res["orders"], res["monos"], res["vals"]
    # summarize order distribution
    from collections import Counter
    ordc = Counter(orders.values())
    log(f"  order distribution over {len(units)} conjugates: {dict(sorted(ordc.items(), key=lambda kv:(kv[0] is None, kv[0])))}", do_print)
    # which t give u=1 ?
    ones = [t for t in units if vals[t] == ([1] + [0]*(res['deg']-1))]
    neg_ones = [t for t in units if orders[t] == 2 and (monos[t] == ("-", 0))]
    non_ru = [t for t in units if orders[t] is None]
    log(f"  t with u==1 (obstruction VANISHES): {ones if ones else 'NONE'}", do_print)
    log(f"  t with u==-1: {neg_ones if neg_ones else 'NONE'}", do_print)
    if non_ru:
        log(f"  t where u is NOT a root of unity (order None): {non_ru}", do_print)
    # value table: show t=1 and a few conjugates, in monomial form where possible
    def fmt(t):
        mo = monos[t]
        if mo is not None:
            sgn, j = mo
            return f"{sgn}x^{j}(ord {orders[t]})"
        return f"[vec ord {orders[t]}]"
    sample_ts = units[:8]
    log(f"  u values (sample): " + ", ".join(f"t={t}:{fmt(t)}" for t in sample_ts), do_print)
    # full monomial exponent table (compact)
    mono_summary = {}
    for t in units:
        mo = monos[t]
        key = (mo[0], "x^%d" % mo[1]) if mo is not None else ("vec", "")
        mono_summary.setdefault(f"{mo[0]}x^{mo[1]}" if mo is not None else "vec", []).append(t)
    log(f"  monomial classes: { {k: len(v) for k,v in sorted(mono_summary.items())} }", do_print)
    verdict = "ALL 48 conjugates u != 1" if (m == 105 and res["all_ne1"]) else (
        f"ALL {len(units)} conjugates u != 1" if res["all_ne1"] else "SOME conjugate has u == 1 (VANISHING)")
    log(f"  >>> VERDICT [{label}]: {verdict};  u != -1 for all t: {res['all_ne_pm1']}  <<<", do_print)
    # sign-convention certificate line
    if res["all_ne1"] and res["all_ne_pm1"]:
        log(f"      SIGN-CONVENTION CERTIFICATE: u ∉ {{+1,-1}} for all {len(units)} conjugates ⟹ under EITHER", do_print)
        log(f"      Jacobi-sum sign convention (u or -u), the Frobenius scalar on V(t·a)(2) is ≠ 1. [EXACT]", do_print)
    elif res["all_ne1"] and not res["all_ne_pm1"]:
        log(f"      NOTE: u != 1 for all t but u == -1 for some t; the '+' convention still gives ≠1 everywhere,", do_print)
        log(f"      but the '-' convention would map those to +1 — so the obstruction is CONVENTION-DEPENDENT there.", do_print)
    return res


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "calib"
    if mode == "calib":
        log(f"\n########## CALIBRATION (B4): reproduce banked m=33 / p=67 §76 certificate ##########")
        res = analyse(33, 67, CLASSES[(33, "A")], "A")
        report(res)
        # explicit closed-form check: u(1) should equal 1 + x^11 = 1 + zeta_3 = zeta_6
        reduce_mod_phi, deg, phi = make_reducer(33)
        u1 = res["vals"][1]
        target = reduce_mod_phi([1] + [0]*10 + [1])   # 1 + x^11
        log(f"  CALIB closed form: u(a,67) == 1 + x^11 (= 1+zeta_3 = zeta_6): {u1 == target}   [expected True]")
        log(f"  CALIB order of u(a,67): {res['orders'][1]}   [expected 6]")
        ok = (res["all_ne1"] and res["all_ne_pm1"] and u1 == target and res["orders"][1] == 6)
        log(f"  ########## CALIBRATION {'PASS' if ok else 'FAIL'} ##########")
    elif mode == "run":
        m = int(sys.argv[2]); p = int(sys.argv[3]); lab = sys.argv[4]
        res = analyse(m, p, CLASSES[(m, lab)], lab)
        report(res)
    elif mode == "both":
        m = int(sys.argv[2]); p = int(sys.argv[3])
        for lab in ("a1", "a2"):
            res = analyse(m, p, CLASSES[(m, lab)], lab)
            report(res)
    else:
        print("unknown mode", mode)
