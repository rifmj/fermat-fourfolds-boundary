"""exchange_close — the EXCHANGE move (§88): for open T = S ⊎ A, enumerate T' = S ⊎ B with
q = A ⊎ (−B) a certified-algebraic exchanger; then claim(T') ⟹ claim(T) by the Exchange Lemma:
  claim(T') + claim(q) ⟹ [Aoki 1-4(i), r,s even] claim(T'⊎q) = claim(T ∗ δ),
  δ = (y_1,−y_1,...,y_k,−y_k) decomposable ∈ D^{2k−2} ⟹ [Aoki 1-4(ii)] claim(T).
Exchanger certification: |A|=2 → q grade-2 quadruple (Lefschetz(1,1) on X²_m, UNCONDITIONAL);
|A|=3 → q grade-3 sextuple NOT in the open set (census-complete levels: everything else closed).
Sol referee 2026-07-14: CHAIN-SOUND (transcript sol_exchange_referee.txt).

Outputs per open class: reachable orbit reps partitioned into {open (⟹ claim-EQUIVALENCE),
closed (⟹ CLOSURE of T)}. Calibration (two-sided): must find the 110-pair + 114-triple links;
known state 2026-07-14 = zero closed-reachable at own level (isolated exchange-cliques).

Usage: python3 exchange_close.py            # scan the seven ≤200 survivors, both |A| sizes
       python3 exchange_close.py m a0,..,a5 [open1 open2 ...]   # custom target + open set
"""
import sys, os, time
import importlib.util as ilu
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
_s = ilu.spec_from_file_location('ce', os.path.join(HERE, 'census_even.py'))
ce = ilu.module_from_spec(_s); _s.loader.exec_module(ce)

SURVIVORS = {
    70:  [(1, 20, 24, 42, 61, 62)],
    110: [(1, 24, 62, 71, 81, 91), (1, 31, 55, 71, 81, 91)],
    114: [(1, 7, 78, 79, 86, 91), (1, 13, 43, 72, 103, 110), (1, 13, 43, 80, 102, 103)],
    168: [(1, 25, 79, 121, 127, 151)],
}


def scan_class(m, T, open_canons, U=None, H=None):
    """Returns (eq_links, closed_links); each item = (|A|, A, B, canon(T'))."""
    U = U or ce.units(m)
    H = H or [t for t in U if t <= m // 2]

    def g_ok(c, g):
        if not all(x % m for x in c):
            return False
        return all(sum((t * x) % m for x in c) == g * m for t in H)

    Tcan = ce.canon(T, m, U)
    eq, closed = [], []

    def record(A, B, Tp, qcan_open):
        if qcan_open:
            return
        can = ce.canon(Tp, m, U)
        if can == Tcan:
            return
        (eq if can in open_canons else closed).append((len(A), tuple(A), tuple(B), can))

    # |A| = 2: exchanger q is a grade-2 quadruple (Lefschetz, unconditional)
    for Aidx in combinations(range(6), 2):
        A = [T[i] for i in Aidx]
        S = [T[i] for i in range(6) if i not in Aidx]
        sA = sum(A) % m
        for y1 in range(1, m):
            y2 = (sA - y1) % m
            if y2 == 0 or y1 > y2:
                continue
            q = tuple(sorted(A + [(m - y1) % m, (m - y2) % m]))
            if not g_ok(q, 2):
                continue
            Tp = tuple(sorted(S + [y1, y2]))
            if g_ok(Tp, 3):
                record(A, [y1, y2], Tp, False)

    # |A| = 3: exchanger q is a grade-3 sextuple; must itself be CLOSED (i.e. not in the open set)
    for Aidx in combinations(range(6), 3):
        A = [T[i] for i in Aidx]
        S = [T[i] for i in range(6) if i not in Aidx]
        sA = sum(A) % m
        for y1 in range(1, m):
            for y2 in range(y1, m):
                y3 = (sA - y1 - y2) % m
                if y3 == 0 or y3 < y2:
                    continue
                B = [y1, y2, y3]
                q = tuple(sorted(A + [(m - y) % m for y in B]))
                if not g_ok(q, 3):
                    continue
                Tp = tuple(sorted(S + B))
                if not g_ok(Tp, 3):
                    continue
                record(A, B, Tp, ce.canon(q, m, U) in open_canons)

    return eq, closed


def run(targets):
    all_ok = True
    for m, opens in targets.items():
        t0 = time.time()
        U = ce.units(m)
        H = [t for t in U if t <= m // 2]
        open_canons = {ce.canon(a, m, U) for a in opens}
        for T in opens:
            eq, closed = scan_class(m, T, open_canons, U, H)
            eq_targets = sorted({e[3] for e in eq})
            print(f"m={m} T={T}: EQ-links={len(eq)} -> {len(eq_targets)} classes; "
                  f"CLOSED-links={len(closed)}  [{time.time()-t0:.0f}s]", flush=True)
            for c in eq_targets:
                print(f"   EQUIV: {c}")
            for c in closed[:10]:
                print(f"   *** CLOSURE: {c} ***")
    return all_ok


def calibrate():
    """Two-sided: the 110-pair and 114-triple links MUST be found; m=70/168 must be isolated."""
    ok = True
    U110 = ce.units(110)
    oc = {ce.canon(a, 110, U110) for a in SURVIVORS[110]}
    eq, closed = scan_class(110, (1, 24, 62, 71, 81, 91), oc)
    hit = any(e[3] == ce.canon((1, 31, 55, 71, 81, 91), 110, U110) for e in eq)
    print(f"CALIB 110-pair link: {'FOUND' if hit else 'MISSING'} (must find)"); ok &= hit
    U70 = ce.units(70)
    eq70, cl70 = scan_class(70, (1, 20, 24, 42, 61, 62), {ce.canon((1, 20, 24, 42, 61, 62), 70, U70)})
    print(f"CALIB 70 isolation: eq={len(eq70)} closed={len(cl70)} (must be 0/0)")
    ok &= (not eq70 and not cl70)
    print(f"CALIBRATION {'PASS' if ok else 'FAIL'}")
    return ok


if __name__ == "__main__":
    if len(sys.argv) > 2:
        m = int(sys.argv[1])
        T = tuple(int(x) for x in sys.argv[2].split(','))
        opens = [T] + [tuple(int(x) for x in s.split(',')) for s in sys.argv[3:]]
        run({m: opens})
    else:
        if not calibrate():
            sys.exit(1)
        run(SURVIVORS)
