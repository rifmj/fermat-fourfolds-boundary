from math import gcd
from fractions import Fraction
from itertools import combinations

def vec(m, entries):
    v=[0]*(m-1)
    for x in entries:
        x%=m
        assert x!=0
        v[x-1]+=1
    return v

def gens_S(m):
    """Generators of the group S_m = <u(sigma_{p,a}), u(D_m)> in Z^{m-1}."""
    G=[]
    # D_m: (a, m-a) for a=1..m-1 (covers (14,14)=2e14 when a=m/2)
    for a in range(1,m):
        G.append(vec(m,[a,m-a]))
    # standard elements
    for p in sorted({q for q in range(2,m) if m%q==0 and all(q%i for i in range(2,int(q**.5)+1))}):
        if p==2:
            if m%2==0:
                for a in range(1,m//2):
                    if (m-2*a)%m==0 or a%m==0 or (a+m//2)%m==0: continue
                    G.append(vec(m,[a, a+m//2, m-2*a, m//2]))
        else:
            for a in range(1,m//p):
                ent=[a+j*(m//p) for j in range(p)]+[m-p*a]
                if any(e%m==0 for e in ent): continue
                G.append(vec(m,ent))
    return G

def hnf_membership_builder(gens):
    """Return a function testing integer-lattice membership via fraction-free
    row reduction; store basis rows in row-echelon (Hermite-like) form over Z."""
    import copy
    n=len(gens[0])
    rows=[r[:] for r in gens]
    # Hermite normal form via integer row ops (column by column)
    basis=[]
    work=rows
    col=0
    mat=[r[:] for r in work]
    # simple HNF: repeatedly pick pivot col
    piv=[]
    r0=0
    for c in range(n):
        # find rows with nonzero entry in col c at or after r0
        idxs=[i for i in range(r0,len(mat)) if mat[i][c]!=0]
        if not idxs: continue
        # gcd-reduce
        while True:
            idxs=[i for i in range(r0,len(mat)) if mat[i][c]!=0]
            if len(idxs)<=1: break
            idxs.sort(key=lambda i: abs(mat[i][c]))
            i0=idxs[0]
            for i in idxs[1:]:
                q=mat[i][c]//mat[i0][c]
                mat[i]=[mat[i][k]-q*mat[i0][k] for k in range(n)]
        idxs=[i for i in range(r0,len(mat)) if mat[i][c]!=0]
        if not idxs: continue
        i0=idxs[0]
        mat[r0],mat[i0]=mat[i0],mat[r0]
        if mat[r0][c]<0: mat[r0]=[-x for x in mat[r0]]
        piv.append(c)
        r0+=1
    mat=mat[:r0]
    def member(v):
        v=v[:]
        ri=0
        for ri,c in enumerate(piv):
            if v[c]!=0:
                if v[c]%mat[ri][c]!=0: return False
                q=v[c]//mat[ri][c]
                v=[v[k]-q*mat[ri][k] for k in range(len(v))]
        return all(x==0 for x in v)
    return member, len(piv)

# ---- m=21 sanity: xi_21 should be OUTSIDE S_21 (gap generator), 2*xi inside
if __name__ != "__main__":
    import os as _os
    _QUIET = _os.environ.get('SLC_QUIET', '1') == '1'
else:
    _QUIET = False
import sys as _sys, io as _io
_saved = _sys.stdout
if _QUIET:
    _sys.stdout = _io.StringIO()
m=21
mem21,rk=hnf_membership_builder(gens_S(21))
xi21=vec(21,[1,4,16,9,15,18])
print(f"m=21 lattice rank {rk}; xi_21 in S_21: {mem21(xi21)} (expect False); 2*xi_21 in S_21: {mem21([2*x for x in xi21])} (expect True)")

# ---- m=28: test candidates
m=28
mem28,rk28=hnf_membership_builder(gens_S(28))
print(f"m=28 lattice rank {rk28}")
for name,ent in [("S u 3S",[1,9,25,3,19,27]),("S u 11S",[1,9,25,11,15,23])]:
    v=vec(28,ent)
    print(f"  {name}: in S_28: {mem28(v)}; 2x in S_28: {mem28([2*x for x in v])}")

# all 136 join classes: how many are OUTSIDE S_28?
U=[t for t in range(1,28) if gcd(t,28)==1]
def isB4(tup,m=28):
    return sum(tup)%m==0 and all(x%m for x in tup) and all(sum((t*x)%m for x in tup)==3*m for t in U)
trips=[t for t in combinations(range(1,28),3) if sum(t)%28==0]
joins=set()
for t1 in trips:
    for t2 in trips:
        tup=tuple(sorted(t1+t2))
        if tup not in joins and isB4(tup):
            joins.add(tup)
outside=[]
for tup in sorted(joins):
    if not mem28(vec(28,list(tup))):
        outside.append(tup)
print(f"join classes in B^4_28: {len(joins)}; OUTSIDE S_28 (gap generators): {len(outside)}")
for t in outside[:12]: print("   gap join:", t)

_sys.stdout = _saved
