/-
  BoundaryCore.lean — machine-checked FINITE CORE of
  "The Hodge conjecture for Fermat fourfolds of odd degree at most 199"
  (the manuscript was retitled on 2026-07-28; it was "New cases and the open boundary of
  the Hodge conjecture for Fermat fourfolds" when this file was written).

  Pure Lean 4 (NO mathlib; imports only the generated BoundaryData). Compiles standalone.
  Reproduces, inside Lean's `native_decide` trust path, the exact-arithmetic receipts of
  `../anc/` (run_all.sh smoke tier), namely:

    I    every closure identity of Theorems A / A′ / A″ (splits, vanishing pairs, 10-multiset
         identities, 5-standard form, Hodge grades, the (33,33) self-pair and its UNIQUENESS)
    II   census anchors m ∈ {9,21,27,33,39,45}: per-level orbit tallies
         (decomposable/quasi/standard/*-split/survivor) matching the census receipt, and the
         survivor uniqueness at 33 (= the da Silva witness orbit) and 45 (= the A′ row)
    III  every S_m-lattice verdict of the manuscript: 13 OUT (gap classes) via modular kernel
         witnesses over GF(q), 3 IN + the m=168 coset identity via exact re-summed integer
         certificates — against Lean's own procedurally generated generator matrix gensS
    IV   Theorem C: the exact ℤ[x]/Φ₃₃ Frobenius certificate at p=67 — (j/p²)⁶ = 1 and
         j/p² ≠ 1 for ALL 20 conjugates, closed form j/p² = 1 + ζ₃₃¹¹; plus the m=39
         divisorial calibration j = p² at p=79 (B4 instrument check), the m=66 consistency
         u(2w@66,67) = 1+ζ₃ = u(w@33,67), and the A′ multiplicativity instance
         p·j(a) = j(S)·j(Q) at m=45, p=181
    V    the ξ₂₈ erratum pair of Prop w168 (misprint refuted, replacement verified)
         and the Prop-D even-m caveat (inadmissible ⟹ decomposable, all m ≤ 250)

  What is NOT here: the geometric content (Shioda–Katsura transport, Aoki's theorems,
  Lefschetz (1,1), finite-morphism descent). Those are the cited inputs; the deduction
  chains from them to the paper's theorems are machine-checked in BoundaryClaim.lean.
  Trust base: one `native_decide` axiom (the Lean compiler).
-/
import BoundaryData

namespace BoundaryCore

/-! ### §0 Basics: residues, units, grades, sorting -/

def lsum : List Nat → Nat := List.foldr (· + ·) 0

def unitsList (m : Nat) : List Nat :=
  ((List.range m).drop 1).filter (fun t => Nat.gcd t m == 1)

/-- one representative of each {t, m−t} pair of units (grade sums at t and m−t are
    complementary, so grade-CHECKS may use these; definitions always use full units). -/
def halfUnits (m : Nat) : List Nat :=
  (unitsList m).filter (fun t => t ≤ m / 2)

def gradeSumAt (m t : Nat) (a : List Nat) : Nat :=
  lsum (a.map (fun x => (t * x) % m))

/-- Hodge character of grade g at level m: length 2g, entries in [1,m−1], and
    Σᵢ ⟨t aᵢ⟩ = g·m for EVERY unit t (the manuscript's §1 definition, full units). -/
def isHodgeB (m g : Nat) (a : List Nat) : Bool :=
  a.length == 2 * g &&
  a.all (fun x => 0 < x && x < m) &&
  (unitsList m).all (fun t => gradeSumAt m t a == g * m)

def orderedInsert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: orderedInsert x ys

def insSort : List Nat → List Nat
  | [] => []
  | x :: xs => orderedInsert x (insSort xs)

/-- multiset equality of two lists. -/
def msEq (a b : List Nat) : Bool := insSort a == insSort b

def galAct (m t : Nat) (a : List Nat) : List Nat :=
  insSort (a.map (fun x => (t * x) % m))

def listLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => x < y || (x == y && listLt xs ys)

/-- canonical (lex-least sorted) Galois-orbit representative. -/
def canonRep (m : Nat) (a : List Nat) : List Nat :=
  (unitsList m).foldl
    (fun best t => let c := galAct m t a; if listLt c best then c else best)
    (insSort a)

/-! ### §1 Sub-multiset splits (chosen, complement), |chosen| = k -/

def splitsK : List Nat → Nat → List (List Nat × List Nat)
  | l, 0 => [([], l)]
  | [], _ + 1 => []
  | x :: xs, k + 1 =>
      ((splitsK xs k).map (fun (c, d) => (x :: c, d))) ++
      ((splitsK xs (k + 1)).map (fun (c, d) => (c, x :: d)))

/-! ### §2 The classifiers (mirroring census_scan_v2.py; precedence dec → quasi → std → star) -/

def hasVanishingPair (m : Nat) (a : List Nat) : Bool :=
  (splitsK a 2).any (fun (c, _) => lsum c % m == 0)

/-- da Silva quasi-decomposability: some a ⊎ {k,m−k} splits into two grade-2 Hodge quadruples. -/
def quasiSplitsAt (m : Nat) (a : List Nat) (k : Nat) : Bool :=
  let T := insSort (a ++ [k, m - k])
  (splitsK T 4).any (fun (c, d) => isHodgeB m 2 c && isHodgeB m 2 d)

def quasiCheck (m : Nat) (a : List Nat) : Bool :=
  ((List.range ((m + 1) / 2)).drop 1).any (fun k => quasiSplitsAt m a k)

/-- Aoki 5-standard grade-3 sextuples σ_{5,x} = {x, x+m/5, …, x+4m/5, m−5x} (5 ∣ m, m > 5). -/
def stdSextuples (m : Nat) : List (List Nat) :=
  if m % 5 == 0 && m > 5 then
    let d := m / 5
    ((List.range m).drop 1).filterMap (fun x =>
      if (5 * x) % m == 0 then none else
      let e := ((List.range 5).map (fun k => (x + k * d) % m)) ++ [(m - (5 * x) % m) % m]
      if e.all (fun v => v != 0) then some (insSort e) else none)
  else []

def stdCanonSet (m : Nat) : List (List Nat) :=
  (stdSextuples m).foldl
    (fun acc s => let c := canonRep m s; if acc.contains c then acc else c :: acc) []

def stdCheck (m : Nat) (a : List Nat) : Bool :=
  (stdCanonSet m).contains (canonRep m a)

/-- Theorem A test: split into two zero-sum triples. -/
def starCheck (m : Nat) (a : List Nat) : Bool :=
  (splitsK a 3).any (fun (c, d) => lsum c % m == 0 && lsum d % m == 0)

/-! ### §3 The census: enumerate sorted grade-3 Hodge sextuples, canonize, classify -/

/-- all sorted sextuples over [1,m−1] passing the cheap filters (sum ≡ 0, half-unit grades);
    the census list then applies the FULL Hodge definition on top. -/
def rawCandidates (m : Nat) : Array (List Nat) := Id.run do
  let H := halfUnits m
  let mut out : Array (List Nat) := #[]
  for a0 in [1:m] do
    for a1 in [a0:m] do
      for a2 in [a1:m] do
        for a3 in [a2:m] do
          for a4 in [a3:m] do
            for a5 in [a4:m] do
              if (a0 + a1 + a2 + a3 + a4 + a5) % m == 0 then
                let a := [a0, a1, a2, a3, a4, a5]
                if H.all (fun t => gradeSumAt m t a == 3 * m) then
                  out := out.push a
  return out

def hodgeSextuples (m : Nat) : List (List Nat) :=
  (rawCandidates m).toList.filter (isHodgeB m 3)

def orbitReps (m : Nat) : List (List Nat) :=
  (hodgeSextuples m).foldl
    (fun acc a => let c := canonRep m a; if acc.contains c then acc else acc ++ [c]) []

inductive Kind where
  | dec | quasi | std | star | surv
deriving BEq, Repr

def classify (m : Nat) (a : List Nat) : Kind :=
  if hasVanishingPair m a then .dec
  else if quasiCheck m a then .quasi
  else if stdCheck m a then .std
  else if starCheck m a then .star
  else .surv

/-- (n_reps, #dec, #quasi, #std, #star, #surv) — the census tallies. -/
def censusTallies (m : Nat) : Nat × Nat × Nat × Nat × Nat × Nat :=
  let reps := orbitReps m
  let ks := reps.map (classify m)
  (reps.length, (ks.filter (· == .dec)).length, (ks.filter (· == .quasi)).length,
   (ks.filter (· == .std)).length, (ks.filter (· == .star)).length,
   (ks.filter (· == .surv)).length)

def survivorsOf (m : Nat) : List (List Nat) :=
  (orbitReps m).filter (fun a => classify m a == .surv)

/-! #### Census theorems — tallies pinned to the manuscript's census receipt
    (data/l4/census_witnesses_odd.json; m = 9, 27 recomputed; small levels classical). -/

def wDaSilva : List Nat := [1, 4, 16, 22, 25, 31]

/-- small classical levels (9 recomputed; 21/27 match the census receipt: 61+3q, 67+1q). -/
theorem census_small :
    ((censusTallies 9 == (10, 10, 0, 0, 0, 0)) &&
     (censusTallies 21 == (64, 61, 3, 0, 0, 0)) &&
     (censusTallies 27 == (68, 67, 1, 0, 0, 0))) = true := by native_decide

theorem census_33 :
    ((censusTallies 33 == (104, 102, 1, 0, 0, 1)) &&
     (survivorsOf 33 == [wDaSilva])) = true := by native_decide

theorem census_39 :
    ((censusTallies 39 == (140, 137, 1, 0, 2, 0)) &&
     (survivorsOf 39 == [])) = true := by native_decide

theorem census_45 :
    ((censusTallies 45 == (245, 237, 6, 1, 0, 1)) &&
     (survivorsOf 45 == [[1, 19, 20, 28, 30, 37]])) = true := by native_decide

/-! ### §4 Theorem A / A′ / A″ identity receipts (verify_closure_identities.py, in-kernel) -/

/-- conjugate types of a *-split: |tβ′| + |tγ′| = 3 with each part in {1,2}, every unit t. -/
def starTypesOK (m : Nat) (b c : List Nat) : Bool :=
  (unitsList m).all (fun t =>
    let gb := gradeSumAt m t b / m
    let gc := gradeSumAt m t c / m
    gradeSumAt m t b % m == 0 && gradeSumAt m t c % m == 0 &&
    gb + gc == 3 && (gb == 1 || gb == 2) && (gc == 1 || gc == 2))

theorem thmA_identities :
    -- m=39, both orbits: Hodge grade 3, zero-sum-triple split, conjugate types
    ((isHodgeB 39 3 [1, 7, 16, 22, 34, 37] &&
     msEq [1, 7, 16, 22, 34, 37] ([1, 16, 22] ++ [7, 34, 37]) &&
     lsum [1, 16, 22] % 39 == 0 && lsum [7, 34, 37] % 39 == 0 &&
     starTypesOK 39 [1, 16, 22] [7, 34, 37]) &&
    (isHodgeB 39 3 [1, 14, 16, 22, 29, 35] &&
     msEq [1, 14, 16, 22, 29, 35] ([1, 16, 22] ++ [14, 29, 35]) &&
     lsum [14, 29, 35] % 39 == 0 &&
     starTypesOK 39 [1, 16, 22] [14, 29, 35])) = true := by native_decide

/-- one A′ row: 10-multiset identity a ⊎ p₁ ⊎ p₂ = S ⊎ Q, S 5-standard, Q grade-2 Hodge. -/
def aprimeRow (m : Nat) (a p1 p2 S Q : List Nat) : Bool :=
  isHodgeB m 3 a &&
  lsum p1 % m == 0 && lsum p2 % m == 0 &&
  msEq (a ++ p1 ++ p2) (S ++ Q) &&
  (stdSextuples m).contains (insSort S) &&
  isHodgeB m 2 Q

theorem thmAprime_identities :
    (aprimeRow 45 [1, 19, 20, 28, 30, 37] [5, 40] [10, 35] [1, 10, 19, 28, 37, 40] [5, 20, 30, 35] &&
    aprimeRow 105 [3, 24, 50, 66, 85, 87] [15, 90] [45, 60] [3, 24, 45, 66, 87, 90] [15, 50, 60, 85] &&
    aprimeRow 105 [1, 22, 43, 64, 90, 95] [5, 100] [20, 85] [1, 22, 43, 64, 85, 100] [5, 20, 90, 95])
    = true := by native_decide

def a66 : List Nat := [2, 8, 32, 44, 50, 62]
def S66 : List Nat := [2, 8, 32, 41, 50, 65]
def Q66 : List Nat := [1, 25, 44, 62]

theorem thmApp_identities :
    -- w is the da Silva witness (Galois-conjugate of his displayed representative)
    (isHodgeB 33 3 wDaSilva &&
     (unitsList 33).any (fun t => galAct 33 t [7, 10, 13, 19, 22, 28] == insSort wDaSilva) &&
     -- a = 2w mod 66, grade-3 Hodge at 66
     (wDaSilva.map (fun x => (2 * x) % 66) == a66) && isHodgeB 66 3 a66 &&
     -- augmented identity a ⊎ (1,65) ⊎ (25,41) = Q ⊎ S
     msEq (a66 ++ [1, 65] ++ [25, 41]) (Q66 ++ S66) && isHodgeB 66 2 Q66 &&
     -- S ⊎ (33,33) = (2,32,33,65) ⊎ (8,33,41,50), both grade-2 Hodge
     msEq (S66 ++ [33, 33]) ([2, 32, 33, 65] ++ [8, 33, 41, 50]) &&
     isHodgeB 66 2 [2, 32, 33, 65] && isHodgeB 66 2 [8, 33, 41, 50] &&
     -- (33,33) is a legitimate element of M₆₆(1): ⟨33t⟩ + ⟨33t⟩ = 66 for every unit t
     (unitsList 66).all (fun t => 2 * ((33 * t) % 66) == 66)) = true := by native_decide

/-- UNIQUENESS of the quasi-witness (Thm A″ / Remark (iv)): among all vanishing pairs
    {k, 66−k}, k ≤ 33, ONLY the self-pair k = 33 splits S ⊎ {k,66−k} into two Hodge quadruples. -/
theorem thmApp_witness_unique :
    ((List.range 34).drop 1).filter (fun k => quasiSplitsAt 66 S66 k) = [33] := by native_decide

/-! ### §5 ξ₂₈ erratum receipts (Prop w168) and the Prop-D even-m caveat -/

theorem xi28_erratum :
    (-- the printed ξ₂₈ = (1,9,25,12,20,24) is NOT a character (not zero-sum mod 28):
    (lsum [1, 9, 25, 12, 20, 24] % 28 != 0) &&
    -- the repaired ξ₂₈ = (1,9,18)∗(10,21,25) IS a grade-3 Hodge character of X⁴₂₈:
    isHodgeB 28 3 (insSort ([1, 9, 18] ++ [10, 21, 25])) &&
    lsum [1, 9, 18] % 28 == 0 && lsum [10, 21, 25] % 28 == 0) = true := by native_decide

/-- Remark (even m): every INADMISSIBLE 5-standard multiset with nonzero entries contains a
    vanishing pair (hence is decomposable) — all 5 ∣ m ≤ 250. -/
def propD_evenm_caveat : Bool := Id.run do
  let mut ok := true
  let mut ncase := 0
  for m5 in [2:51] do
    let m := 5 * m5
    let d := m / 5
    for x in [1:m] do
      if (5 * x) % m != 0 && d / Nat.gcd x d ≤ 2 then
        let e := ((List.range 5).map (fun k => (x + k * d) % m)) ++ [(m - (5 * x) % m) % m]
        if e.all (fun v => v != 0) then
          ncase := ncase + 1
          if !hasVanishingPair m e then
            ok := false
  return ok && ncase > 0

theorem propD_evenm : propD_evenm_caveat = true := by native_decide

/-! ### §6 The S_m lattice: generators, kernel witnesses, certificates
    (ports s_lattice_core.gens_S verbatim — same generator ORDER, pinned by fingerprints). -/

/-- multiplicity vector of a multiset of nonzero residues, as Array of length m−1. -/
def vecOf (m : Nat) (a : List Nat) : Array Nat := Id.run do
  let mut v : Array Nat := .replicate (m - 1) 0
  for x in a do
    let r := x % m
    v := v.set! (r - 1) (v[r - 1]! + 1)
  return v

def isPrimeNat (n : Nat) : Bool :=
  n ≥ 2 && (((List.range n).drop 2).all (fun q => n % q != 0))

/-- generators of S_m, in the exact order of s_lattice_core.gens_S:
    all pairs (a, m−a), a = 1..m−1; then per prime p ∣ m ascending, the standard blocks. -/
def gensS (m : Nat) : Array (Array Nat) := Id.run do
  let mut G : Array (Array Nat) := #[]
  for a in [1:m] do
    G := G.push (vecOf m [a, m - a])
  for p in [2:m] do
    if isPrimeNat p && m % p == 0 then
      if p == 2 then
        if m % 2 == 0 then
          for a in [1:m/2] do
            if !((m - 2 * a) % m == 0 || a % m == 0 || (a + m / 2) % m == 0) then
              G := G.push (vecOf m [a, a + m / 2, m - 2 * a, m / 2])
      else
        for a in [1:m/p] do
          let ent := ((List.range p).map (fun j => a + j * (m / p))) ++ [m - p * a]
          if ent.all (fun e => e % m != 0) then
            G := G.push (vecOf m ent)
  return G

def gensFingerprint (G : Array (Array Nat)) : Nat := Id.run do
  let M := 1000000007
  let mut fp := 0
  for i in [0:G.size] do
    let g := G[i]!
    for j in [0:g.size] do
      if g[j]! != 0 then
        fp := (fp + g[j]! * (i + 1) * (j + 1)) % M
  return fp

/-- the fingerprints of Lean's gensS match the generating script's (count + weighted hash):
    certificate INDICES below therefore address the same generators. -/
theorem gensS_fingerprints :
    BoundaryData.gensFingerprints.all
      (fun (m, n, fp) => (gensS m).size == n && gensFingerprint (gensS m) == fp)
    = true := by native_decide

def dotModQ (q : Nat) (phi : List Nat) (v : Array Nat) : Nat := Id.run do
  let mut s := 0
  let mut i := 0
  for c in phi do
    s := (s + c * v[i]!) % q
    i := i + 1
  return s

/-- OUT verdict check: φ kills every generator mod q but not u — hence u ∉ S_m
    (an integer combination would force φ·u ≡ 0 mod q). -/
def kernelWitnessOK (m q : Nat) (phi cls : List Nat) : Bool :=
  phi.length == m - 1 &&
  (gensS m).all (fun g => dotModQ q phi g == 0) &&
  dotModQ q phi (vecOf m cls) != 0

/-- exact re-summation of an integer certificate over the generators. -/
def certSumOK (m : Nat) (cert : List (Nat × Int)) (target : Array Int) : Bool := Id.run do
  let G := gensS m
  let mut s : Array Int := .replicate (m - 1) 0
  for (i, c) in cert do
    if h : i < G.size then
      let g := G[i]
      for j in [0:m-1] do
        s := s.set! j (s[j]! + c * (Int.ofNat g[j]!))
    else
      return false
  return s == target

def natVecToInt (v : Array Nat) : Array Int := v.map Int.ofNat

def scaleVec (c : Int) (v : Array Nat) : Array Int := v.map (fun x => c * Int.ofNat x)

def subVec (a b : Array Int) : Array Int := Id.run do
  let mut r := a
  for j in [0:b.size] do
    r := r.set! j (r[j]! - b[j]!)
  return r

/-- All 13 OUT verdicts: each class is Hodge grade 3, ν ∉ S_m by kernel witness, and
    2ν ∈ S_m by an exactly re-summed certificate (the gap-group 2-torsion).  (`ν` is the
    manuscript's lattice valuation of `prop:ident`, written `u` before the 2026-07-28
    revision — hence the generated field name `cert2u` in `BoundaryData`.) -/
theorem lattice_out_verdicts :
    BoundaryData.outVerdicts.all (fun r =>
      isHodgeB r.m 3 r.cls &&
      kernelWitnessOK r.m r.q r.phi r.cls &&
      certSumOK r.m r.cert2u (scaleVec 2 (vecOf r.m r.cls)))
    = true := by native_decide

/-- The 3 IN verdicts (m=210 with 40 generators and coefficients ±1; m=45; m=105-ζ₇):
    u ∈ S_m by exact re-summation. -/
theorem lattice_in_verdicts :
    BoundaryData.inVerdicts.all (fun r =>
      isHodgeB r.m 3 r.cls &&
      certSumOK r.m r.cert (natVecToInt (vecOf r.m r.cls)))
    = true := by native_decide

theorem lattice_in_210_pm1 :
    (BoundaryData.inVerdicts.head?.map (fun r =>
      r.m == 210 && r.cert.length == 40 &&
      r.cert.all (fun (_, c) => c == 1 || c == -1))) = some true := by native_decide

/-- m=168 coset identity (Prop w168): vec(a) − vec(6·ξ₂₈) ∈ S₁₆₈. -/
theorem lattice_coset168 :
    (certSumOK 168 BoundaryData.coset168cert
      (subVec (natVecToInt (vecOf 168 BoundaryData.coset168cls))
              (natVecToInt (vecOf 168 BoundaryData.coset168xi))) &&
     (BoundaryData.coset168xi == [1, 9, 18, 10, 21, 25].map (6 * ·))) = true := by native_decide

/-! ### §7 Exchange edges (the manuscript's even-sector wall structure): each edge (T, A, B): q = A ⊎ (−B) is a grade-2 Hodge
    quadruple, T′ = (T∖A) ⊎ B is grade-3 Hodge, T′ ⊎ q = T ⊎ B ⊎ (−B), and T′ is the
    t-conjugate of the named target wall member.  (Consumed by BoundaryClaim's wall theorems.) -/

def edgeOK (e : BoundaryData.ExEdge) : Bool :=
  let m := e.m
  let negB := e.B.map (fun y => (m - y % m) % m)
  isHodgeB m 3 e.T && isHodgeB m 3 e.Tp && isHodgeB m 3 e.target &&
  msEq e.q (e.A ++ negB) && isHodgeB m 2 e.q &&
  msEq (e.Tp ++ e.q) (e.T ++ e.B ++ negB) &&
  galAct m e.t e.target == insSort e.Tp &&
  -- T′ really is T with A exchanged for B:
  msEq (e.Tp ++ e.A) (e.T ++ e.B)

theorem exchange_edges_ok :
    BoundaryData.exchangeEdges.all edgeOK = true := by native_decide

/-! ### §8 The cyclotomic layer: exact ℤ[x]/Φ_m arithmetic and the Jacobi-sum certificates -/

/-- polynomial multiplication over ℤ (dense coefficient arrays). -/
def polMul (a b : Array Int) : Array Int := Id.run do
  if a.size == 0 || b.size == 0 then return #[]
  let mut r : Array Int := .replicate (a.size + b.size - 1) 0
  for i in [0:a.size] do
    if a[i]! != 0 then
      for j in [0:b.size] do
        r := r.set! (i + j) (r[i + j]! + a[i]! * b[j]!)
  return r

/-- exact polynomial division (monic-enough divisors); none on failure. -/
def polDivExact (num den : Array Int) : Option (Array Int) := Id.run do
  if den.size == 0 || den.back! == 0 then return none
  if num.size < den.size then
    return if num.all (· == 0) then some #[] else none
  let mut n := num
  let qlen := num.size - den.size + 1
  let mut q : Array Int := .replicate qlen 0
  for i0 in [0:qlen] do
    let i := qlen - 1 - i0
    let c := n[i + den.size - 1]!
    if c % den.back! != 0 then return none
    let qi := c / den.back!
    q := q.set! i qi
    for j in [0:den.size] do
      n := n.set! (i + j) (n[i + j]! - qi * den[j]!)
  if n.all (· == 0) then return some q else return none

def xPowSub1 (n : Nat) : Array Int := Id.run do
  let mut v : Array Int := .replicate (n + 1) 0
  v := v.set! 0 (-1)
  v := v.set! n 1
  return v

/-- Φ_k for all k ≤ n by exact division: Φ_k = (x^k − 1) / ∏_{d ∣ k, d < k} Φ_d. -/
def cyclotomicUpTo (n : Nat) : Array (Array Int) := Id.run do
  let mut phis : Array (Array Int) := .replicate (n + 1) #[]
  for k in [1:n+1] do
    let mut num := xPowSub1 k
    for d in [1:k] do
      if k % d == 0 then
        match polDivExact num phis[d]! with
        | some q => num := q
        | none => pure ()  -- cannot happen; caught by the certification theorem
    phis := phis.set! k num
  return phis

def cyclotomicPoly (n : Nat) : Array Int := (cyclotomicUpTo n)[n]!

/-- the Φ used by the certificates are certified by the defining product ∏_{d∣n} Φ_d = xⁿ−1. -/
def phiProductCheck (n : Nat) : Bool := Id.run do
  let mut prod : Array Int := #[1]
  for d in [1:n+1] do
    if n % d == 0 then
      prod := polMul prod (cyclotomicPoly d)
  return prod == xPowSub1 n

theorem cyclotomic_certified :
    (phiProductCheck 33 && phiProductCheck 39 && phiProductCheck 45 && phiProductCheck 66) &&
    ((cyclotomicPoly 33).size == 21 && (cyclotomicPoly 39).size == 25 &&
     (cyclotomicPoly 45).size == 25 && (cyclotomicPoly 66).size == 21) = true := by
  native_decide

/-- reduce a length-m exponent vector (element of ℤ[x]/(x^m − 1)) mod Φ_m. -/
def reduceModPhi (m : Nat) (v : Array Int) : Array Int := Id.run do
  let phi := cyclotomicPoly m
  let deg := phi.size - 1
  let mut w := v
  if w.size < deg then return w
  for i0 in [0:w.size - deg] do
    let i := w.size - 1 - i0
    let c := w[i]!
    if c != 0 then
      for j in [0:phi.size] do
        w := w.set! (i - deg + j) (w[i - deg + j]! - c * phi[j]!)
  return w.extract 0 deg

def mulModX (m : Nat) (a b : Array Int) : Array Int := Id.run do
  let mut r : Array Int := .replicate m 0
  for i in [0:a.size] do
    if a[i]! != 0 then
      for j in [0:b.size] do
        if b[j]! != 0 then
          r := r.set! ((i + j) % m) (r[(i + j) % m]! + a[i]! * b[j]!)
  return r

def primRoot (p : Nat) : Nat := Id.run do
  for g in [2:p] do
    let mut x := 1
    let mut seen : Array Bool := .replicate p false
    let mut cnt := 0
    for _ in [0:p-1] do
      x := x * g % p
      if !seen[x]! then
        seen := seen.set! x true
        cnt := cnt + 1
    if cnt == p - 1 then return g
  return 0

/-- S(α) = Σ_{v ∈ (F_p^×)^k, Σv ≡ 0} ∏ᵢ χ^{αᵢ}(vᵢ) as a length-m exponent vector over ℤ,
    χ(g^k) = ζ_m^k for the least primitive root g; exact integer DP over (Σv mod p, exp mod m). -/
def jacobiS (p m : Nat) (alpha : List Nat) : Array Int := Id.run do
  let g := primRoot p
  let mut ind : Array Nat := .replicate p 0
  let mut x := 1
  for k in [0:p-1] do
    ind := ind.set! x k
    x := x * g % p
  let mut dp : Array Int := .replicate (p * m) 0
  dp := dp.set! 0 1
  for ai in alpha do
    let mut ndp : Array Int := .replicate (p * m) 0
    for v in [1:p] do
      let e := (ai * ind[v]!) % m
      for s in [0:p] do
        let t := (s + v) % p
        for ee in [0:m] do
          let c := dp[s * m + ee]!
          if c != 0 then
            let idx := t * m + (ee + e) % m
            ndp := ndp.set! idx (ndp[idx]! + c)
    dp := ndp
  let mut out : Array Int := .replicate m 0
  for ee in [0:m] do
    out := out.set! ee (dp[ee]!)
  return out

def scaleDivExact (v : Array Int) (d : Int) : Option (Array Int) := Id.run do
  let mut r := v
  for i in [0:v.size] do
    if v[i]! % d != 0 then return none
    r := r.set! i (v[i]! / d)
  return some r

/-- Galois x ↦ x^t on a length-m exponent vector. -/
def galConj (m t : Nat) (v : Array Int) : Array Int := Id.run do
  let mut out : Array Int := .replicate m 0
  for e in [0:m] do
    if v[e]! != 0 then
      let idx := (e * t) % m
      out := out.set! idx (out[idx]! + v[e]!)
  return out

def oneVec (deg : Nat) : Array Int := Id.run do
  let mut v : Array Int := .replicate deg 0
  v := v.set! 0 1
  return v

/-- Theorem C engine: at (p, m, α), for every unit t compute u′ = j(t·α)/p² reduced mod Φ_m
    and check that u′ has EXACT order 6 — (u′)⁶ = 1 together with (u′)² ≠ 1 and (u′)³ ≠ 1,
    which rules out the divisors 1, 2, 3 of 6.  (The manuscript states Theorem C as
    "a primitive sixth root of unity, of exact order 6"; the earlier check (u′)⁶ = 1 ∧ u′ ≠ 1
    left order 2 and order 3 open and was therefore weaker than the printed claim.) -/
def thmC_allConjugates (p m : Nat) (alpha : List Nat) : Bool := Id.run do
  let S := jacobiS p m alpha
  match scaleDivExact S (Int.ofNat (p - 1)) with
  | none => return false
  | some J =>
    let deg := (cyclotomicPoly m).size - 1
    let one := oneVec deg
    let mut ok := true
    for t in unitsList m do
      let Jt := reduceModPhi m (galConj m t J)
      match scaleDivExact Jt (Int.ofNat (p * p)) with
      | none => ok := false
      | some U =>
        let uu := U ++ Array.replicate (m - U.size) (0 : Int)
        let U2 := mulModX m uu uu
        let U3 := mulModX m U2 uu
        let U6 := reduceModPhi m (mulModX m U3 U3)
        -- exact order 6: order ∣ 6, and neither 2 nor 3 (u′ ≠ 1 follows from (u′)³ ≠ 1)
        if !(U6 == one && U != one &&
             reduceModPhi m U2 != one && reduceModPhi m U3 != one) then ok := false
    return ok

/-- the closed form u′(t=1) = j/p² = 1 + x^k (as elements of ℤ[x]/Φ_m). -/
def closedFormCheck (p m k : Nat) (alpha : List Nat) : Bool :=
  match scaleDivExact (jacobiS p m alpha) (Int.ofNat (p - 1)) with
  | none => false
  | some J =>
    match scaleDivExact (reduceModPhi m J) (Int.ofNat (p * p)) with
    | none => false
    | some U => Id.run do
        let mut xk : Array Int := .replicate m 0
        xk := xk.set! 0 1
        xk := xk.set! k (xk[k]! + 1)
        return U == reduceModPhi m xk

/-- the TWO-VALUE DISTRIBUTION (manuscript §C: "the convention-independent assertions are
    the exact order six and the two-value distribution").  The 20 conjugates
    u′(t) = j(t·α)/p² take EXACTLY two values — ζ₆ = 1 + x^k and ζ₆⁻¹ = 1 + x^{2k mod m} —
    and both actually occur.  (Galois acts on ζ₃ = ζ_m^k through t mod 3, so no third value
    is possible; this checks it rather than assuming it.)  Counts are deliberately NOT
    asserted: the manuscript claims the two-value distribution, not a split. -/
def twoValueCheck (p m k : Nat) (alpha : List Nat) : Bool := Id.run do
  match scaleDivExact (jacobiS p m alpha) (Int.ofNat (p - 1)) with
  | none => return false
  | some J =>
    let mk (e : Nat) : Array Int := Id.run do
      let mut v : Array Int := .replicate m 0
      v := v.set! 0 1
      v := v.set! e (v[e]! + 1)
      return reduceModPhi m v
    let v1 := mk (k % m)
    let v2 := mk (2 * k % m)
    let mut ok := true
    let mut seen1 := false
    let mut seen2 := false
    for t in unitsList m do
      let Jt := reduceModPhi m (galConj m t J)
      match scaleDivExact Jt (Int.ofNat (p * p)) with
      | none => ok := false
      | some U =>
        if U == v1 then seen1 := true
        else if U == v2 then seen2 := true
        else ok := false
    return ok && seen1 && seen2 && v1 != v2

/-- THEOREM C (manuscript §8, `thm:C`): at p = 67, for da Silva's representative
    a₀ = (7,10,13,19,22,28), every one of the 20 Galois conjugates has j/p² of EXACT order 6
    ((j/p²)⁶ = 1, (j/p²)² ≠ 1, (j/p²)³ ≠ 1) — so Frobenius acts on every V(t·a₀)(2) by a
    primitive sixth root of unity, as the manuscript states, and no ℚ(ζ₃₃)-rational cycle
    class has nonzero projection.  Closed form at t = 1: j/p² = 1 + ζ₃₃¹¹ = ζ₆ (the closed
    form is checked for the base conjugate only; the order-6 statement is checked for all 20).
    Both convention-independent assertions of §C are covered: exact order 6 AND the
    two-value distribution {ζ₆, ζ₆⁻¹} = {1 + ζ₃₃¹¹, 1 + ζ₃₃²²}, both values occurring. -/
theorem thmC_certificate :
    (thmC_allConjugates 67 33 [7, 10, 13, 19, 22, 28] &&
     closedFormCheck 67 33 11 [7, 10, 13, 19, 22, 28] &&
     twoValueCheck 67 33 11 [7, 10, 13, 19, 22, 28]) = true := by native_decide

/-- B4 calibration: the DIVISORIAL second m=39 class has j = p² exactly at the split prime
    p = 79 (a Hasse–Davenport telescope instance; pins u = 1 on divisorial classes). -/
theorem jacobi_calibration_39 :
    (match scaleDivExact (jacobiS 79 39 [1, 14, 16, 22, 29, 35]) (Int.ofNat 78) with
     | none => false
     | some J => reduceModPhi 39 J == (oneVec 24).map (fun c => c * (79 * 79 : Int)))
    = true := by native_decide

/-- consistency of the level-66 lift (Thm A″ Remark (iii)): u(2w@66, 67) = 1 + ζ₃ = ζ₆ —
    the SAME Frobenius scalar as u(w@33, 67) (1 + x²² at level 66 ↦ 1 + ζ₃ ↤ 1 + x¹¹ at 33). -/
theorem jacobi_consistency_66 :
    closedFormCheck 67 66 22 (wDaSilva.map (fun x => (2 * x) % 66)) = true := by native_decide

/-- A′ Remark instance: the Frobenius characters multiply exactly, p·j(a) = j(S)·j(Q),
    at the split prime p = 181 for the m=45 row (one-prime instance of u(a) = u(S)u(Q)). -/
theorem jacobi_multiplicativity_45 :
    (match scaleDivExact (jacobiS 181 45 [1, 19, 20, 28, 30, 37]) 180,
           scaleDivExact (jacobiS 181 45 [1, 10, 19, 28, 37, 40]) 180,
           scaleDivExact (jacobiS 181 45 [5, 20, 30, 35]) 180 with
     | some jA, some jS, some jQ =>
        reduceModPhi 45 (jA.map (fun c => c * 181)) == reduceModPhi 45 (mulModX 45 jS jQ)
     | _, _, _ => false)
    = true := by native_decide

/-! ### §9 trust-base receipts (each prints `[Lean.ofReduceBool]` — the compiler axiom) -/

#print axioms census_33
#print axioms thmC_certificate
#print axioms lattice_out_verdicts

end BoundaryCore
