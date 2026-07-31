/-
  BoundaryCensus.lean — the FULL odd census, in Lean, with a PROVABLY COMPLETE enumerator.

  Closes two cut-lines of the original formalisation (lean/README.md, "Honest cut-lines"):

  * "Census enumeration completeness": `census_enumeration_complete` is a ∀-theorem — for
    EVERY level m and EVERY grade-3 Hodge character a (any entry order), the sorted
    representative of a is an element of the enumerator's output `rawFull m`.  The trust
    previously placed in six nested `for` loops is now a machine-checked statement.

  * "Scale": the census closure sweeps run at EVERY odd level 3 ≤ m ≤ 199 (99 levels — the
    manuscript's Theorem B range, with no classical-level carve-out: the anc artifacts skip
    m = 23 and m < 21 as classical) and at the three induced-risk levels 231/273/297 (the
    manuscript's beyond-the-bound probes).  `thmB_census_full` : for every listed level,
    EVERY grade-3 Hodge character is derivable in the claim calculus; `thmB_full_conditional`
    transports this to any `Inputs`-satisfying predicate.

  ENGINE (mirrors the anc engine's meet-in-the-middle, `census_scan_v2.hodge_multisets`):
  sorted triples over [1, m−1] are keyed by their grade profile on (a prefix of) the half
  units, folded into a UInt64; a sorted sextuple is grade-3-Hodge iff its two sorted halves
  carry complementary profiles, so the join over complementary buckets + the glue condition
  (max of the lower half ≤ min of the upper half) enumerates each sorted Hodge sextuple
  EXACTLY ONCE.  The UInt64 profile fold is COMPLETE by congruence (equal digit lists give
  equal keys — the only direction the completeness theorem needs); hash collisions could at
  worst add junk, which the per-level pins (representative counts against the anc receipts
  and two independent engines) exclude empirically, and which would in any case make the
  closure sweep fail visibly, never silently succeed.

  Per-level closure = the ORIGINAL checkers of BoundaryClaim (`closesBase`, via rfl-equal
  fast twins with the units list hoisted) + Galois-orbit routes to the seven beyond-machinery
  orbits already derived there, + the two induced copies 7w@231 / 9w@297 (new `.inflate`
  instances).  The reduction from an arbitrary raw class to its canonized representative
  uses the checked per-level unit-inverse table (no Bezout needed).

  Pin provenance: m ∈ {21,…,199}∖{23} — anc/data/l4/census_level_summaries.json (三-engine:
  scan_v2 + independent + brute force); m ∈ {3..19, 23} and {231, 273, 297} — an independent
  Python enumeration (profile-MITM + brute force, 2026-07-30), Lean-vs-Python two-engine
  agreement.  231/273/297 match the manuscript's probes (one induced orbit each at 231/297,
  content 7 resp. 9; the 273 remainder closes in the base tier).

  Trust base: `native_decide` for the sweeps (in the companion Sweeps files); this file's
  theorems are standard-axiom proofs about the enumerator and the reduction.
-/
import BoundaryClaim
import BoundaryValidity
import Std.Data.HashMap

namespace BoundaryCensus
open BoundaryCore BoundaryClaim

/-! ### §0 Hoisted-units Hodge test (rfl-equal to `isHodgeB`) and no-allocation digits -/

/-- `isHodgeB` with the units list hoisted out: `isHodgeBU (unitsList m) m g a = isHodgeB m g a`
    definitionally.  The fast twins below use it so that compiled sweeps build the units list
    once per level instead of once per call. -/
def isHodgeBU (U : List Nat) (m g : Nat) (a : List Nat) : Bool :=
  a.length == 2 * g &&
  a.all (fun x => 0 < x && x < m) &&
  U.all (fun t => gradeSumAt m t a == g * m)

theorem isHodgeBU_eq (m g : Nat) (a : List Nat) :
    isHodgeBU (unitsList m) m g a = isHodgeB m g a := rfl

/-- allocation-free grade digit of a triple; rfl-equal to `gradeSumAt m t [x,y,z]`. -/
def dig3 (m t x y z : Nat) : Nat := (t*x) % m + ((t*y) % m + ((t*z) % m + 0))

theorem dig3_eq (m t x y z : Nat) : dig3 m t x y z = gradeSumAt m t [x, y, z] := rfl

/-- allocation-free grade digit of a sextuple; rfl-equal to `gradeSumAt m t [a,…,f]`. -/
def dig6 (m t a b c d e f : Nat) : Nat :=
  (t*a) % m + ((t*b) % m + ((t*c) % m + ((t*d) % m + ((t*e) % m + ((t*f) % m + 0)))))

theorem dig6_eq (m t a b c d e f : Nat) :
    dig6 m t a b c d e f = gradeSumAt m t [a, b, c, d, e, f] := rfl

/-! ### §1 Sortedness (Bool) and insertion-sort correctness -/

def sortedB : List Nat → Bool
  | [] => true
  | [_] => true
  | x :: y :: t => decide (x ≤ y) && sortedB (y :: t)

theorem sortedB_cons_le {x y : Nat} {t : List Nat} (h : sortedB (x :: y :: t) = true) :
    x ≤ y ∧ sortedB (y :: t) = true := by
  simp only [sortedB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem sortedB_orderedInsert (x : Nat) :
    ∀ (l : List Nat), sortedB l = true → sortedB (orderedInsert x l) = true := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons y ys ih =>
    intro hs
    by_cases hxy : x ≤ y
    · simp only [orderedInsert, if_pos hxy]
      show (decide (x ≤ y) && sortedB (y :: ys)) = true
      rw [Bool.and_eq_true]; exact ⟨decide_eq_true hxy, hs⟩
    · simp only [orderedInsert, if_neg hxy]
      have hyx : y ≤ x := by omega
      cases ys with
      | nil =>
        show (decide (y ≤ x) && sortedB [x]) = true
        rw [Bool.and_eq_true]; exact ⟨decide_eq_true hyx, rfl⟩
      | cons z zs =>
        have hz := sortedB_cons_le hs
        have hrec := ih hz.2
        by_cases hxz : x ≤ z
        · simp only [orderedInsert, if_pos hxz] at hrec ⊢
          show (decide (y ≤ x) && sortedB (x :: z :: zs)) = true
          rw [Bool.and_eq_true]; exact ⟨decide_eq_true hyx, hrec⟩
        · simp only [orderedInsert, if_neg hxz] at hrec ⊢
          show (decide (y ≤ z) && sortedB (z :: orderedInsert x zs)) = true
          rw [Bool.and_eq_true]; exact ⟨decide_eq_true hz.1, hrec⟩

theorem sortedB_insSort : ∀ (l : List Nat), sortedB (insSort l) = true := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih => exact sortedB_orderedInsert x _ ih

/-! ### §2 Permutation transport for the Hodge predicate -/

theorem lsum_perm {a b : List Nat} (h : List.Perm a b) : lsum a = lsum b := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    show x + lsum _ = x + lsum _
    rw [ih]
  | swap x y l =>
    show y + (x + lsum l) = x + (y + lsum l)
    omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem all_of_perm {p : Nat → Bool} {a b : List Nat} (hp : List.Perm a b)
    (h : a.all p = true) : b.all p = true := by
  rw [List.all_eq_true] at h ⊢
  exact fun x hx => h x (hp.mem_iff.mpr hx)

theorem isHodgeB_of_perm {m g : Nat} {a b : List Nat} (hp : List.Perm a b)
    (h : isHodgeB m g a = true) : isHodgeB m g b = true := by
  simp only [isHodgeB, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨hlen, hent⟩, hgr⟩ := h
  refine ⟨⟨?_, all_of_perm hp hent⟩, ?_⟩
  · rw [beq_iff_eq] at hlen ⊢
    rw [← hp.length_eq]
    exact hlen
  · rw [List.all_eq_true] at hgr ⊢
    intro t ht
    have hg := hgr t ht
    rw [beq_iff_eq] at hg ⊢
    unfold gradeSumAt at hg ⊢
    rw [← lsum_perm (hp.map _)]
    exact hg

/-! ### §3 The triple enumerator and its completeness -/

def triples (m : Nat) : List (List Nat) :=
  (List.range m).flatMap fun x =>
    (List.range m).flatMap fun y =>
      (List.range m).filterMap fun z =>
        if decide (1 ≤ x) && decide (x ≤ y) && decide (y ≤ z) then some [x, y, z] else none

theorem mem_triples {m x y z : Nat} (h1 : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hzm : z < m) :
    [x, y, z] ∈ triples m := by
  unfold triples
  rw [List.mem_flatMap]
  refine ⟨x, List.mem_range.mpr (by omega), ?_⟩
  rw [List.mem_flatMap]
  refine ⟨y, List.mem_range.mpr (by omega), ?_⟩
  rw [List.mem_filterMap]
  refine ⟨z, List.mem_range.mpr hzm, ?_⟩
  rw [decide_eq_true h1, decide_eq_true hxy, decide_eq_true hyz]
  rfl

/-! ### §4 Profile keys, cached digits, buckets, the join -/

/-- the profile units: a prefix of the half units (each extra unit sharpens the key;
    twenty is a speed/pruning compromise, any prefix is sound and complete). -/
def keyUnits (m : Nat) : List Nat := (halfUnits m).take 20

def digitsOf (m : Nat) (K : List Nat) : List Nat → List Nat
  | [x, y, z] => K.map fun t => dig3 m t x y z
  | _ => []

/-- fold a digit list into a UInt64 key (odd multiplier ⟹ well-mixed; completeness only
    ever uses CONGRUENCE: equal digit lists give equal keys). -/
def foldKey : List Nat → UInt64 :=
  List.foldr (fun d acc => acc * 1099511628211 + UInt64.ofNat d) 0

def compKeyOf (m : Nat) (ds : List Nat) : UInt64 :=
  foldKey (ds.map fun d => 3 * m - d)

/-- triples paired with their cached digit lists (the key units hoisted out of the map). -/
def tripD (m : Nat) : List (List Nat × List Nat) :=
  let K := keyUnits m
  (triples m).map fun h => (h, digitsOf m K h)

def bstep (mp : Std.HashMap UInt64 (List (List Nat))) (hd : List Nat × List Nat) :
    Std.HashMap UInt64 (List (List Nat)) :=
  mp.insert (foldKey hd.2) (hd.1 :: mp.getD (foldKey hd.2) [])

def bucketsOf (Td : List (List Nat × List Nat)) : Std.HashMap UInt64 (List (List Nat)) :=
  Td.foldl bstep ∅

theorem bstep_getD_mono {mp : Std.HashMap UInt64 (List (List Nat))} {k : UInt64}
    {A : List Nat} (hd : List Nat × List Nat) (h : A ∈ mp.getD k []) :
    A ∈ (bstep mp hd).getD k [] := by
  unfold bstep
  by_cases he : foldKey hd.2 = k
  · subst he
    rw [Std.HashMap.getD_insert_self]
    exact List.mem_cons_of_mem _ h
  · rw [Std.HashMap.getD_insert]
    simp only [beq_iff_eq, if_neg he]
    exact h

theorem foldl_bstep_getD_mono (l : List (List Nat × List Nat))
    {mp : Std.HashMap UInt64 (List (List Nat))} {k : UInt64} {A : List Nat}
    (h : A ∈ mp.getD k []) : A ∈ (l.foldl bstep mp).getD k [] := by
  induction l generalizing mp with
  | nil => exact h
  | cons hd t ih => exact ih (bstep_getD_mono hd h)

theorem mem_foldl_bstep (l : List (List Nat × List Nat))
    {mp : Std.HashMap UInt64 (List (List Nat))} {hd : List Nat × List Nat}
    (hmem : hd ∈ l) : hd.1 ∈ (l.foldl bstep mp).getD (foldKey hd.2) [] := by
  induction l generalizing mp with
  | nil => cases hmem
  | cons h0 t ih =>
    rcases List.mem_cons.mp hmem with rfl | ht
    · rw [List.foldl_cons]
      apply foldl_bstep_getD_mono
      unfold bstep
      rw [Std.HashMap.getD_insert_self]
      exact List.mem_cons_self ..
    · exact ih ht

def glueOK : List Nat → List Nat → Bool
  | [_, _, c], [d, _, _] => decide (c ≤ d)
  | _, _ => false

/-- exact half-unit Hodge verify of a glued pair, allocation-free on the 3+3 shape.
    For halves from `triples`, entries and length are automatic, and constancy on the half
    units forces constancy on all units (S_{m−t} = 6m − S_t on nonzero entries) — so this
    is exactly "the glued sextuple is grade-3 Hodge", and it kills the key-prefix junk
    (the profile key certifies only `keyUnits`, a PREFIX of the half units). -/
def halfHodge (m : Nat) (H : List Nat) : List Nat → List Nat → Bool
  | [x, y, z], [u, v, w] => H.all fun t => dig6 m t x y z u v w == 3 * m
  | _, _ => false

def rawJoin (Td : List (List Nat × List Nat)) (m : Nat) (H : List Nat) : List (List Nat) :=
  let bk := bucketsOf Td
  Td.flatMap fun Bd =>
    (bk.getD (compKeyOf m Bd.2) []).filterMap fun A =>
      if glueOK A Bd.1 && halfHodge m H A Bd.1 then some (A ++ Bd.1) else none

/-- the census enumerator: every sorted grade-3 Hodge sextuple of level m, each exactly once
    (soundness is pinned by the per-level representative counts; completeness is the theorem
    `rawFull_complete` below). -/
def rawFull (m : Nat) : List (List Nat) := rawJoin (tripD m) m (halfUnits m)

/-! ### §5 Completeness of the enumerator -/

theorem exists_six {s : List Nat} (h : s.length = 6) :
    ∃ a b c d e f, s = [a, b, c, d, e, f] := by
  match s, h with
  | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩

theorem sortedB_six {a b c d e f : Nat} (h : sortedB [a, b, c, d, e, f] = true) :
    a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e ∧ e ≤ f := by
  simp only [sortedB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

private theorem foldr_add_shift (l : List Nat) (c : Nat) :
    l.foldr (· + ·) c = l.foldr (· + ·) 0 + c := by
  induction l with
  | nil => simp
  | cons x t ih =>
    show x + t.foldr (· + ·) c = x + t.foldr (· + ·) 0 + c
    rw [ih]
    omega

theorem gradeSumAt_append (m t : Nat) (A B : List Nat) :
    gradeSumAt m t (A ++ B) = gradeSumAt m t A + gradeSumAt m t B := by
  unfold gradeSumAt lsum
  rw [List.map_append, List.foldr_append, foldr_add_shift]

/-- membership of the key units in the full units list. -/
theorem keyUnits_subset_units {m t : Nat} (h : t ∈ keyUnits m) : t ∈ unitsList m := by
  unfold keyUnits at h
  have h2 : t ∈ halfUnits m := List.take_subset _ _ h
  unfold halfUnits at h2
  exact (List.mem_filter.mp h2).1

/-- COMPLETENESS of the enumerator: every SORTED grade-3 Hodge sextuple is in `rawFull m`. -/
theorem rawFull_complete {m : Nat} {s : List Nat}
    (hsort : sortedB s = true) (hh : isHodgeB m 3 s = true) : s ∈ rawFull m := by
  have hh' := hh
  simp only [isHodgeB, Bool.and_eq_true] at hh'
  obtain ⟨⟨hlen, hent⟩, hgr⟩ := hh'
  rw [beq_iff_eq] at hlen
  obtain ⟨a, b, c, d, e, f, rfl⟩ := exists_six hlen
  obtain ⟨hab, hbc, hcd, hde, hef⟩ := sortedB_six hsort
  -- entry bounds
  have hbnd : ∀ x ∈ [a, b, c, d, e, f], 0 < x ∧ x < m := by
    intro x hx
    have := List.all_eq_true.mp hent x hx
    rw [Bool.and_eq_true] at this
    exact ⟨of_decide_eq_true this.1, of_decide_eq_true this.2⟩
  have ha1 : 0 < a := (hbnd a (by simp)).1
  have hd1 : 0 < d := (hbnd d (by simp)).1
  have hfm : f < m := (hbnd f (by simp)).2
  -- the two halves are enumerated triples
  have hA : [a, b, c] ∈ triples m := mem_triples ha1 hab hbc (by omega)
  have hB : [d, e, f] ∈ triples m := mem_triples hd1 hde hef hfm
  -- half grades are complementary on the key units
  have hgrade : ∀ t ∈ keyUnits m, gradeSumAt m t [a, b, c, d, e, f] = 3 * m := by
    intro t ht
    have := List.all_eq_true.mp hgr t (keyUnits_subset_units ht)
    rw [beq_iff_eq] at this
    exact this
  have hdig : digitsOf m (keyUnits m) [a, b, c] =
      (digitsOf m (keyUnits m) [d, e, f]).map (fun dd => 3 * m - dd) := by
    unfold digitsOf
    rw [List.map_map]
    apply List.map_congr_left
    intro t ht
    have hsplit : gradeSumAt m t [a, b, c] + gradeSumAt m t [d, e, f] = 3 * m := by
      have := hgrade t ht
      rw [show ([a, b, c, d, e, f] : List Nat) = [a, b, c] ++ [d, e, f] from rfl,
        gradeSumAt_append] at this
      exact this
    show dig3 m t a b c = 3 * m - dig3 m t d e f
    rw [dig3_eq, dig3_eq]
    omega
  have hkey : foldKey (digitsOf m (keyUnits m) [a, b, c]) =
      compKeyOf m (digitsOf m (keyUnits m) [d, e, f]) := by
    unfold compKeyOf
    rw [hdig]
  -- assemble the join membership
  have hATd : ([a, b, c], digitsOf m (keyUnits m) [a, b, c]) ∈ tripD m := by
    simp only [tripD]
    exact List.mem_map.mpr ⟨[a, b, c], hA, rfl⟩
  have hBTd : ([d, e, f], digitsOf m (keyUnits m) [d, e, f]) ∈ tripD m := by
    simp only [tripD]
    exact List.mem_map.mpr ⟨[d, e, f], hB, rfl⟩
  have hbk : [a, b, c] ∈ (bucketsOf (tripD m)).getD
      (foldKey (digitsOf m (keyUnits m) [a, b, c])) [] :=
    mem_foldl_bstep _ hATd
  show [a, b, c, d, e, f] ∈ rawJoin (tripD m) m (halfUnits m)
  simp only [rawJoin]
  rw [List.mem_flatMap]
  refine ⟨([d, e, f], digitsOf m (keyUnits m) [d, e, f]), hBTd, ?_⟩
  rw [List.mem_filterMap]
  refine ⟨[a, b, c], ?_, ?_⟩
  · rw [← hkey]
    exact hbk
  · have hg : glueOK [a, b, c] [d, e, f] = true := by
      show decide (c ≤ d) = true
      exact decide_eq_true hcd
    have hhh : halfHodge m (halfUnits m) [a, b, c] [d, e, f] = true := by
      show ((halfUnits m).all fun t => dig6 m t a b c d e f == 3 * m) = true
      rw [List.all_eq_true]
      intro t ht
      have htu : t ∈ unitsList m := (List.mem_filter.mp ht).1
      have hgt := List.all_eq_true.mp hgr t htu
      rw [beq_iff_eq] at hgt
      rw [beq_iff_eq, dig6_eq]
      exact hgt
    rw [hg, hhh]
    rfl

/-- ENUMERATION COMPLETENESS, headline form: every grade-3 Hodge character of X⁴_m, in any
    entry order, has its sorted representative in the census enumerator's output — at every
    level m, with no side conditions.  (This is the ∀-theorem the original formalisation's
    README listed as a cut-line.) -/
theorem census_enumeration_complete (m : Nat) :
    ∀ a, isHodgeB m 3 a = true → insSort a ∈ rawFull m := fun a ha =>
  rawFull_complete (sortedB_insSort a) (isHodgeB_of_perm (insSort_perm a).symm ha)

/-! ### §6 Canonization (quick-skip minimum) and the representative list -/

def minMap6 (m t : Nat) : List Nat → Nat
  | [a, b, c, d, e, f] =>
      min ((t*a) % m) (min ((t*b) % m) (min ((t*c) % m)
        (min ((t*d) % m) (min ((t*e) % m) ((t*f) % m)))))
  | _ => 0

def canonStep (m : Nat) (a : List Nat) (best : List Nat) (t : Nat) : List Nat :=
  if best.getD 0 0 < minMap6 m t a then best
  else if listLt (insSort (a.map fun x => (t * x) % m)) best then
    insSort (a.map fun x => (t * x) % m)
  else best

def canonRepU (U : List Nat) (m : Nat) (a : List Nat) : List Nat :=
  U.foldl (canonStep m a) (insSort a)

theorem canonStep_cases (m : Nat) (a best : List Nat) (t : Nat) :
    canonStep m a best t = best ∨
    canonStep m a best t = insSort (a.map fun x => (t * x) % m) := by
  unfold canonStep
  by_cases h1 : best.getD 0 0 < minMap6 m t a
  · left; rw [if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : listLt (insSort (a.map fun x => (t * x) % m)) best = true
    · right; rw [if_pos h2]
    · left; rw [if_neg h2]

theorem canonRepU_cases (U : List Nat) (m : Nat) (a : List Nat) :
    canonRepU U m a = insSort a ∨
    ∃ t ∈ U, canonRepU U m a = insSort (a.map fun x => (t * x) % m) := by
  unfold canonRepU
  generalize insSort a = init
  induction U generalizing init with
  | nil => left; rfl
  | cons t ts ih =>
    rw [List.foldl_cons]
    rcases canonStep_cases m a init t with he | he <;> rw [he]
    · rcases ih init with h | ⟨u, hu, h⟩
      · left; exact h
      · right; exact ⟨u, List.mem_cons_of_mem _ hu, h⟩
    · rcases ih (insSort (a.map fun x => (t * x) % m)) with h | ⟨u, hu, h⟩
      · right; exact ⟨t, List.mem_cons_self .., h⟩
      · right; exact ⟨u, List.mem_cons_of_mem _ hu, h⟩

instance : Hashable (List Nat) := ⟨fun l => l.foldl (fun h x => mixHash h (hash x)) 7⟩

instance : LawfulHashable (List Nat) := ⟨by intro a b h; rw [eq_of_beq h]⟩

def rstep (U : List Nat) (m : Nat)
    (st : Std.HashMap (List Nat) Unit × List (List Nat)) (s : List Nat) :
    Std.HashMap (List Nat) Unit × List (List Nat) :=
  if st.1.contains (canonRepU U m s) then st
  else (st.1.insert (canonRepU U m s) (), canonRepU U m s :: st.2)

/-- the canonized representative list of the level (dedup via a seen-set). -/
def repsFull (m : Nat) : List (List Nat) :=
  ((rawFull m).foldl (rstep (unitsList m) m) (∅, [])).2

theorem rstep_snd_mono {U : List Nat} {m : Nat}
    {st : Std.HashMap (List Nat) Unit × List (List Nat)} {x : List Nat} (s : List Nat)
    (h : x ∈ st.2) : x ∈ (rstep U m st s).2 := by
  unfold rstep
  split
  · exact h
  · exact List.mem_cons_of_mem _ h

theorem foldl_rstep_snd_mono (l : List (List Nat)) {U : List Nat} {m : Nat}
    {st : Std.HashMap (List Nat) Unit × List (List Nat)} {x : List Nat}
    (h : x ∈ st.2) : x ∈ (l.foldl (rstep U m) st).2 := by
  induction l generalizing st with
  | nil => exact h
  | cons s t ih => exact ih (rstep_snd_mono s h)

theorem mem_foldl_rstep (l : List (List Nat)) {U : List Nat} {m : Nat}
    {st : Std.HashMap (List Nat) Unit × List (List Nat)}
    (hinv : ∀ k, st.1.contains k = true → k ∈ st.2) {s : List Nat} (hs : s ∈ l) :
    canonRepU U m s ∈ (l.foldl (rstep U m) st).2 := by
  induction l generalizing st with
  | nil => cases hs
  | cons s0 t ih =>
    have hinv' : ∀ k, (rstep U m st s0).1.contains k = true → k ∈ (rstep U m st s0).2 := by
      intro k hk
      unfold rstep at hk ⊢
      by_cases hc : st.1.contains (canonRepU U m s0) = true
      · simp only [hc, reduceIte] at hk ⊢
        exact hinv k hk
      · simp only [hc, Bool.false_eq_true, if_false] at hk ⊢
        rw [Std.HashMap.contains_insert] at hk
        rw [Bool.or_eq_true] at hk
        rcases hk with hk | hk
        · rw [eq_of_beq hk]
          exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hinv k hk)
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hs with rfl | ht
    · have hin : canonRepU U m s ∈ (rstep U m st s).2 := by
        unfold rstep
        split
        · next hcond => exact hinv _ hcond
        · exact List.mem_cons_self ..
      exact foldl_rstep_snd_mono t hin
    · exact ih hinv' ht

theorem mem_repsFull {m : Nat} {s : List Nat} (hs : s ∈ rawFull m) :
    canonRepU (unitsList m) m s ∈ repsFull m := by
  unfold repsFull
  exact mem_foldl_rstep _
    (fun k hk => by rw [Std.HashMap.contains_empty] at hk; cases hk) hs

/-! ### §7 The unit-inverse reduction (checked table, no Bezout) -/

theorem mem_unitsList {m x : Nat} :
    x ∈ unitsList m ↔ 1 ≤ x ∧ x < m ∧ Nat.gcd x m = 1 := by
  unfold unitsList
  rw [List.mem_filter, List.range_eq_range', List.drop_range', List.mem_range'_1]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rw [beq_iff_eq] at h3
    exact ⟨by omega, by omega, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [beq_iff_eq]
    exact h3

theorem inv_cancel {m t u x : Nat} (hm : 0 < m) (hx : x < m) (h : (t * u) % m = 1) :
    (u * ((t * x) % m)) % m = x := by
  have hmm : (t * x) % m % m = (t * x) % m := Nat.mod_eq_of_lt (Nat.mod_lt _ hm)
  rw [Nat.mul_mod, hmm, ← Nat.mul_mod]
  rw [← Nat.mul_assoc, Nat.mul_comm u t]
  rw [Nat.mul_mod (t * u) x m, h, Nat.one_mul, Nat.mod_eq_of_lt (Nat.mod_lt _ hm),
    Nat.mod_eq_of_lt hx]

/-! ### §8 rfl-equal fast twins of the closure checkers (hoisted units) -/

def closesDecompBF (m : Nat) (a : List Nat) : Bool :=
  let U := unitsList m
  (splitsK a 2).any fun (δ, q) =>
    isDClassB m δ && isHodgeBU U m 1 δ && isHodgeBU U m 2 q && msEq a (q ++ δ)

def closesQuasiBF (m : Nat) (a : List Nat) : Bool :=
  let U := unitsList m
  isHodgeBU U m 3 a &&
  (((List.range ((m + 1) / 2)).drop 1).any fun k =>
    let δ := [k, m - k]
    isDClassB m δ && (δ.length % 2 == 0) &&
    ((splitsK (a ++ δ) 4).any fun (c, d) =>
      isHodgeBU U m 2 c && isHodgeBU U m 2 d && msEq (c ++ d) (a ++ δ)))

def closesStdBF (m : Nat) (a : List Nat) : Bool :=
  let U := unitsList m
  (stdSextuples m).any fun σ =>
    isStdStrictB m σ &&
    (U.any fun t => Nat.gcd t m == 1 && msEq (σ.map fun x => (t * x) % m) a)

def closesStarBF (m : Nat) (a : List Nat) : Bool :=
  let U := unitsList m
  (m % 2 == 1) && isHodgeBU U m 3 a &&
  ((splitsK a 3).any fun (b, c) =>
    b.length == 3 && c.length == 3 &&
    lsum b % m == 0 && lsum c % m == 0 && msEq a (b ++ c))

def closesBaseFast (m : Nat) (a : List Nat) : Bool :=
  closesDecompBF m a || closesQuasiBF m a || closesStdBF m a || closesStarBF m a

theorem closesBaseFast_eq (m : Nat) (a : List Nat) : closesBaseFast m a = closesBase m a := rfl

/-! ### §8b The level-transport route (scaled classes close on their primitive level)

The base checkers mirror the CITED closure rules, and Aoki's Theorem 2-1 carries the
hypothesis gcd(x, m/p) = 1 — so a standard sextuple σ_{5,x} with gcd(x, m/5) = g > 1
(every entry divisible by g) is NOT covered by `closesStdB` at its own level.  It is the
g-inflation of σ_{5,x/g} at level m/g, and the manuscript closes it by "level transport"
(the inflation lemma).  `closesLiftB` implements exactly that: divide out a common divisor
e ∣ m of all entries and close the divided class in the base tier of level m/e; soundness
is one `.inflate` application. -/

def closesLiftB (m : Nat) (a : List Nat) : Bool :=
  ((List.range m).drop 2).any fun e =>
    (m % e == 0) &&
    (a.all fun x => x % e == 0) &&
    (a.all fun x => x % m != 0) &&
    isHodgeBU (unitsList (m / e)) (m / e) 3 (a.map (· / e)) &&
    closesBaseFast (m / e) (a.map (· / e))

theorem mem_range_drop2 {m e : Nat} (h : e ∈ (List.range m).drop 2) : 2 ≤ e ∧ e < m := by
  rw [List.range_eq_range', List.drop_range', List.mem_range'_1] at h
  omega

theorem closesLiftB_sound {H : Nat → List Nat → Prop} {m : Nat} {a : List Nat}
    (h : closesLiftB m a = true) : ClaimFrom H m a := by
  obtain ⟨e, he, hb⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨hme, hdiv⟩, hnz⟩, hHsub⟩, hcb⟩ := hb
  have he2 := (mem_range_drop2 he).1
  have hdvd : e ∣ m := Nat.dvd_of_mod_eq_zero (by rwa [beq_iff_eq] at hme)
  have hmap : (a.map (· / e)).map (e * ·) = a := by
    rw [List.map_map]
    have hpt : ∀ x ∈ a, ((e * ·) ∘ (· / e)) x = x := by
      intro x hx
      have := List.all_eq_true.mp hdiv x hx
      rw [beq_iff_eq] at this
      exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero this)
    rw [List.map_congr_left hpt]
    simp
  have hem : e * (m / e) = m := Nat.mul_div_cancel' hdvd
  have hsub : ClaimFrom H (m / e) (a.map (· / e)) := by
    rw [closesBaseFast_eq] at hcb
    exact closesBase_sound hcb
  have hnz' : (((a.map (· / e)).map (e * ·)).all fun x => x % (e * (m / e)) != 0) = true := by
    rw [hmap, hem]
    exact hnz
  have hinf := ClaimFrom.inflate (H := H) e (by omega) (by decide) (g := 3)
    (by rw [← isHodgeBU_eq]; exact hHsub) hnz' hsub
  rw [hmap, hem] at hinf
  exact hinf

/-! ### §9 The per-level check and the generic level theorem -/

/-- one level's full check: 1 is a unit (m ≥ 2), the representative count matches the pin,
    every representative closes (base tier, a Galois-orbit route to a listed base, or the
    level-transport route), and every unit has an inverse in the units list (the checked
    table the reduction uses). -/
def levelFull (m n : Nat) (bases : List (List Nat)) : Bool :=
  let U := unitsList m
  let R := repsFull m
  U.contains 1 &&
  ((R.length == n) &&
  ((R.all fun r =>
      closesBaseFast m r || (bases.any fun b => closesOrbitB m b r) || closesLiftB m r) &&
  (U.all fun t => U.any fun u => (t * u) % m == 1)))

theorem levelFull_parts {m n : Nat} {bases : List (List Nat)}
    (h : levelFull m n bases = true) :
    (unitsList m).contains 1 = true ∧
    ((repsFull m).all fun r =>
        closesBaseFast m r || (bases.any fun b => closesOrbitB m b r) ||
          closesLiftB m r) = true ∧
    ((unitsList m).all fun t => (unitsList m).any fun u => (t * u) % m == 1) = true := by
  unfold levelFull at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1, h.2.2.1, h.2.2.2⟩

/-- THE GENERIC LEVEL THEOREM: a passing `levelFull` check plus claims for the listed bases
    give Theorem B's census statement at the level — EVERY grade-3 Hodge character (any
    entry order, over the abstract predicate) is derivable in the claim calculus. -/
theorem thmB_level {H : Nat → List Nat → Prop} {m n : Nat} {bases : List (List Nat)}
    (hchk : levelFull m n bases = true)
    (hb : ∀ b ∈ bases, ClaimFrom H m b) :
    ∀ a, isHodgeB m 3 a = true → ClaimFrom H m a := by
  obtain ⟨h1, hsweep, hinvtab⟩ := levelFull_parts hchk
  intro a ha
  -- the sorted representative is enumerated
  have hhs : isHodgeB m 3 (insSort a) = true := isHodgeB_of_perm (insSort_perm a).symm ha
  have hraw : insSort a ∈ rawFull m := rawFull_complete (sortedB_insSort a) hhs
  have hrep := mem_repsFull hraw
  -- its canonized representative closes
  have hclr : ClaimFrom H m (canonRepU (unitsList m) m (insSort a)) := by
    have hcl := List.all_eq_true.mp hsweep _ hrep
    rw [Bool.or_eq_true, Bool.or_eq_true] at hcl
    rcases hcl with (hcb | horb) | hlift
    · rw [closesBaseFast_eq] at hcb
      exact closesBase_sound hcb
    · obtain ⟨b, hbmem, hob⟩ := List.any_eq_true.mp horb
      exact closesOrbitB_sound (hb b hbmem) hob
    · exact closesLiftB_sound hlift
  -- transport back to a along the Galois inverse
  rcases canonRepU_cases (unitsList m) m (insSort a) with hcc | ⟨t, htU, hcc⟩
  · rw [hcc] at hclr
    exact .perm ((insSort_perm _).trans (insSort_perm a)) hclr
  · rw [hcc] at hclr
    have hstep1 : ClaimFrom H m ((insSort a).map fun x => (t * x) % m) :=
      .perm (insSort_perm _) hclr
    obtain ⟨u, huU, huv⟩ := List.any_eq_true.mp (List.all_eq_true.mp hinvtab t htU)
    have huv' : (t * u) % m = 1 := by rwa [beq_iff_eq] at huv
    obtain ⟨hu1, hum, hugcd⟩ := mem_unitsList.mp huU
    have hm : 0 < m := by omega
    have hstep2 := ClaimFrom.galois (H := H) u (by rw [beq_iff_eq]; exact hugcd) hstep1
    rw [List.map_map] at hstep2
    have hid : ((insSort a).map ((fun x => (u * x) % m) ∘ fun x => (t * x) % m))
        = insSort a := by
      have hpt : ∀ x ∈ insSort a, ((fun x => (u * x) % m) ∘ fun x => (t * x) % m) x = x := by
        intro x hx
        have hent := hhs
        simp only [isHodgeB, Bool.and_eq_true] at hent
        have hxb := List.all_eq_true.mp hent.1.2 x hx
        rw [Bool.and_eq_true] at hxb
        have hx2 : x < m := of_decide_eq_true hxb.2
        exact inv_cancel hm hx2 huv'
      rw [List.map_congr_left hpt]
      simp
    rw [hid] at hstep2
    exact .perm (insSort_perm a) hstep2

/-! ### §10 The level tables (pins) and per-level base routes -/

/- Pins: m ∈ {21..199}∖{23} from anc/data/l4/census_level_summaries.json (itself certified by
   THREE engines: census_scan_v2, census_independent, census_bruteforce); m ∈ {3..19, 23} and
   {231, 273, 297} from an independent Python enumeration (2026-07-30; brute force below 21
   and at 23, profile-MITM at the three extra levels), giving Lean-vs-Python two-engine
   agreement at those levels.  m = 23 is EXCLUDED from the anc artifacts as classical
   (da Silva covers primes); the Lean census carries it like any other level. -/

/-- pin batch 1 (74 levels: odd 3..149). -/
def censusTable1 : List (Nat × Nat) :=
  [(3, 1), (5, 2), (7, 4), (9, 10), (11, 7), (13, 10), (15, 40), (17, 15), (19, 19), (21, 64),
   (23, 26), (25, 39), (27, 68), (29, 40), (31, 46), (33, 104), (35, 92), (37, 64), (39, 140),
   (41, 77), (43, 85), (45, 245), (47, 100), (49, 128), (51, 217), (53, 126), (55, 197),
   (57, 265), (59, 155), (61, 166), (63, 407), (65, 268), (67, 199), (69, 372), (71, 222),
   (73, 235), (75, 561), (77, 346), (79, 274), (81, 504), (83, 301), (85, 437), (87, 570),
   (89, 345), (91, 473), (93, 646), (95, 539), (97, 409), (99, 825), (101, 442), (103, 460),
   (105, 1286), (107, 495), (109, 514), (111, 900), (113, 551), (115, 772), (117, 1117),
   (119, 776), (121, 694), (123, 1091), (125, 866), (127, 694), (129, 1195), (131, 737),
   (133, 960), (135, 1767), (137, 805), (139, 829), (141, 1414), (143, 1062), (145, 1204),
   (147, 1816), (149, 950)]

/-- pin batch 2 (15 levels: odd 151..179). -/
def censusTable2 : List (Nat × Nat) :=
  [(151, 976), (153, 1816), (155, 1370), (157, 1054), (159, 1780), (161, 1379), (163, 1135),
   (165, 2743), (167, 1190), (169, 1322), (171, 2236), (173, 1276), (175, 2015), (177, 2187),
   (179, 1365)]

/-- pin batch 3 (10 levels: odd 181..199). -/
def censusTable3 : List (Nat × Nat) :=
  [(181, 1396), (183, 2334), (185, 1930), (187, 1761), (189, 3100), (191, 1552), (193, 1585),
   (195, 3715), (197, 1650), (199, 1684)]

/-- pin batch 4 (the induced-risk levels 231 = 7·33 and 273 = 3·7·13). -/
def censusTable4 : List (Nat × Nat) := [(231, 4838), (273, 6578)]

/-- pin batch 5 (the induced-risk level 297 = 9·33). -/
def censusTable5 : List (Nat × Nat) := [(297, 6899)]

def censusTable : List (Nat × Nat) :=
  censusTable1 ++ (censusTable2 ++ (censusTable3 ++ (censusTable4 ++ censusTable5)))

/-- all census levels (odd 3..199 and 231/273/297). -/
def censusLevels : List Nat := censusTable.map (·.1)

/-- the Galois-orbit base routes per level: the seven beyond-machinery orbits of the
    manuscript (already derived in BoundaryClaim) plus the two induced copies at the
    beyond-the-bound levels (7w@231, 9w@297 — `claim_w231`/`claim_w297` below).  273 needs
    no route: its non-decomposable remainder closes in the base tier (Theorem A), exactly
    as the manuscript's probe states. -/
def levelBases (m : Nat) : List (List Nat) :=
  if m == 33 then [wDaSilva]
  else if m == 45 then [a45]
  else if m == 99 then [wDaSilva.map (3 * ·)]
  else if m == 105 then [a105a, a105b]
  else if m == 135 then [a45.map (3 * ·)]
  else if m == 165 then [wDaSilva.map (5 * ·)]
  else if m == 231 then [wDaSilva.map (7 * ·)]
  else if m == 297 then [wDaSilva.map (9 * ·)]
  else []

section InducedCopies
variable {H : Nat → List Nat → Prop}

/-- the induced copy at 231 = 7·33 (content 7): inflation of the m=33 witness. -/
theorem claim_w231 : ClaimFrom H 231 (wDaSilva.map (7 * ·)) :=
  show ClaimFrom H (7 * 33) (wDaSilva.map (7 * ·)) from
    .inflate 7 (by decide) (by decide) (g := 3) (by native_decide) (by native_decide) claim_w33

/-- the induced copy at 297 = 9·33 (content 9): inflation of the m=33 witness. -/
theorem claim_w297 : ClaimFrom H 297 (wDaSilva.map (9 * ·)) :=
  show ClaimFrom H (9 * 33) (wDaSilva.map (9 * ·)) from
    .inflate 9 (by decide) (by decide) (g := 3) (by native_decide) (by native_decide) claim_w33

/-- every listed base route is derivable in the calculus. -/
theorem basesClaimed (m : Nat) : ∀ b ∈ levelBases m, ClaimFrom H m b := by
  intro b hb
  unfold levelBases at hb
  split at hb
  · next h => rw [eq_of_beq h]; rw [List.mem_singleton] at hb; subst hb
              exact claim_w33
  · split at hb
    · next h => rw [eq_of_beq h]; rw [List.mem_singleton] at hb; subst hb
                exact claim_a45
    · split at hb
      · next h => rw [eq_of_beq h]; rw [List.mem_singleton] at hb; subst hb
                  exact claim_w99
      · split at hb
        · next h =>
            rw [eq_of_beq h]
            rcases List.mem_cons.mp hb with rfl | hb2
            · exact claim_a105a
            · rw [List.mem_singleton] at hb2; subst hb2; exact claim_a105b
        · split at hb
          · next h => rw [eq_of_beq h]; rw [List.mem_singleton] at hb; subst hb
                      exact claim_a135
          · split at hb
            · next h => rw [eq_of_beq h]; rw [List.mem_singleton] at hb
                        subst hb; exact claim_w165
            · split at hb
              · next h => rw [eq_of_beq h]; rw [List.mem_singleton] at hb
                          subst hb; exact claim_w231
              · split at hb
                · next h => rw [eq_of_beq h]; rw [List.mem_singleton] at hb
                            subst hb; exact claim_w297
                · cases hb

end InducedCopies

end BoundaryCensus
