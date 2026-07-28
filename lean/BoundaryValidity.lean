/-
  BoundaryValidity.lean — the validity receipts of the claim calculus.

  The faithfulness audit of `BoundaryClaim` (2026-07-28) found that two rules admitted
  objects no cited theorem speaks about:

    * `pairsD` (Aoki Thm 1-1) accepted δ = [] — but 𝔇^r_m has r + 2 ≥ 2 entries, there is
      no `V([])` and no `X^{-2}_m`; the same leak reached `cancel` through `isDClassB`;
    * `inflate` / `descend` (manuscript `lem:infl` / `lem:descent`) accepted g = 0, a transport
      between varieties that do not exist.

  Both rules are now guarded — `2 ≤ l.length` inside `isDClassB`, `1 ≤ g` in `pairsD`,
  `inflate`, `descend`.  This file proves the guards actually bite, and does so
  calculus-wide rather than rule-by-rule:

    * `isDClassB_nil`       — the empty list is never a 𝔇-class, at any level;
    * `pairsD_nil_blocked`  — hence Aoki 1-1 cannot introduce it (the audit's regression:
                              `Claim 3 []` is not derivable via `pairsD`);
    * `Claim.length_ge_two` — EVERY absolutely derivable class has at least 2 entries, so
                              it is a Hodge character of some grade g ≥ 1 living on an
                              honest X_m^{2g−2};
    * `Claim.nil_not_derivable` — in particular `Claim m []` is false for every m.

  Lean core only: no mathlib, no `native_decide`.  Trust base = the standard axioms.
-/
import BoundaryClaim

namespace BoundaryClaim
open BoundaryCore

/-! ### §1 The Bool guards, read back as bounds -/

/-- the length fence of `isDClassB`: the empty list is not a 𝔇-class at any level. -/
theorem isDClassB_nil (m : Nat) : isDClassB m [] = false := rfl

/-- every 𝔇-class has at least the two entries of one vanishing pair. -/
theorem isDClassB_length {m : Nat} {l : List Nat} (h : isDClassB m l = true) :
    2 ≤ l.length := by
  simp only [isDClassB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- a Hodge character of grade g has exactly 2g entries (§1 of the manuscript). -/
theorem isHodgeB_length {m g : Nat} {a : List Nat} (h : isHodgeB m g a = true) :
    a.length = 2 * g := by
  simp only [isHodgeB, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

/-- an Aoki standard character σ_{p,x} has p + 1 ≥ 4 entries. -/
theorem isStdStrictB_length {m : Nat} {σ : List Nat} (h : isStdStrictB m σ = true) :
    4 ≤ σ.length := by
  unfold isStdStrictB at h
  obtain ⟨p, -, hp⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at hp
  obtain ⟨⟨⟨⟨hp3, -⟩, -⟩, -⟩, hx⟩ := hp
  obtain ⟨x, -, hxb⟩ := List.any_eq_true.mp hx
  simp only [Bool.and_eq_true] at hxb
  have h3 : 3 ≤ p := of_decide_eq_true hp3
  have hlen := (msEq_perm hxb.2).length_eq
  simp only [List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil] at hlen
  omega

/-! ### §2 The audit's regression: Aoki 1-1 cannot introduce the empty class -/

/-- REGRESSION (audit finding 1).  No instance of the `pairsD` rule produces `[]`: its two
    Bool side conditions plus `1 ≤ g` are jointly unsatisfiable there, at every level and
    every grade.  Before the fix, `g = 0` and `δ = []` satisfied all of them. -/
theorem pairsD_nil_blocked (m g : Nat) :
    ¬ (1 ≤ g ∧ isDClassB m [] = true ∧ isHodgeB m g [] = true) := by
  rintro ⟨-, h, -⟩
  rw [isDClassB_nil] at h
  exact Bool.noConfusion h

/-! ### §3 The calculus-wide receipt -/

/-- EVERY class derivable in the absolute calculus has ≥ 2 entries — i.e. it is a Hodge
    character of grade g ≥ 1, and the geometric reading `V(a) ⊂ H^{|a|−2}(X_m^{|a|−2})`
    always names an actual Fermat variety.  Proved by induction over the eleven rules:
    the four introduction rules produce characters of grade ≥ 1 (`lefschetz` grade 2,
    `pairsD` a 𝔇-class, `standard` a σ_{p,x}, `starSplit` grade 3), `join` only grows the
    length, `cancel`/`descend` carry their own grade hypothesis, and `perm`/`galois`/
    `inflate` preserve length. -/
theorem Claim.length_ge_two {m : Nat} {a : List Nat} (d : Claim m a) : 2 ≤ a.length := by
  induction d with
  | hyp h => exact h.elim
  | perm hp _ ih => rw [← hp.length_eq]; exact ih
  | galois t _ _ ih => simpa using ih
  | lefschetz h => have := isHodgeB_length h; omega
  | pairsD g _ hD _ => exact isDClassB_length hD
  | standard h => have := isStdStrictB_length h; omega
  | join h1 _ hg1 _ _ _ ih1 _ =>
    have := isHodgeB_length h1
    simp only [List.length_append]
    omega
  | cancel h1 hg _ _ _ _ => have := isHodgeB_length h1; omega
  | starSplit b c _ h2 _ _ _ _ _ => have := isHodgeB_length h2; omega
  | inflate e _ _ _ _ _ ih => simpa using ih
  | descend e _ hg h1 _ _ _ => have := isHodgeB_length h1; omega

/-- consequently the empty class is not derivable at all (not merely not via `pairsD`). -/
theorem Claim.nil_not_derivable (m : Nat) : ¬ Claim m [] := by
  intro d
  have h := Claim.length_ge_two d
  simp at h

/-! ### §4 trust-base receipts: standard axioms only (no compiler, no native_decide) -/

#print axioms Claim.length_ge_two
#print axioms Claim.nil_not_derivable
#print axioms pairsD_nil_blocked

end BoundaryClaim
