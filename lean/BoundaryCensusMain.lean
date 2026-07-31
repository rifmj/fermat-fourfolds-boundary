/-
  BoundaryCensusMain.lean — assembly of the full-census sweeps into the headline theorems.

  `thmB_census_full` : at EVERY census level (all odd 3 ≤ m ≤ 199, and 231/273/297), every
  grade-3 Hodge character — any entry order — is derivable in the claim calculus.
  `thmB_full_conditional` : the same over any `Inputs`-satisfying predicate Alg (the
  manuscript's Theorem B census leg, instantiating Alg := algebraicity).

  This subsumes and extends `BoundaryClaim.thmB_conditional` (six levels) to the full
  Theorem-B range of the manuscript, plus the three beyond-the-bound probe levels.
-/
import BoundaryCensusSweeps1
import BoundaryCensusSweeps2
import BoundaryCensusSweeps3
import BoundaryCensusSweeps4
import BoundaryCensusSweeps5

namespace BoundaryCensus
open BoundaryCore BoundaryClaim

theorem sweep_all : ∀ p ∈ censusTable, levelFull p.1 p.2 (levelBases p.1) = true := by
  intro p hp
  unfold censusTable at hp
  rcases List.mem_append.mp hp with h | hp
  · exact List.all_eq_true.mp sweeps1 p h
  rcases List.mem_append.mp hp with h | hp
  · exact List.all_eq_true.mp sweeps2 p h
  rcases List.mem_append.mp hp with h | hp
  · exact List.all_eq_true.mp sweeps3 p h
  rcases List.mem_append.mp hp with h | hp
  · exact List.all_eq_true.mp sweeps4 p h
  · exact List.all_eq_true.mp sweeps5 p hp

/-- THEOREM B, census leg, full range, calculus level: at every census level m (odd 3..199,
    231, 273, 297), every grade-3 Hodge character of X⁴_m is derivable in the claim
    calculus — over ANY hypothesis predicate H (in particular absolutely). -/
theorem thmB_census_full {H : Nat → List Nat → Prop} :
    ∀ m ∈ censusLevels, ∀ a, isHodgeB m 3 a = true → ClaimFrom H m a := by
  intro m hm a ha
  obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
  subst hpe
  exact thmB_level (sweep_all p hp) (basesClaimed p.1) a ha

/-- THEOREM B, census leg, full range, conditional form: for any predicate Alg satisfying
    the ten cited inputs, every grade-3 Hodge character at every census level satisfies
    Alg.  (Instantiating Alg := algebraicity gives the manuscript's Theorem B census leg
    for all odd m ≤ 199 — and at the probe levels 231/273/297.) -/
theorem thmB_full_conditional (Alg : Nat → List Nat → Prop) (hI : Inputs Alg) :
    ∀ m ∈ censusLevels, ∀ a, isHodgeB m 3 a = true → Alg m a :=
  fun m hm a ha =>
    Claim.sound hI (thmB_census_full (H := fun _ _ => False) m hm a ha)

/-! ### trust-base receipts -/

#print axioms census_enumeration_complete
#print axioms thmB_census_full
#print axioms thmB_full_conditional
#print axioms rawFull_matches_core

end BoundaryCensus
