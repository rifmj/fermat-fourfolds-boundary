/-
  BoundaryThmB.lean — the codimension-1 and codimension-3 legs of Theorem B, and the
  machine-checked reduction FULL Hodge conjecture ⟸ census closure.

  The manuscript's Theorem B concludes the Hodge conjecture IN FULL for the Fermat
  fourfolds of its range, by a one-paragraph reduction (`thm:B`):

    codim 0/4 : H⁰ and H⁸ are spanned by the classes of X and of a point (trivial);
    codim 1   : Lefschetz (1,1);
    codim 2   : the non-primitive summand of H⁴ is spanned by the algebraic class h², so
                the statement follows from the primitive one — which is the census;
    codim 3   : hard Lefschetz — L² : H²(ℚ) ≅ H⁶(ℚ) is an isomorphism of Hodge
                structures, so every (3,3) Hodge class is L² of a (1,1) Hodge class, and
                L² of a divisor class is algebraic.

  This file states those citations as the fields of an abstract interface (`ThmBInputs`,
  the same genre as `BoundaryClaim.Inputs` — one field per citation, geometry abstracted)
  and machine-checks the reduction: `HC_of_census` derives "every (c,c) Hodge class is
  algebraic, c = 0..4" from the census closure plus the cited fields.  Combined with the
  full census (`thmB_census_full`) this yields `HC_fourfold`, the manuscript's headline
  statement at calculus level, for every census level.

  What is NOT here (unchanged): the geometry.  Lefschetz (1,1), hard Lefschetz, the
  rationality of the primitive decomposition, and the Shioda character-space spanning of
  primitive cohomology are CITED — they are the fields of `ThmBInputs`, exactly as Aoki's
  theorems are the fields of `Inputs`.  Instantiating both structures is the manuscript's
  §§3–5 and the classical literature, not this file.

  Trust base: `HC_of_census` uses standard axioms only (no native_decide, no compiler);
  `HC_fourfold` inherits the census sweeps' `Lean.ofReduceBool`.
-/
import BoundaryCensusMain

namespace BoundaryThmB
open BoundaryCore BoundaryClaim BoundaryCensus

/-- an abstract Fermat-fourfold cohomology carrier: `C c` stands for H^{2c}(X⁴_m, ℚ);
    `hodge c x` = "x is a (c,c) Hodge class", `alg c x` = "x lies in the ℚ-span of
    codimension-c algebraic cycle classes"; `prim`/`hsq` = the primitive part and the
    line ℚ·h² inside H⁴; `Lsq` = the hard-Lefschetz operator L² : H² → H⁶. -/
structure Fourfold : Type 1 where
  C : Nat → Type
  hodge : (c : Nat) → C c → Prop
  alg : (c : Nat) → C c → Prop
  add : (c : Nat) → C c → C c → C c
  prim : C 2 → Prop
  hsq : C 2 → Prop
  Lsq : C 1 → C 3

/-- the cited inputs of Theorem B's reduction, one field per citation (the codim-2 census
    is NOT a field — it is the theorem's other hypothesis, supplied by the claim calculus):

    * `h0` / `h4` — H⁰/H⁸ spanned by the class of X / of a point;
    * `lefschetz11` — Lefschetz (1,1) on the fourfold;
    * `decomp22` — rationality of the primitive decomposition H⁴ = prim ⊕ ℚ·h²,
      compatibly with (p,q)-types;
    * `hsq_alg` — h² is algebraic (and ℚ-multiples of algebraic classes are algebraic);
    * `alg_add` — algebraic classes are closed under sum;
    * `prim_span` — Shioda's character decomposition: if every grade-3 Hodge character of
      X⁴_m satisfies Alg (:= "V(a) is spanned by algebraic classes"), then every primitive
      (2,2) Hodge class is algebraic;
    * `hardLefschetz` — L² : H²(ℚ) ≅ H⁶(ℚ) as Hodge structures (every (3,3) Hodge class
      is L² of a (1,1) Hodge class);
    * `Lsq_alg` — L² of an algebraic class is algebraic (intersection with hyperplanes). -/
structure ThmBInputs (m : Nat) (F : Fourfold) (Alg : Nat → List Nat → Prop) : Prop where
  h0 : ∀ x, F.hodge 0 x → F.alg 0 x
  lefschetz11 : ∀ x, F.hodge 1 x → F.alg 1 x
  decomp22 : ∀ x, F.hodge 2 x → ∃ p q, x = F.add 2 p q ∧ F.prim p ∧ F.hodge 2 p ∧ F.hsq q
  hsq_alg : ∀ q, F.hsq q → F.alg 2 q
  alg_add : ∀ c x y, F.alg c x → F.alg c y → F.alg c (F.add c x y)
  prim_span : ∀ p, F.prim p → F.hodge 2 p →
      (∀ a, isHodgeB m 3 a = true → Alg m a) → F.alg 2 p
  hardLefschetz : ∀ y, F.hodge 3 y → ∃ x, F.hodge 1 x ∧ y = F.Lsq x
  Lsq_alg : ∀ x, F.alg 1 x → F.alg 3 (F.Lsq x)
  h4 : ∀ x, F.hodge 4 x → F.alg 4 x

/-- THE REDUCTION (machine-checked, standard axioms only): census closure of the grade-3
    Hodge characters + the cited legs ⟹ the FULL Hodge conjecture statement in every
    codimension 0..4.  This is the manuscript's Theorem-B paragraph as a derivation. -/
theorem HC_of_census {m : Nat} {F : Fourfold} {Alg : Nat → List Nat → Prop}
    (hI : Inputs Alg) (B : ThmBInputs m F Alg)
    (census : ∀ a, isHodgeB m 3 a = true → Claim m a) :
    ∀ c, c ≤ 4 → ∀ x : F.C c, F.hodge c x → F.alg c x := by
  have hAlg : ∀ a, isHodgeB m 3 a = true → Alg m a :=
    fun a ha => Claim.sound hI (census a ha)
  intro c hc x hx
  match c, hc with
  | 0, _ => exact B.h0 x hx
  | 1, _ => exact B.lefschetz11 x hx
  | 2, _ =>
    obtain ⟨p, q, rfl, hp, hph, hq⟩ := B.decomp22 x hx
    exact B.alg_add 2 p q (B.prim_span p hp hph hAlg) (B.hsq_alg q hq)
  | 3, _ =>
    obtain ⟨x1, hx1, rfl⟩ := B.hardLefschetz x hx
    exact B.Lsq_alg x1 (B.lefschetz11 x1 hx1)
  | 4, _ => exact B.h4 x hx
  | n + 5, hc => exact absurd hc (by omega)

/-- THE HEADLINE: for every census level m (all odd 3 ≤ m ≤ 199 and 231/273/297), any
    carrier F and predicate Alg satisfying the ten calculus citations and the nine
    Theorem-B legs, EVERY (c,c) Hodge class of X⁴_m is algebraic, c = 0..4 — the
    manuscript's "Hodge conjecture in full", at calculus level. -/
theorem HC_fourfold {Alg : Nat → List Nat → Prop} (hI : Inputs Alg) :
    ∀ m ∈ censusLevels, ∀ (F : Fourfold), ThmBInputs m F Alg →
      ∀ c, c ≤ 4 → ∀ x : F.C c, F.hodge c x → F.alg c x := by
  intro m hm F B
  exact HC_of_census hI B (fun a ha => thmB_census_full m hm a ha)

/-! ### trust-base receipts (`HC_of_census`: standard axioms ONLY — no compiler) -/

#print axioms HC_of_census
#print axioms HC_fourfold

end BoundaryThmB
