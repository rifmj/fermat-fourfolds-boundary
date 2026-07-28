/-
  BoundaryClaim.lean — the CLAIM CALCULUS: the manuscript's deduction chains, machine-checked.

  The paper's closure theorems (A′, A″, Theorem B, the exchange walls) are citation chains
  through TEN geometric inputs: permutation and Galois-orbit invariance of Aoki's claim;
  Lefschetz (1,1) on the Fermat surface; Aoki's Theorems 1-1, 2-1, 1-4(i), 1-4(ii)
  (J. Math. Soc. Japan 39 (1987)); Theorem A's joining-line transport (manuscript §3);
  and the inflation/descent lemmas (manuscript §§4–5).  `ClaimFrom` accordingly has ELEVEN
  constructors: one per cited input, plus `hyp` (no citation — it carries the hypothesis
  set of a relative derivation and is discharged separately by `sound`).  This file:

    1. defines `ClaimFrom H m a` — the smallest predicate closed under EXACTLY those
       inference rules, with every side condition an explicitly checked Bool (grades,
       nonzero entries, vanishing-pair structure, gcd hypotheses of Thm 2-1, parities);
    2. proves `sound`: for ANY predicate Alg satisfying the ten cited inputs (the
       `Inputs` structure — one field per citation), every ClaimFrom-derivable class
       satisfies Alg.  The intended instantiation is dimension-polymorphic and
       validity-guarded — Alg m a := "a is a Hodge character of grade g ≥ 1 (|a| = 2g)
       and V(a) ⊂ H^{|a|−2}(X_m^{|a|−2}) is spanned by algebraic cycle classes" — under
       which every theorem below becomes the corresponding algebraicity statement; that
       instantiation (the geometry) is the paper's content, not this file's;
    3. derives, inside the calculus: the seven beyond-machinery orbits
       (m = 33 via the level-66 lift with the (33,33) quasi-witness; 45; both 105;
       the induced 99/135/165), the complete closure of EVERY grade-3 Hodge class at
       the census levels m ∈ {9, 21, 27, 33, 39, 45} (Theorem B at those levels), and
       the claim-equivalence WALLS W₇₀ (70 ≃ 210#2), W₁₁₀ (110#1 ≃ 110#2 ≃ 220),
       W₁₁₄ (the triangle) as derivation transformers.

  Trust base: standard axioms + `Lean.ofReduceBool` (native_decide) for the Bool side
  conditions and the census sweeps.  No `sorry`, no `axiom` declarations.
-/
import BoundaryCore
import BoundaryData

namespace BoundaryClaim
open BoundaryCore

/-! ### §0 Sorting/permutation bridge (Bool multiset-equality ⟹ List.Perm) -/

theorem orderedInsert_perm (x : Nat) (l : List Nat) :
    List.Perm (orderedInsert x l) (x :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
    unfold orderedInsert
    by_cases h : x ≤ y
    · simp only [if_pos h]
      exact List.Perm.refl _
    · simp only [if_neg h]
      exact (List.Perm.cons y ih).trans (List.Perm.swap x y ys)

theorem insSort_perm (l : List Nat) : List.Perm (insSort l) l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
    exact (orderedInsert_perm x (insSort xs)).trans (List.Perm.cons x ih)

theorem msEq_perm {a b : List Nat} (h : msEq a b = true) : List.Perm a b := by
  have he : insSort a = insSort b := eq_of_beq h
  exact (insSort_perm a).symm.trans (he ▸ insSort_perm b)

/-! ### §1 The Bool side conditions not already in BoundaryCore -/

/-- 𝔇-class (Aoki §1): a coordinate permutation of (a₀, −a₀, …, a_r, −a_r), entries
    nonzero — i.e. the multiset admits a perfect matching into vanishing pairs
    (the self-pair (m/2, m/2) at even m is a legitimate block). -/
def isDClassGo (m : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | 0, _ => false
  | fuel + 1, x :: xs =>
      let y := (m - x % m) % m
      0 < x && x < m && xs.contains y && isDClassGo m fuel (xs.erase y)

/-- 𝔇^r_m has r + 2 ≥ 2 entries (r ≥ 0 even), so the empty list is NOT a 𝔇-class: the
    recursion above bottoms out at `[]` and would otherwise let `pairsD`/`cancel` speak
    about an uncited object (there is no `X^{-2}_m`).  The length guard is the fence. -/
def isDClassB (m : Nat) (l : List Nat) : Bool := 2 ≤ l.length && isDClassGo m l.length l

/-- Aoki standard character σ_{p,x} under EXACTLY the Theorem 2-1 hypotheses:
    p an odd prime dividing m, d = m/p, gcd(x, d) = 1, admissible (d/(x,d) > 2),
    nonzero entries; σ is a coordinate permutation of {x, x+d, …, x+(p−1)d, m−px}.
    (`3 ≤ p` is implied by the enumeration range and by oddness+primality; it is checked
    explicitly so that |σ| = p + 1 ≥ 4 is extractable — see `BoundaryValidity`.) -/
def isStdStrictB (m : Nat) (σ : List Nat) : Bool :=
  ((List.range (m + 1)).drop 3).any fun p =>
    3 ≤ p && isPrimeNat p && p % 2 == 1 && m % p == 0 &&
    (((List.range m).drop 1).any fun x =>
      let d := m / p
      let e := ((List.range p).map fun k => (x + k * d) % m) ++ [(m - (p * x) % m) % m]
      Nat.gcd x d == 1 && d / Nat.gcd x d > 2 && e.all (· != 0) && msEq σ e)

/-! ### §2 The calculus -/

/-- `ClaimFrom H m a`: `claim(a)` at level m is derivable from the ten cited inputs
    together with the hypothesis set H.  One constructor per citation, plus `hyp` —
    eleven in total; every side condition is a decidable Bool so that instances close by
    `native_decide`.  `H := fun _ _ => False` gives the absolute calculus `Claim`.
    Every rule that INTRODUCES a class (`lefschetz`, `pairsD`, `standard`, `starSplit`)
    or moves one between levels (`inflate`, `descend`) is guarded so that the class is a
    Hodge character of grade g ≥ 1, i.e. a genuine character of X_m^{2g−2}; grade 0 and
    the empty list have no cited geometric object.  See `BoundaryValidity` for the
    calculus-wide receipt (`Claim.length_ge_two`). -/
inductive ClaimFrom (H : Nat → List Nat → Prop) : Nat → List Nat → Prop where
  /-- hypothesis introduction (for relative derivations — the exchange walls). -/
  | hyp {m a} : H m a → ClaimFrom H m a
  /-- claim is invariant under coordinate permutation (an algebraic automorphism of X⁴_m;
      manuscript §4 "∼ a coordinate permutation"). -/
  | perm {m a b} : List.Perm a b → ClaimFrom H m a → ClaimFrom H m b
  /-- claim is a Galois-orbit-level property (Aoki, Introduction: M(a) = ⊕ over the orbit). -/
  | galois {m a} (t : Nat) : (Nat.gcd t m == 1) = true →
      ClaimFrom H m a → ClaimFrom H m (a.map fun x => (t * x) % m)
  /-- Lefschetz (1,1) on the Fermat surface X²_m: every grade-2 Hodge quadruple is claimed
      (manuscript §4 step (1); no 𝔇-membership required). -/
  | lefschetz {m q} : isHodgeB m 2 q = true → ClaimFrom H m q
  /-- Aoki Theorem 1-1 (Shioda): 𝔇-classes are represented by linear subvarieties.
      `1 ≤ g` (with the length guard inside `isDClassB`) keeps the rule on cited objects:
      𝔇^r_m lives on X^r_m with r = 2g − 2 ≥ 0 even. -/
  | pairsD {m δ} (g : Nat) : 1 ≤ g → isDClassB m δ = true → isHodgeB m g δ = true →
      ClaimFrom H m δ
  /-- Aoki Theorem 2-1: the standard classes σ_{p,x}, gcd(x, m/p) = 1, are claimed. -/
  | standard {m σ} : isStdStrictB m σ = true → ClaimFrom H m σ
  /-- Aoki Theorem 1-4(i) (Shioda, Ran): claim(α) ∧ claim(β) ⟹ claim(α∗β), r,s even —
      in grade form: Hodge characters have even length automatically, so the r,s-parity
      is the Hodge-character typing of the two factors. -/
  | join {m g₁ g₂ α β} : isHodgeB m g₁ α = true → isHodgeB m g₂ β = true →
      1 ≤ g₁ → 1 ≤ g₂ →
      ClaimFrom H m α → ClaimFrom H m β → ClaimFrom H m (α ++ β)
  /-- Aoki Theorem 1-4(ii): claim(α∗δ) for some δ ∈ 𝔇^s_m (s even) ⟹ claim(α). -/
  | cancel {m g α δ} : isHodgeB m g α = true → 1 ≤ g → isDClassB m δ = true →
      (δ.length % 2 == 0) = true →
      ClaimFrom H m (α ++ δ) → ClaimFrom H m α
  /-- Theorem A of the manuscript (§3, `thm:A`, the transport through the Shioda–Katsura
      structure map): odd m, a = β′ ⊎ γ′ with zero-sum triples.

      DRIFT (2026-07-28, unsynced): the manuscript's current revision states Theorem A for
      m ARBITRARY — its transport lemma (`lem:transport`) replaced the base point
      e = (1:−1:0), which is what forced m odd, by the rational zero-cycle
      z = (1/m)(C ∩ H) — and no longer claims a single ruled-surface representative.  This
      rule still carries `m % 2 == 1`, so the calculus is strictly NARROWER than the paper:
      sound (the `Inputs.starSplit` field is correspondingly easier to instantiate), but it
      does not yet capture the even-m half of the printed theorem.  The three certified
      ∗-split closures (39/117/195) are odd, so nothing proved here depends on the gap. -/
  | starSplit {m a} (b c : List Nat) : (m % 2 == 1) = true → isHodgeB m 3 a = true →
      (b.length == 3) = true → (c.length == 3) = true →
      (lsum b % m == 0) = true → (lsum c % m == 0) = true →
      List.Perm a (b ++ c) → ClaimFrom H m a
  /-- inflation (manuscript §4, `lem:infl` = Lemma 4.1): claim_{m′}(β) ⟹ claim_{em′}(eβ).
      `1 ≤ g`: the finite morphism is between X_{m′}^{2g−2} and X_{em′}^{2g−2}; g = 0
      names no variety. -/
  | inflate {m' g a} (e : Nat) : 1 ≤ e → 1 ≤ g → isHodgeB m' g a = true →
      ((a.map (e * ·)).all fun x => x % (e * m') != 0) = true →
      ClaimFrom H m' a → ClaimFrom H (e * m') (a.map (e * ·))
  /-- descent (manuscript §5, `lem:descent` = Lemma 5.2, along (xᵢ) ↦ (xᵢᵉ)):
      claim_{em′}(eβ) ⟹ claim_{m′}(β). -/
  | descend {m' g a} (e : Nat) : 1 ≤ e → 1 ≤ g → isHodgeB m' g a = true →
      ((a.map (e * ·)).all fun x => x % (e * m') != 0) = true →
      ClaimFrom H (e * m') (a.map (e * ·)) → ClaimFrom H m' a

/-- the absolute calculus (no extra hypotheses). -/
abbrev Claim : Nat → List Nat → Prop := ClaimFrom fun _ _ => False

/-! ### §3 Soundness: any predicate satisfying the ten cited inputs contains the calculus -/

/-- The cited geometric inputs, abstractly.  The intended instantiation is
    DIMENSION-POLYMORPHIC and validity-guarded:

      `Alg m a` := "a is a Hodge character of grade g ≥ 1 at level m (so |a| = 2g) and
                    V(a) ⊂ H^{|a|−2}(X_m^{|a|−2}) is spanned by algebraic cycle classes".

    The ambient Fermat variety is read off the character — quadruples (g = 2) live on the
    surface X²_m, sextuples (g = 3) on the fourfold X⁴_m (the manuscript's case) — and the
    rules genuinely move between dimensions.  Reading `Alg m a` as a FIXED statement about
    H⁴(X⁴_m) is wrong and would not satisfy these fields: `lefschetz` speaks about H²(X²_m),
    `standard` about X^{p−1}_m, `join` about X⁶_m, X⁸_m, … (Aoki 1-4 changes n by r+s+2).

    The ten fields are EXACTLY: coordinate-permutation invariance; Galois-orbit invariance
    [Aoki87 Intro]; Lefschetz (1,1) on X²_m; Aoki Thm 1-1; Aoki Thm 2-1; Aoki Thm 1-4(i);
    Aoki Thm 1-4(ii); manuscript Theorem A; manuscript Lemmas 4.1 = `lem:infl` (inflation)
    and 5.2 = `lem:descent` (descent).  (Labels, not just numbers: the manuscript is under
    revision and the numbers have already moved once — `lem:descent` was 5.1 before it.)  `ClaimFrom`'s eleventh constructor `hyp` carries no citation and is
    discharged separately by `sound`'s `hH`. -/
structure Inputs (Alg : Nat → List Nat → Prop) : Prop where
  perm_inv : ∀ {m a b}, List.Perm a b → Alg m a → Alg m b
  galois_inv : ∀ {m a} (t : Nat), (Nat.gcd t m == 1) = true →
      Alg m a → Alg m (a.map fun x => (t * x) % m)
  lefschetz : ∀ {m q}, isHodgeB m 2 q = true → Alg m q
  pairsD : ∀ {m δ} (g : Nat), 1 ≤ g → isDClassB m δ = true → isHodgeB m g δ = true →
      Alg m δ
  standard : ∀ {m σ}, isStdStrictB m σ = true → Alg m σ
  join : ∀ {m g₁ g₂ α β}, isHodgeB m g₁ α = true → isHodgeB m g₂ β = true →
      1 ≤ g₁ → 1 ≤ g₂ → Alg m α → Alg m β → Alg m (α ++ β)
  cancel : ∀ {m g α δ}, isHodgeB m g α = true → 1 ≤ g → isDClassB m δ = true →
      (δ.length % 2 == 0) = true → Alg m (α ++ δ) → Alg m α
  starSplit : ∀ {m a} (b c : List Nat), (m % 2 == 1) = true → isHodgeB m 3 a = true →
      (b.length == 3) = true → (c.length == 3) = true →
      (lsum b % m == 0) = true → (lsum c % m == 0) = true →
      List.Perm a (b ++ c) → Alg m a
  inflate : ∀ {m' g a} (e : Nat), 1 ≤ e → 1 ≤ g → isHodgeB m' g a = true →
      ((a.map (e * ·)).all fun x => x % (e * m') != 0) = true →
      Alg m' a → Alg (e * m') (a.map (e * ·))
  descend : ∀ {m' g a} (e : Nat), 1 ≤ e → 1 ≤ g → isHodgeB m' g a = true →
      ((a.map (e * ·)).all fun x => x % (e * m') != 0) = true →
      Alg (e * m') (a.map (e * ·)) → Alg m' a

/-- SOUNDNESS.  Every ClaimFrom-derivation maps to any Inputs-satisfying predicate;
    hypotheses map through `hH`. -/
theorem ClaimFrom.sound {H : Nat → List Nat → Prop} {Alg : Nat → List Nat → Prop}
    (hI : Inputs Alg) (hH : ∀ {m a}, H m a → Alg m a) :
    ∀ {m a}, ClaimFrom H m a → Alg m a := by
  intro m a d
  induction d with
  | hyp h => exact hH h
  | perm hp _ ih => exact hI.perm_inv hp ih
  | galois t ht _ ih => exact hI.galois_inv t ht ih
  | lefschetz h => exact hI.lefschetz h
  | pairsD g h0 h1 h2 => exact hI.pairsD g h0 h1 h2
  | standard h => exact hI.standard h
  | join h1 h2 h3 h4 _ _ ih1 ih2 => exact hI.join h1 h2 h3 h4 ih1 ih2
  | cancel h1 h2 h3 h4 _ ih => exact hI.cancel h1 h2 h3 h4 ih
  | starSplit b c h1 h2 h3 h4 h5 h6 hp => exact hI.starSplit b c h1 h2 h3 h4 h5 h6 hp
  | inflate e h0 h1 h2 h3 _ ih => exact hI.inflate e h0 h1 h2 h3 ih
  | descend e h0 h1 h2 h3 _ ih => exact hI.descend e h0 h1 h2 h3 ih

theorem Claim.sound {Alg : Nat → List Nat → Prop} (hI : Inputs Alg) {m a}
    (d : Claim m a) : Alg m a :=
  ClaimFrom.sound hI (fun h => h.elim) d

/-! ### §4 Derived rules (used by the census closure and the walls) -/

section DerivedRules
variable {H : Nat → List Nat → Prop}

/-- decomposable closure: a ∼ q ⊎ δ with δ a vanishing pair, q a Lefschetz quadruple
    (derivable: join + perm — da Silva's induced-decomposable case). -/
theorem closes_decomp {m : Nat} {a q δ : List Nat}
    (hq : isHodgeB m 2 q = true) (hδD : isDClassB m δ = true) (hδH : isHodgeB m 1 δ = true)
    (hp : msEq a (q ++ δ) = true) : ClaimFrom H m a :=
  .perm (msEq_perm hp).symm
    (.join hq hδH (by decide) (by decide) (.lefschetz hq) (.pairsD 1 (by decide) hδD hδH))

/-- quasi-decomposable closure (da Silva (P2)): a ⊎ {k,m−k} = c ⊎ d, both Lefschetz
    quadruples (derivable: join + perm + cancel — the manuscript's A′/A″ mechanism at s=0). -/
theorem closes_quasi {m : Nat} {a c d δ : List Nat}
    (ha : isHodgeB m 3 a = true) (hc : isHodgeB m 2 c = true) (hd : isHodgeB m 2 d = true)
    (hδD : isDClassB m δ = true) (hδe : (δ.length % 2 == 0) = true)
    (hp : msEq (c ++ d) (a ++ δ) = true) : ClaimFrom H m a :=
  .cancel ha (by decide) hδD hδe
    (.perm (msEq_perm hp)
      (.join hc hd (by decide) (by decide) (.lefschetz hc) (.lefschetz hd)))

/-- Galois-orbit closure from a claimed base representative. -/
theorem closes_orbit {m t : Nat} {base a : List Nat}
    (ht : (Nat.gcd t m == 1) = true)
    (hp : msEq (base.map fun x => (t * x) % m) a = true)
    (h : ClaimFrom H m base) : ClaimFrom H m a :=
  .perm (msEq_perm hp) (.galois t ht h)

end DerivedRules

/-! ### §5 Bool checkers + their soundness (the census-closure engine) -/

def closesDecompB (m : Nat) (a : List Nat) : Bool :=
  (splitsK a 2).any fun (δ, q) =>
    isDClassB m δ && isHodgeB m 1 δ && isHodgeB m 2 q && msEq a (q ++ δ)

def closesQuasiB (m : Nat) (a : List Nat) : Bool :=
  isHodgeB m 3 a &&
  (((List.range ((m + 1) / 2)).drop 1).any fun k =>
    let δ := [k, m - k]
    isDClassB m δ && (δ.length % 2 == 0) &&
    ((splitsK (a ++ δ) 4).any fun (c, d) =>
      isHodgeB m 2 c && isHodgeB m 2 d && msEq (c ++ d) (a ++ δ)))

def closesStdB (m : Nat) (a : List Nat) : Bool :=
  (stdSextuples m).any fun σ =>
    isStdStrictB m σ &&
    ((unitsList m).any fun t =>
      Nat.gcd t m == 1 && msEq (σ.map fun x => (t * x) % m) a)

def closesStarB (m : Nat) (a : List Nat) : Bool :=
  (m % 2 == 1) && isHodgeB m 3 a &&
  ((splitsK a 3).any fun (b, c) =>
    b.length == 3 && c.length == 3 &&
    lsum b % m == 0 && lsum c % m == 0 && msEq a (b ++ c))

def closesOrbitB (m : Nat) (base a : List Nat) : Bool :=
  (unitsList m).any fun t =>
    Nat.gcd t m == 1 && msEq (base.map fun x => (t * x) % m) a

section CheckerSound
variable {H : Nat → List Nat → Prop}

theorem closesDecompB_sound {m : Nat} {a : List Nat}
    (h : closesDecompB m a = true) : ClaimFrom H m a := by
  obtain ⟨p, _, hb⟩ := List.any_eq_true.mp h
  obtain ⟨δ, q⟩ := p
  simp only [Bool.and_eq_true] at hb
  exact closes_decomp hb.1.2 hb.1.1.1 hb.1.1.2 hb.2

theorem closesQuasiB_sound {m : Nat} {a : List Nat}
    (h : closesQuasiB m a = true) : ClaimFrom H m a := by
  simp only [closesQuasiB, Bool.and_eq_true] at h
  obtain ⟨ha, hrest⟩ := h
  obtain ⟨k, _, hb⟩ := List.any_eq_true.mp hrest
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨hδD, hδe⟩, hsplit⟩ := hb
  obtain ⟨p, _, hcd⟩ := List.any_eq_true.mp hsplit
  obtain ⟨c, d⟩ := p
  simp only [Bool.and_eq_true] at hcd
  exact closes_quasi ha hcd.1.1 hcd.1.2 hδD hδe hcd.2

theorem closesStdB_sound {m : Nat} {a : List Nat}
    (h : closesStdB m a = true) : ClaimFrom H m a := by
  obtain ⟨σ, _, hb⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at hb
  obtain ⟨hstd, hany⟩ := hb
  obtain ⟨t, _, htb⟩ := List.any_eq_true.mp hany
  simp only [Bool.and_eq_true] at htb
  exact closes_orbit htb.1 htb.2 (.standard hstd)

theorem closesStarB_sound {m : Nat} {a : List Nat}
    (h : closesStarB m a = true) : ClaimFrom H m a := by
  simp only [closesStarB, Bool.and_eq_true] at h
  obtain ⟨⟨hodd, ha⟩, hsplit⟩ := h
  obtain ⟨p, _, hb⟩ := List.any_eq_true.mp hsplit
  obtain ⟨b, c⟩ := p
  simp only [Bool.and_eq_true] at hb
  exact .starSplit b c hodd ha hb.1.1.1.1 hb.1.1.1.2 hb.1.1.2 hb.1.2 (msEq_perm hb.2)

theorem closesOrbitB_sound {m : Nat} {base a : List Nat}
    (hbase : ClaimFrom H m base) (h : closesOrbitB m base a = true) : ClaimFrom H m a := by
  obtain ⟨t, _, hb⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at hb
  exact closes_orbit hb.1 hb.2 hbase

end CheckerSound

/-! ### §6 The seven beyond-machinery orbits, derived in the calculus -/

section Orbits
variable {H : Nat → List Nat → Prop}

def a45 : List Nat := [1, 19, 20, 28, 30, 37]
def a105a : List Nat := [3, 24, 50, 66, 85, 87]
def a105b : List Nat := [1, 22, 43, 64, 90, 95]

/-- Thm A′ mechanism, generically: claim(S), Q Lefschetz, a∗δ ∼ S∗Q, δ ∈ 𝔇², ⟹ claim(a). -/
theorem twoPair_close {m : Nat} {a S Q δ : List Nat} {gS : Nat}
    (hS : isHodgeB m gS S = true) (hgS : 1 ≤ gS) (hQ : isHodgeB m 2 Q = true)
    (ha : isHodgeB m 3 a = true) (hδD : isDClassB m δ = true)
    (hδe : (δ.length % 2 == 0) = true)
    (hp : msEq (S ++ Q) (a ++ δ) = true)
    (hclaimS : ClaimFrom H m S) : ClaimFrom H m a :=
  .cancel ha (by decide) hδD hδe
    (.perm (msEq_perm hp) (.join hS hQ hgS (by decide) hclaimS (.lefschetz hQ)))

/-- m = 45 (Thm A′ row 1): S = σ₅,₁ standard, δ = (5,40)(10,35). -/
theorem claim_a45 : ClaimFrom H 45 a45 :=
  twoPair_close (gS := 3)
    (S := [1, 10, 19, 28, 37, 40]) (Q := [5, 20, 30, 35]) (δ := [5, 40, 10, 35])
    (by native_decide) (by decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (.standard (by native_decide))

/-- m = 105 row 1: S = 3·σ₅,₁@35 (inflation, gcd(3,21) = 3 ∤ 1 blocks Thm 2-1 directly). -/
theorem claim_a105a : ClaimFrom H 105 a105a :=
  twoPair_close (gS := 3)
    (S := [3, 24, 45, 66, 87, 90]) (Q := [15, 50, 60, 85]) (δ := [15, 90, 45, 60])
    (by native_decide) (by decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (show ClaimFrom H (3 * 35) ([1, 8, 15, 22, 29, 30].map (3 * ·)) from
      .inflate 3 (by decide) (by decide) (g := 3) (by native_decide) (by native_decide)
        (.standard (by native_decide)))

/-- m = 105 row 2: S = σ₅,₁@105 directly. -/
theorem claim_a105b : ClaimFrom H 105 a105b :=
  twoPair_close (gS := 3)
    (S := [1, 22, 43, 64, 85, 100]) (Q := [5, 20, 90, 95]) (δ := [5, 100, 20, 85])
    (by native_decide) (by decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (.standard (by native_decide))

/-- level 66: claim(S₆₆) through the self-paired (33,33) quasi-witness (Thm A″ step 1). -/
theorem claim_S66 : ClaimFrom H 66 S66 :=
  .cancel (g := 3) (by native_decide) (by decide)
    (δ := [33, 33]) (by native_decide) (by native_decide)
    (.perm (msEq_perm (a := [2, 32, 33, 65] ++ [8, 33, 41, 50])
        (b := S66 ++ [33, 33]) (by native_decide))
      (.join (g₁ := 2) (g₂ := 2) (by native_decide) (by native_decide)
        (by decide) (by decide)
        (.lefschetz (by native_decide)) (.lefschetz (by native_decide))))

/-- level 66: claim(a₆₆) (Thm A″ step 2: join with Q₆₆, cancel (1,65)(25,41)). -/
theorem claim_a66 : ClaimFrom H 66 a66 :=
  .cancel (g := 3) (by native_decide) (by decide)
    (δ := [1, 65, 25, 41]) (by native_decide) (by native_decide)
    (.perm (msEq_perm (a := S66 ++ Q66) (b := a66 ++ [1, 65, 25, 41]) (by native_decide))
      (.join (g₁ := 3) (g₂ := 2) (by native_decide) (by native_decide)
        (by decide) (by decide) claim_S66 (.lefschetz (by native_decide))))

/-- THE m = 33 WITNESS (Thm A″): descent of a₆₆ = 2w along x ↦ x² . -/
theorem claim_w33 : ClaimFrom H 33 wDaSilva :=
  .descend 2 (by decide) (by decide) (g := 3) (by native_decide) (by native_decide)
    (show ClaimFrom H (2 * 33) (wDaSilva.map (2 * ·)) from claim_a66)

/-- the induced copies 99, 165 (inflations of w) and 135 (inflation of a45). -/
theorem claim_w99 : ClaimFrom H 99 ([3, 12, 48, 66, 75, 93]) :=
  show ClaimFrom H (3 * 33) (wDaSilva.map (3 * ·)) from
    .inflate 3 (by decide) (by decide) (g := 3) (by native_decide) (by native_decide) claim_w33

theorem claim_w165 : ClaimFrom H 165 ([5, 20, 80, 110, 125, 155]) :=
  show ClaimFrom H (5 * 33) (wDaSilva.map (5 * ·)) from
    .inflate 5 (by decide) (by decide) (g := 3) (by native_decide) (by native_decide) claim_w33

theorem claim_a135 : ClaimFrom H 135 ([3, 57, 60, 84, 90, 111]) :=
  show ClaimFrom H (3 * 45) (a45.map (3 * ·)) from
    .inflate 3 (by decide) (by decide) (g := 3) (by native_decide) (by native_decide) claim_a45

/-- the *-split classes at 39 / 117 / 195 (Theorem A instances; 117/195 = the census reps). -/
theorem claim_39a : ClaimFrom H 39 [1, 7, 16, 22, 34, 37] :=
  .starSplit [1, 16, 22] [7, 34, 37] (by decide) (by native_decide)
    (by decide) (by decide) (by decide) (by decide) (msEq_perm (by native_decide))

theorem claim_39b : ClaimFrom H 39 [1, 14, 16, 22, 29, 35] :=
  .starSplit [1, 16, 22] [14, 29, 35] (by decide) (by native_decide)
    (by decide) (by decide) (by decide) (by decide) (msEq_perm (by native_decide))

theorem claim_117a : ClaimFrom H 117 [3, 21, 48, 66, 102, 111] :=
  .starSplit [3, 48, 66] [21, 102, 111] (by decide) (by native_decide)
    (by decide) (by decide) (by decide) (by decide) (msEq_perm (by native_decide))

theorem claim_117b : ClaimFrom H 117 [3, 42, 48, 66, 87, 105] :=
  .starSplit [3, 48, 66] [42, 87, 105] (by decide) (by native_decide)
    (by decide) (by decide) (by decide) (by decide) (msEq_perm (by native_decide))

theorem claim_195a : ClaimFrom H 195 [5, 35, 80, 110, 170, 185] :=
  .starSplit [5, 80, 110] [35, 170, 185] (by decide) (by native_decide)
    (by decide) (by decide) (by decide) (by decide) (msEq_perm (by native_decide))

theorem claim_195b : ClaimFrom H 195 [5, 70, 80, 110, 145, 175] :=
  .starSplit [5, 80, 110] [70, 145, 175] (by decide) (by native_decide)
    (by decide) (by decide) (by decide) (by decide) (msEq_perm (by native_decide))

end Orbits

/-! ### §7 Theorem B at the census levels: EVERY grade-3 Hodge class closes -/

section CensusClosure
variable {H : Nat → List Nat → Prop}

def closesBase (m : Nat) (a : List Nat) : Bool :=
  closesDecompB m a || closesQuasiB m a || closesStdB m a || closesStarB m a

theorem closesBase_sound {m : Nat} {a : List Nat}
    (h : closesBase m a = true) : ClaimFrom H m a := by
  simp only [closesBase, Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h
  · exact closesDecompB_sound h
  · exact closesQuasiB_sound h
  · exact closesStdB_sound h
  · exact closesStarB_sound h

def closes33 (a : List Nat) : Bool := closesBase 33 a || closesOrbitB 33 wDaSilva a
def closes39 (a : List Nat) : Bool := closesBase 39 a
def closes45 (a : List Nat) : Bool := closesBase 45 a || closesOrbitB 45 a45 a
def closesSmall (m : Nat) (a : List Nat) : Bool := closesBase m a

/-- the census sweeps: every enumerated grade-3 Hodge sextuple at the six levels passes
    its closure checker (heavy native_decide — the full enumerations run here). -/
theorem sweep_33 : (hodgeSextuples 33).all closes33 = true := by native_decide
theorem sweep_39 : (hodgeSextuples 39).all closes39 = true := by native_decide
theorem sweep_45 : (hodgeSextuples 45).all closes45 = true := by native_decide
theorem sweep_small :
    ((hodgeSextuples 9).all (closesSmall 9) &&
     (hodgeSextuples 21).all (closesSmall 21) &&
     (hodgeSextuples 27).all (closesSmall 27)) = true := by native_decide

/-- THEOREM B in the calculus, m = 33: every grade-3 Hodge class of X⁴₃₃ is claimed. -/
theorem thmB_33 : ∀ a ∈ hodgeSextuples 33, ClaimFrom H 33 a := by
  intro a ha
  have h := List.all_eq_true.mp sweep_33 a ha
  simp only [closes33, Bool.or_eq_true] at h
  rcases h with h | h
  · exact closesBase_sound h
  · exact closesOrbitB_sound claim_w33 h

theorem thmB_39 : ∀ a ∈ hodgeSextuples 39, ClaimFrom H 39 a := by
  intro a ha
  exact closesBase_sound (List.all_eq_true.mp sweep_39 a ha)

theorem thmB_45 : ∀ a ∈ hodgeSextuples 45, ClaimFrom H 45 a := by
  intro a ha
  have h := List.all_eq_true.mp sweep_45 a ha
  simp only [closes45, Bool.or_eq_true] at h
  rcases h with h | h
  · exact closesBase_sound h
  · exact closesOrbitB_sound claim_a45 h

theorem thmB_small : ∀ m ∈ ([9, 21, 27] : List Nat), ∀ a ∈ hodgeSextuples m, ClaimFrom H m a := by
  intro m hm a ha
  have hs := sweep_small
  simp only [Bool.and_eq_true] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact closesBase_sound (List.all_eq_true.mp hs.1.1 a ha)
  · exact closesBase_sound (List.all_eq_true.mp hs.1.2 a ha)
  · exact closesBase_sound (List.all_eq_true.mp hs.2 a ha)

end CensusClosure

/-! ### §8 The exchange walls: claim-equivalences as derivation transformers -/

section Walls
variable {H : Nat → List Nat → Prop}

/-- the Exchange move (the manuscript's exchange mechanism, |A| = 2 shape): from claim(target),
    land on the conjugate T′ = (T∖A) ⊎ B, join the Lefschetz exchanger q = A ⊎ (−B),
    cancel δ = B ⊎ (−B) ∈ 𝔇². -/
theorem edge_transfer {m t : Nat} {T Tp q δ target : List Nat}
    (hq : isHodgeB m 2 q = true) (hTp : isHodgeB m 3 Tp = true) (hT : isHodgeB m 3 T = true)
    (hδD : isDClassB m δ = true) (hδe : (δ.length % 2 == 0) = true)
    (ht : (Nat.gcd t m == 1) = true)
    (hp1 : msEq (target.map fun x => (t * x) % m) Tp = true)
    (hp2 : msEq (Tp ++ q) (T ++ δ) = true)
    (h : ClaimFrom H m target) : ClaimFrom H m T :=
  .cancel hT (by decide) hδD hδe
    (.perm (msEq_perm hp2)
      (.join hTp hq (by decide) (by decide)
        (.perm (msEq_perm hp1) (.galois t ht h)) (.lefschetz hq)))

def T110a : List Nat := [1, 24, 62, 71, 81, 91]
def T110b : List Nat := [1, 31, 55, 71, 81, 91]
def T114a : List Nat := [1, 13, 43, 72, 103, 110]
def T114b : List Nat := [1, 13, 43, 80, 102, 103]
def T114c : List Nat := [1, 7, 78, 79, 86, 91]
def c70 : List Nat := [1, 20, 24, 42, 61, 62]
def T210 : List Nat := [2, 9, 129, 142, 168, 180]
def T220 : List Nat := [1, 62, 111, 142, 162, 182]

/-- W₁₁₀ core: the two m=110 classes are claim-equivalent (edges from gen_data.py,
    re-verified: q = (24,55,62,79) resp. (1,55,56,108) at t = 71). -/
theorem wall110_ba (h : ClaimFrom H 110 T110b) : ClaimFrom H 110 T110a :=
  edge_transfer (t := 1) (Tp := [1, 31, 55, 71, 81, 91]) (q := [24, 55, 62, 79])
    (δ := [31, 55, 79, 55])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) h

theorem wall110_ab (h : ClaimFrom H 110 T110a) : ClaimFrom H 110 T110b :=
  edge_transfer (t := 71) (Tp := [2, 31, 54, 71, 81, 91]) (q := [1, 55, 56, 108])
    (δ := [2, 54, 108, 56])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) h

theorem wall114_ba (h : ClaimFrom H 114 T114b) : ClaimFrom H 114 T114a :=
  edge_transfer (t := 1) (Tp := T114b) (q := [12, 34, 72, 110])
    (δ := [80, 102, 34, 12])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) h

theorem wall114_ab (h : ClaimFrom H 114 T114a) : ClaimFrom H 114 T114b :=
  edge_transfer (t := 1) (Tp := T114a) (q := [4, 42, 80, 102])
    (δ := [72, 110, 42, 4])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) h

theorem wall114_ca (h : ClaimFrom H 114 T114c) : ClaimFrom H 114 T114a :=
  edge_transfer (t := 55) (Tp := [43, 55, 56, 72, 103, 13]) (q := [1, 58, 59, 110])
    (δ := [55, 56, 59, 58])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) h

theorem wall114_ac (h : ClaimFrom H 114 T114a) : ClaimFrom H 114 T114c :=
  edge_transfer (t := 85) (Tp := [85, 91, 7, 78, 2, 79]) (q := [1, 29, 86, 112])
    (δ := [2, 85, 112, 29])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) h

/-- W₇₀ ≃ 210#2: through the 3-lift (inflate/descend) and the level-210 exchange. -/
theorem wall70_from210 (h : ClaimFrom H 210 T210) : ClaimFrom H 70 c70 :=
  .descend 3 (by decide) (by decide) (g := 3) (by native_decide) (by native_decide)
    (show ClaimFrom H (3 * 70) (c70.map (3 * ·)) from
      edge_transfer (t := 47) (Tp := [94, 164, 3, 126, 183, 60]) (q := [46, 72, 116, 186])
        (δ := [94, 164, 116, 46])
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide) h)

theorem wall70_to210 (h : ClaimFrom H 70 c70) : ClaimFrom H 210 T210 :=
  edge_transfer (t := 73) (Tp := [9, 129, 168, 180, 6, 138]) (q := [2, 72, 142, 204])
    (δ := [6, 138, 204, 72])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (show ClaimFrom H (3 * 70) (c70.map (3 * ·)) from
      .inflate 3 (by decide) (by decide) (g := 3) (by native_decide) (by native_decide) h)

/-- W₁₁₀ ∋ 220: the 220 class is claim-equivalent to the 2-lift of 110#2. -/
theorem wall220_from110 (h : ClaimFrom H 110 T110b) : ClaimFrom H 220 T220 :=
  edge_transfer (t := 1) (Tp := [2, 62, 110, 142, 162, 182]) (q := [1, 110, 111, 218])
    (δ := [2, 110, 218, 110])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (show ClaimFrom H (2 * 110) (T110b.map (2 * ·)) from
      .inflate 2 (by decide) (by decide) (g := 3) (by native_decide) (by native_decide) h)

theorem wall220_to110 (h : ClaimFrom H 220 T220) : ClaimFrom H 110 T110b :=
  .descend 2 (by decide) (by decide) (g := 3) (by native_decide) (by native_decide)
    (show ClaimFrom H (2 * 110) (T110b.map (2 * ·)) from
      edge_transfer (t := 1) (Tp := T220) (q := [2, 109, 110, 219])
        (δ := [1, 111, 219, 109])
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide) h)

end Walls

/-! ### §9 The headline conditional theorems (via soundness) -/

/-- the seven beyond-machinery orbits of the odd census, for ANY Inputs-satisfying Alg. -/
theorem beyond_machinery (Alg : Nat → List Nat → Prop) (hI : Inputs Alg) :
    Alg 33 wDaSilva ∧ Alg 45 a45 ∧ Alg 105 a105a ∧ Alg 105 a105b ∧
    Alg 99 [3, 12, 48, 66, 75, 93] ∧ Alg 135 [3, 57, 60, 84, 90, 111] ∧
    Alg 165 [5, 20, 80, 110, 125, 155] :=
  ⟨Claim.sound hI claim_w33, Claim.sound hI claim_a45, Claim.sound hI claim_a105a,
   Claim.sound hI claim_a105b, Claim.sound hI claim_w99, Claim.sound hI claim_a135,
   Claim.sound hI claim_w165⟩

/-- THEOREM B at the machine-checked levels: for any Inputs-satisfying Alg, EVERY
    grade-3 Hodge character of X⁴_m, m ∈ {9, 21, 27, 33, 39, 45}, satisfies Alg.
    (Instantiating Alg := algebraicity and Inputs := the ten citations gives the
    manuscript's Theorem B at those levels.) -/
theorem thmB_conditional (Alg : Nat → List Nat → Prop) (hI : Inputs Alg) :
    ∀ m ∈ ([9, 21, 27, 33, 39, 45] : List Nat), ∀ a ∈ hodgeSextuples m, Alg m a := by
  intro m hm a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Claim.sound hI (thmB_small 9 (by simp) a ha)
  · exact Claim.sound hI (thmB_small 21 (by simp) a ha)
  · exact Claim.sound hI (thmB_small 27 (by simp) a ha)
  · exact Claim.sound hI (thmB_33 a ha)
  · exact Claim.sound hI (thmB_39 a ha)
  · exact Claim.sound hI (thmB_45 a ha)

/-- the *-split closures at the three Theorem-A levels. -/
theorem starSplit_closures (Alg : Nat → List Nat → Prop) (hI : Inputs Alg) :
    Alg 39 [1, 7, 16, 22, 34, 37] ∧ Alg 39 [1, 14, 16, 22, 29, 35] ∧
    Alg 117 [3, 21, 48, 66, 102, 111] ∧ Alg 117 [3, 42, 48, 66, 87, 105] ∧
    Alg 195 [5, 35, 80, 110, 170, 185] ∧ Alg 195 [5, 70, 80, 110, 145, 175] :=
  ⟨Claim.sound hI claim_39a, Claim.sound hI claim_39b, Claim.sound hI claim_117a,
   Claim.sound hI claim_117b, Claim.sound hI claim_195a, Claim.sound hI claim_195b⟩

/-- transfer a relative derivation to any Inputs-satisfying Alg. -/
theorem transfer {Alg : Nat → List Nat → Prop} (hI : Inputs Alg)
    {m₀ m₁ : Nat} {a₀ a₁ : List Nat}
    (d : ClaimFrom (fun m a => m = m₀ ∧ a = a₀) m₁ a₁) (h : Alg m₀ a₀) : Alg m₁ a₁ :=
  ClaimFrom.sound hI (fun hp => by rcases hp with ⟨rfl, rfl⟩; exact h) d

/-- THE WALLS (W₇₀/W₁₁₀/W₁₁₄), Alg-level: closing any member closes the wall.
    W₁₁₀ = {110#1 ≃ 110#2 ≃ 220}, W₁₁₄ = the triangle, W₇₀ = {70 ≃ 210#2}. -/
theorem walls (Alg : Nat → List Nat → Prop) (hI : Inputs Alg) :
    ((Alg 110 T110a → Alg 110 T110b) ∧ (Alg 110 T110b → Alg 110 T110a) ∧
     (Alg 110 T110b → Alg 220 T220) ∧ (Alg 220 T220 → Alg 110 T110b)) ∧
    ((Alg 114 T114a → Alg 114 T114b) ∧ (Alg 114 T114b → Alg 114 T114a) ∧
     (Alg 114 T114a → Alg 114 T114c) ∧ (Alg 114 T114c → Alg 114 T114a)) ∧
    ((Alg 70 c70 → Alg 210 T210) ∧ (Alg 210 T210 → Alg 70 c70)) :=
  ⟨⟨fun h => transfer hI (wall110_ab (.hyp ⟨rfl, rfl⟩)) h,
    fun h => transfer hI (wall110_ba (.hyp ⟨rfl, rfl⟩)) h,
    fun h => transfer hI (wall220_from110 (.hyp ⟨rfl, rfl⟩)) h,
    fun h => transfer hI (wall220_to110 (.hyp ⟨rfl, rfl⟩)) h⟩,
   ⟨fun h => transfer hI (wall114_ab (.hyp ⟨rfl, rfl⟩)) h,
    fun h => transfer hI (wall114_ba (.hyp ⟨rfl, rfl⟩)) h,
    fun h => transfer hI (wall114_ac (.hyp ⟨rfl, rfl⟩)) h,
    fun h => transfer hI (wall114_ca (.hyp ⟨rfl, rfl⟩)) h⟩,
   ⟨fun h => transfer hI (wall70_to210 (.hyp ⟨rfl, rfl⟩)) h,
    fun h => transfer hI (wall70_from210 (.hyp ⟨rfl, rfl⟩)) h⟩⟩

/-! ### §10 trust-base receipts -/

#print axioms thmB_conditional
#print axioms beyond_machinery
#print axioms walls

end BoundaryClaim
