/-
  BoundaryForms.lean — mathlib tier: the manuscript's two ∀-lemmas as universal theorems
  (no native_decide, no compiler in the trust base — standard axioms only).

  1.  `gradeConst_length` (census completeness, `lem:complete` = Lemma 6.1): a multiset of
      nonzero residues
      mod m with CONSTANT grade g (Σᵢ ⟨t aᵢ⟩ = g·m for every unit t) has length exactly 2g.
      This is the parity fact behind the census classifier (part lengths (2,6)/(4,4) of the
      quasi test, M_m(1) = the vanishing pairs).  Only t = 1 and t = m−1 are used — the
      constancy hypothesis is needed exactly at one complementary pair of units.

  2.  `apChar_gradeConst` (Proposition D, standard = AP): for ODD p ∣ m with px ≢ 0 (mod m),
      Aoki's padded arithmetic-progression multiset {x, x+m/p, …, x+(p−1)m/p, −px} has
      constant grade (p+1)/2 — for EVERY unit t simultaneously.  (No primality of p is
      needed for the grade computation; Aoki's σ_{p,x} takes p an odd prime.)  With
      `apChar_grade_three_iff` ((p+1)/2 = 3 ⟺ p = 5) this is the manuscript's §2 claim;
      `apChar_entries_nonzero` is the nonzero-entries/admissibility part, and
      `apChar_length_consistency` closes the loop against Lemma 1 (length = 2·grade).
-/
import Mathlib

namespace BoundaryForms

open Finset

/-- Σᵢ ⟨t·aᵢ⟩ = g·m for every unit t — the manuscript's grade-g constancy (§1). -/
def GradeConst (m g : Nat) (a : List Nat) : Prop :=
  ∀ t : Nat, Nat.gcd t m = 1 → (a.map fun x => t * x % m).sum = g * m

/-! ### §1 The parity lemma -/

private lemma neg_one_mul_mod (m x : Nat) (hm : 2 ≤ m) (hx : x % m ≠ 0) :
    (m - 1) * x % m = m - x % m := by
  rw [Nat.mul_mod, Nat.mod_eq_of_lt (show m - 1 < m by omega)]
  have hrlt : x % m < m := Nat.mod_lt _ (by omega)
  have hrpos : 0 < x % m := Nat.pos_of_ne_zero hx
  generalize x % m = r at hrlt hrpos ⊢
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨u, rfl⟩ : ∃ u, m = r' + 1 + u + 1 := ⟨m - r' - 2, by omega⟩
  rw [show r' + 1 + u + 1 - 1 = r' + u + 1 by omega]
  rw [show (r' + u + 1) * (r' + 1) = (u + 1) + r' * (r' + 1 + u + 1) by ring]
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  omega

private lemma sum_map_mod_le (m : Nat) (hm : 0 < m) (a : List Nat) :
    (a.map fun x => x % m).sum ≤ a.length * m := by
  induction a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hx : x % m ≤ m := le_of_lt (Nat.mod_lt _ hm)
    rw [Nat.succ_mul]
    omega

private lemma sum_map_msub (m : Nat) (hm : 0 < m) (a : List Nat) :
    (a.map fun x => m - x % m).sum = a.length * m - (a.map fun x => x % m).sum := by
  induction a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hx : x % m ≤ m := le_of_lt (Nat.mod_lt _ hm)
    have hle := sum_map_mod_le m hm xs
    rw [ih, Nat.succ_mul]
    omega

/-- CENSUS-COMPLETENESS LEMMA (i) / M_m parity: a grade-constant multiset of nonzero
    residues mod m (m ≥ 2) has even length 2g.  In particular M_m(1) = the vanishing
    pairs and every quasi-split has part lengths (2,6) or (4,4). -/
theorem gradeConst_length (m g : Nat) (hm : 2 ≤ m) (a : List Nat)
    (hnz : ∀ x ∈ a, x % m ≠ 0) (h : GradeConst m g a) : a.length = 2 * g := by
  have h1 : (a.map fun x => 1 * x % m).sum = g * m := h 1 (Nat.gcd_one_left m)
  have hcop : Nat.gcd (m - 1) m = 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp
  have h2 : (a.map fun x => (m - 1) * x % m).sum = g * m := h (m - 1) hcop
  have e1 : (a.map fun x => 1 * x % m) = (a.map fun x => x % m) := by
    apply List.map_congr_left
    intro x _
    rw [Nat.one_mul]
  have e2 : (a.map fun x => (m - 1) * x % m) = (a.map fun x => m - x % m) := by
    apply List.map_congr_left
    intro x hxa
    exact neg_one_mul_mod m x hm (hnz x hxa)
  rw [e1] at h1
  rw [e2, sum_map_msub m (by omega)] at h2
  have hle := sum_map_mod_le m (by omega) a
  have h2g : a.length * m = 2 * g * m := by rw [Nat.mul_assoc]; omega
  exact Nat.eq_of_mul_eq_mul_right (by omega) h2g

/-! ### §2 Proposition D: the AP character has constant grade (p+1)/2 -/

/-- Aoki's padded AP multiset {x, x+d, …, x+(p−1)d, m−px}, d = m/p, as reduced residues. -/
def apChar (m p x : Nat) : List Nat :=
  ((List.range p).map fun k => (x + k * (m / p)) % m) ++ [(m - p * x % m) % m]

/-- the mod-decomposition: (r + q·d) mod p·d = r + (q mod p)·d for r < d. -/
private lemma mod_decomp (p d r q : Nat) (hp : 0 < p) (hr : r < d) :
    (r + q * d) % (p * d) = r + q % p * d := by
  conv_lhs => rw [show q = q % p + p * (q / p) from (Nat.mod_add_div q p).symm]
  rw [show r + (q % p + p * (q / p)) * d = (r + q % p * d) + q / p * (p * d) by ring,
      Nat.add_mul_mod_self_right]
  have hqp : q % p < p := Nat.mod_lt _ hp
  have h1 : q % p * d ≤ (p - 1) * d := Nat.mul_le_mul_right d (by omega)
  have h2 : (p - 1) * d + d = p * d := by
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    simp [Nat.add_mul]
  exact Nat.mod_eq_of_lt (by omega)

private lemma affine_injOn (p c τ : Nat) (hτ : Nat.gcd τ p = 1) :
    Set.InjOn (fun k => (c + k * τ) % p) ↑(range p) := by
  intro k₁ hk₁ k₂ hk₂ he
  simp only [Finset.coe_range, Set.mem_Iio] at hk₁ hk₂
  have h1 : k₁ * τ ≡ k₂ * τ [MOD p] := Nat.ModEq.add_left_cancel' c he
  have h2 : k₁ ≡ k₂ [MOD p] :=
    Nat.ModEq.cancel_right_of_coprime (by rwa [Nat.gcd_comm]) h1
  have := h2  -- k₁ % p = k₂ % p
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hk₁, Nat.mod_eq_of_lt hk₂] at this

/-- affine reindexing: for gcd(τ, p) = 1, k ↦ (c + kτ) mod p permutes range p. -/
private lemma sum_affine_mod (p c τ : Nat) (hp : 0 < p) (hτ : Nat.gcd τ p = 1) :
    ∑ k ∈ range p, (c + k * τ) % p = ∑ k ∈ range p, k := by
  have hinj := affine_injOn p c τ hτ
  have himg : Finset.image (fun k => (c + k * τ) % p) (range p) = range p := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      simp only [Finset.mem_image] at hv
      obtain ⟨k, _, rfl⟩ := hv
      exact Finset.mem_range.mpr (Nat.mod_lt _ hp)
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ k ∈ range p, (c + k * τ) % p
      = ∑ v ∈ Finset.image (fun k => (c + k * τ) % p) (range p), v :=
        (Finset.sum_image (f := fun v => v) hinj).symm
    _ = ∑ k ∈ range p, k := by rw [himg]

/-- t·(m − w) ≡ −t·w: the reduced value is m − (t·w mod m), via the (m−1)-twist. -/
private lemma mul_msub_mod (m t w : Nat) (hm : 2 ≤ m) (hwm : w < m)
    (h : t * w % m ≠ 0) : t * (m - w) % m = m - t * w % m := by
  have e1 : t * (m - w) + t * w = m * t := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (le_of_lt hwm)]
    ring
  have e2 : (m - 1) * (t * w) + t * w = m * (t * w) := by
    conv_rhs => rw [show m = (m - 1) + 1 by omega]
    ring
  have h0 : t * (m - w) ≡ (m - 1) * (t * w) [MOD m] := by
    apply Nat.ModEq.add_right_cancel' (t * w)
    rw [e1, e2]
    calc m * t ≡ 0 [MOD m] := Nat.modEq_zero_iff_dvd.mpr ⟨t, rfl⟩
      _ ≡ m * (t * w) [MOD m] := (Nat.modEq_zero_iff_dvd.mpr ⟨t * w, rfl⟩).symm
  rw [show t * (m - w) % m = (m - 1) * (t * w) % m from h0]
  exact neg_one_mul_mod m (t * w) hm h

/-- PROPOSITION D (standard = AP), the grade computation: for odd p ∣ m and px ≢ 0 mod m,
    the padded AP multiset has constant grade (p+1)/2 — at EVERY unit t. -/
theorem apChar_gradeConst (p d x : Nat) (hp2 : 2 ≤ p) (hpodd : p % 2 = 1) (hd0 : 0 < d)
    (hx : p * x % (p * d) ≠ 0) :
    GradeConst (p * d) ((p + 1) / 2) (apChar (p * d) p x) := by
  have hp0 : 0 < p := by omega
  intro t ht
  -- coprimalities inherited from gcd(t, m) = 1
  have htp : Nat.gcd t p = 1 := Nat.Coprime.coprime_dvd_right ⟨d, rfl⟩ ht
  have htd : Nat.gcd t d = 1 := Nat.Coprime.coprime_dvd_right ⟨p, by ring⟩ ht
  -- x, t·x are units-free of d: their residues mod d are nonzero
  have hxd : x % d ≠ 0 := by
    intro h0
    exact hx (by rw [Nat.mul_mod_mul_left, h0, Nat.mul_zero])
  have hyd : t * x % d ≠ 0 := by
    intro h0
    have hdvd2 : d ∣ t * x := Nat.dvd_of_mod_eq_zero h0
    have hdx : d ∣ x := Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_comm.mp htd) hdvd2
    obtain ⟨c, rfl⟩ := hdx
    exact hxd (Nat.mul_mod_right d c)
  have hm2 : 2 ≤ p * d := by
    have h1 : p * x % (p * d) < p * d := Nat.mod_lt _ (Nat.mul_pos hp0 hd0)
    have h2 : 0 < p * x % (p * d) := Nat.pos_of_ne_zero hx
    omega
  -- unfold; the AP block and the padding term are summed separately
  unfold apChar
  rw [Nat.mul_div_cancel_left d hp0, List.map_append, List.sum_append, List.map_map]
  -- (a) the AP block
  have hAP : ((List.range p).map
        ((fun v => t * v % (p * d)) ∘ (fun k => (x + k * d) % (p * d)))).sum
      = p * (t * x % d) + p * (p - 1) / 2 * d := by
    have hb : ((List.range p).map
          ((fun v => t * v % (p * d)) ∘ (fun k => (x + k * d) % (p * d)))).sum
        = ∑ k ∈ range p, t * ((x + k * d) % (p * d)) % (p * d) := rfl
    rw [hb]
    have hpt : ∀ k ∈ range p,
        t * ((x + k * d) % (p * d)) % (p * d) = t * x % d + (t * x / d + k * t) % p * d := by
      intro k _
      rw [Nat.mul_mod_mod]
      have e : t * (x + k * d) = t * x % d + (t * x / d + k * t) * d := by
        have hy := Nat.mod_add_div (t * x) d
        set r := t * x % d with hr
        set q := t * x / d with hq
        rw [Nat.mul_add, ← hy]
        ring
      rw [e, mod_decomp p d _ _ hp0 (Nat.mod_lt _ hd0)]
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_range, smul_eq_mul, ← Finset.sum_mul,
        sum_affine_mod p (t * x / d) t hp0 htp, Finset.sum_range_id]
  rw [hAP]
  -- (b) the padding term −px
  have hw : p * x % (p * d) = p * (x % d) := Nat.mul_mod_mul_left p x d
  have hwlt : p * x % (p * d) < p * d := Nat.mod_lt _ (Nat.mul_pos hp0 hd0)
  have hw0 : 0 < p * x % (p * d) := Nat.pos_of_ne_zero hx
  have htw : t * (p * x % (p * d)) % (p * d) ≠ 0 := by
    rw [hw, show t * (p * (x % d)) = p * (t * (x % d)) by ring, Nat.mul_mod_mul_left]
    intro h0
    rcases Nat.mul_eq_zero.mp h0 with h | h
    · omega
    · rw [Nat.mul_mod_mod] at h
      exact hyd h
  have hLast : (([(p * d - p * x % (p * d)) % (p * d)]).map fun v => t * v % (p * d)).sum
      = p * d - p * (t * x % d) := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [Nat.mod_eq_of_lt (show p * d - p * x % (p * d) < p * d by omega)]
    rw [mul_msub_mod (p * d) t (p * x % (p * d)) hm2 hwlt htw]
    rw [hw, show t * (p * (x % d)) = p * (t * (x % d)) by ring, Nat.mul_mod_mul_left,
        Nat.mul_mod_mod]
  rw [hLast]
  -- (c) total: p·r + (p(p−1)/2)·d + (pd − p·r) = ((p+1)/2)·(pd)
  obtain ⟨u, rfl⟩ : ∃ u, p = 2 * u + 1 := ⟨p / 2, by omega⟩
  have e1 : (2 * u + 1) * (2 * u + 1 - 1) / 2 = (2 * u + 1) * u := by
    rw [show 2 * u + 1 - 1 = 2 * u by omega,
        show (2 * u + 1) * (2 * u) = 2 * ((2 * u + 1) * u) by ring]
    exact Nat.mul_div_cancel_left _ (by omega)
  have e2 : (2 * u + 1 + 1) / 2 = u + 1 := by omega
  rw [e1, e2]
  have hrlt : t * x % d < d := Nat.mod_lt _ hd0
  have hPlt : (2 * u + 1) * (t * x % d) < (2 * u + 1) * d :=
    (Nat.mul_lt_mul_left (by omega)).mpr hrlt
  rw [show (2 * u + 1) * u * d = (2 * u + 1) * d * u by ring,
      show (u + 1) * ((2 * u + 1) * d) = (2 * u + 1) * d * u + (2 * u + 1) * d by ring]
  omega

/-- grade 3 ⟺ p = 5 (odd p): the manuscript's "grade-3 standard classes exist iff 5 ∣ m". -/
theorem apChar_grade_three_iff (p : Nat) (hpodd : p % 2 = 1) :
    (p + 1) / 2 = 3 ↔ p = 5 := by omega

theorem apChar_length (m p x : Nat) : (apChar m p x).length = p + 1 := by
  simp [apChar]

/-- nonzero entries (the admissibility part of Prop D): every entry of the AP multiset is
    a nonzero residue. -/
theorem apChar_entries_nonzero (p d x : Nat) (hp0 : 0 < p) (hd0 : 0 < d)
    (hx : p * x % (p * d) ≠ 0) :
    ∀ v ∈ apChar (p * d) p x, v % (p * d) ≠ 0 := by
  have hxd : x % d ≠ 0 := by
    intro h0
    exact hx (by rw [Nat.mul_mod_mul_left, h0, Nat.mul_zero])
  have hm0 : 0 < p * d := Nat.mul_pos hp0 hd0
  intro v hv
  unfold apChar at hv
  rw [Nat.mul_div_cancel_left d hp0] at hv
  rcases List.mem_append.mp hv with hv | hv
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hv
    have e : (x + k * d) % (p * d) = x % d + (x / d + k) % p * d := by
      have e0 : x + k * d = x % d + (x / d + k) * d := by
        have hy := Nat.mod_add_div x d
        set r := x % d with hr
        set q := x / d with hq
        rw [← hy]
        ring
      rw [e0, mod_decomp p d _ _ hp0 (Nat.mod_lt _ hd0)]
    rw [Nat.mod_eq_of_lt (Nat.mod_lt _ hm0), e]
    omega
  · rw [List.mem_singleton.mp hv]
    have hwlt : p * x % (p * d) < p * d := Nat.mod_lt _ hm0
    have hw0 : 0 < p * x % (p * d) := Nat.pos_of_ne_zero hx
    rw [Nat.mod_eq_of_lt (show p * d - p * x % (p * d) < p * d by omega),
        Nat.mod_eq_of_lt (show p * d - p * x % (p * d) < p * d by omega)]
    omega

/-- consistency capstone: the two theorems agree — the AP multiset's length p+1 equals
    2·((p+1)/2), as forced by `gradeConst_length` applied to `apChar_gradeConst`. -/
theorem apChar_length_consistency (p d x : Nat) (hp2 : 2 ≤ p) (hpodd : p % 2 = 1)
    (hd0 : 0 < d) (hx : p * x % (p * d) ≠ 0) :
    (apChar (p * d) p x).length = 2 * ((p + 1) / 2) := by
  have hm2 : 2 ≤ p * d := by
    have h1 : p * x % (p * d) < p * d := Nat.mod_lt _ (Nat.mul_pos (by omega) hd0)
    have h2 : 0 < p * x % (p * d) := Nat.pos_of_ne_zero hx
    omega
  exact gradeConst_length (p * d) ((p + 1) / 2) hm2 _
    (apChar_entries_nonzero p d x (by omega) hd0 hx)
    (apChar_gradeConst p d x hp2 hpodd hd0 hx)

/-! ### trust-base receipts: standard axioms only (no compiler, no native_decide) -/

#print axioms gradeConst_length
#print axioms apChar_gradeConst
#print axioms apChar_length_consistency

end BoundaryForms
