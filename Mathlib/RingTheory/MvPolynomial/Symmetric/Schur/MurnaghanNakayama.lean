/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Alternant.PowerSum
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.DualPieriSchur

/-!
# The Murnaghan–Nakayama rule

Following `theories/MPoly/MurnaghanNakayama.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove the Murnaghan–Nakayama rule
in its one step form: for a partition `lam` and `r ≥ 1`,

`p_r * s_lam = ∑ (-1) ^ height * s_mu`,

the sum being over the shapes `mu` obtained from `lam` by adding a *ribbon* (a border
strip) of `r` boxes, and `height` being the number of rows of the ribbon minus one.

Adding a ribbon is described here in the language of the bialternant formula: the
staircase shift `lam + delta` of `lam` is a strictly decreasing vector, and adding `r` to
its entry in row `k` and sorting the result yields the staircase shift of `mu`.  Sorting
moves the modified entry from row `k` to a row `mnPos lam r k ≤ k`, which is the first row
`i` with `lam i + (k - i) ≤ lam k + r`, and the resulting shape is

`mu i = lam i` for `i < j` and for `i > k`, `mu j = lam k + r - (k - j)`, and
`mu i = lam (i-1) + 1` for `j < i ≤ k`, where `j = mnPos lam r k`;

this is exactly the shape obtained from `lam` by adding a ribbon of `r` boxes occupying
the rows `j, …, k`, of height `k - j`.  The step is possible (`MvPolynomial.MNAddable`) exactly
when the modified entry does not collide with another entry of the vector.

## Main definitions and results

* `MvPolynomial.mnPos lam r k` : the first row of the ribbon added in row `k`.
* `MvPolynomial.MNAddable lam r k` : the ribbon can be added in row `k`.
* `MvPolynomial.mnShape lam r k` : the resulting shape.
* `MvPolynomial.mnHeight lam r k` : the height `k - mnPos lam r k` of the ribbon.
* `MvPolynomial.isPart_mnShape`, `MvPolynomial.sum_mnShape`, `MvPolynomial.included_mnShape` :
  the resulting shape is a partition of `|lam| + r` containing `lam`.
* `MvPolynomial.psum_mul_schurPoly` : **the Murnaghan–Nakayama rule**.
-/

@[expose] public section

namespace MvPolynomial

open List MvPolynomial Finset

variable {m : ℕ} {R : Type*} [CommRing R]

/-! ### The position of the ribbon -/

/-- If a predicate on `ℕ` is downward closed, the elements of `range n` satisfying it form
an initial segment. -/
lemma filter_range_eq_range_card {P : ℕ → Prop} [DecidablePred P]
    (hdown : ∀ i i', i' ≤ i → P i → P i') (n : ℕ) :
    (Finset.range n).filter P = Finset.range (((Finset.range n).filter P).card) := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : P n
    · have hall : (Finset.range (n + 1)).filter P = Finset.range (n + 1) :=
        Finset.filter_true_of_mem fun i hi =>
          hdown n i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hn
      rw [hall, Finset.card_range]
    · rw [Finset.range_add_one, Finset.filter_insert, ite_eq_right hn, ih, Finset.card_range]

/-- The row in which the entry of row `k` lands after adding `r` to it and sorting:
the number of rows `i ≤ k` with `lam k + r + i < lam i + k`. -/
def mnPos (lam : List ℕ) (r k : ℕ) : ℕ :=
  ((Finset.range (k + 1)).filter (fun i => lam.getD k 0 + r + i < lam.getD i 0 + k)).card

variable {lam : List ℕ} {r k : ℕ}

lemma filter_range_mnPos (hlam : IsPart lam) (r k : ℕ) :
    (Finset.range (k + 1)).filter (fun i => lam.getD k 0 + r + i < lam.getD i 0 + k)
      = Finset.range (mnPos lam r k) := by
  refine filter_range_eq_range_card (fun i i' hi' hi => ?_) _
  have := hlam.getD_antitone hi'
  omega

/-- Characterisation of the rows above the ribbon. -/
lemma lt_mnPos_iff (hlam : IsPart lam) {i : ℕ} (hi : i ≤ k) :
    i < mnPos lam r k ↔ lam.getD k 0 + r + i < lam.getD i 0 + k := by
  have h := filter_range_mnPos (r := r) hlam k
  constructor
  · intro hlt
    have : i ∈ (Finset.range (k + 1)).filter
        (fun i => lam.getD k 0 + r + i < lam.getD i 0 + k) := by
      rw [h]; exact Finset.mem_range.2 hlt
    exact (Finset.mem_filter.1 this).2
  · intro hP
    have : i ∈ (Finset.range (k + 1)).filter
        (fun i => lam.getD k 0 + r + i < lam.getD i 0 + k) :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hP⟩
    rw [h] at this
    exact Finset.mem_range.1 this

/-- The ribbon starts in a row above the row where it was added. -/
lemma mnPos_le (hlam : IsPart lam) (r k : ℕ) : mnPos lam r k ≤ k := by
  by_contra hcon
  have hk : k < mnPos lam r k := by omega
  have := (lt_mnPos_iff (r := r) hlam (le_refl k)).1 hk
  omega

/-- The height of the ribbon: the number of its rows minus one. -/
def mnHeight (lam : List ℕ) (r k : ℕ) : ℕ := k - mnPos lam r k

/-- Adding a ribbon of `r` boxes ending in row `k` of `lam` is possible when the entry
`lam k + r` of the shifted vector collides with no other entry. -/
def MNAddable (lam : List ℕ) (r k : ℕ) : Prop :=
  ∀ i < k, lam.getD i 0 + k ≠ lam.getD k 0 + r + i

instance (lam : List ℕ) (r k : ℕ) : Decidable (MNAddable lam r k) :=
  inferInstanceAs (Decidable (∀ i < k, _))

/-- The height of the ribbon is at most the number of boxes it adds in row `k`. -/
lemma mnHeight_le (hlam : IsPart lam) (hr : 0 < r) :
    mnHeight lam r k ≤ lam.getD k 0 + r := by
  rw [mnHeight]
  rcases Nat.eq_or_lt_of_le (mnPos_le (r := r) hlam k) with hjk | hjk
  · omega
  · have h1 : ¬ (lam.getD k 0 + r + mnPos lam r k < lam.getD (mnPos lam r k) 0 + k) := by
      intro hcon
      exact absurd ((lt_mnPos_iff (r := r) hlam (le_of_lt hjk)).2 hcon) (lt_irrefl _)
    omega

/-! ### The shape obtained by adding a ribbon -/

/-- The rows of the shape obtained from `lam` by adding a ribbon of `r` boxes ending in
row `k`. -/
def mnFn (lam : List ℕ) (r k : ℕ) : ℕ → ℕ := fun i =>
  if i < mnPos lam r k then lam.getD i 0
  else if i = mnPos lam r k then lam.getD k 0 + r - (k - mnPos lam r k)
  else if i ≤ k then lam.getD (i - 1) 0 + 1
  else lam.getD i 0

lemma mnFn_of_lt {i : ℕ} (h : i < mnPos lam r k) : mnFn lam r k i = lam.getD i 0 := by
  rw [mnFn, ite_eq_left h]

lemma mnFn_mnPos :
    mnFn lam r k (mnPos lam r k) = lam.getD k 0 + r - (k - mnPos lam r k) := by
  rw [mnFn, ite_eq_right (lt_irrefl _), ite_eq_left rfl]

lemma mnFn_of_mid {i : ℕ} (h1 : mnPos lam r k < i) (h2 : i ≤ k) :
    mnFn lam r k i = lam.getD (i - 1) 0 + 1 := by
  rw [mnFn, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h2]

lemma mnFn_of_gt (hlam : IsPart lam) {i : ℕ} (h : k < i) :
    mnFn lam r k i = lam.getD i 0 := by
  have := mnPos_le (r := r) hlam k
  rw [mnFn, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The shape obtained from `lam` by adding a ribbon of `r` boxes ending in row `k`. -/
def mnShape (lam : List ℕ) (r k : ℕ) : List ℕ :=
  shapeOfFn (max (k + 1) lam.length) (mnFn lam r k)

lemma length_mnShape_le (lam : List ℕ) (r k : ℕ) :
    (mnShape lam r k).length ≤ max (k + 1) lam.length :=
  length_shapeOfFn_le _ _

lemma getD_mnShape (hlam : IsPart lam) (r k i : ℕ) :
    (mnShape lam r k).getD i 0 = mnFn lam r k i := by
  rw [mnShape, getD_shapeOfFn]
  by_cases hi : i < max (k + 1) lam.length
  · rw [ite_eq_left hi]
  · rw [ite_eq_right hi, mnFn_of_gt hlam (show k < i by omega),
      List.getD_eq_default _ _ (by omega)]

/-- The shape obtained by adding a ribbon is a partition. -/
lemma isPart_mnShape (hlam : IsPart lam) (hr : 0 < r) (hadd : MNAddable lam r k) :
    IsPart (mnShape lam r k) := by
  refine isPart_shapeOfFn fun i => ?_
  have hjk : mnPos lam r k ≤ k := mnPos_le (r := r) hlam k
  have hsub : k - mnPos lam r k ≤ lam.getD k 0 + r := mnHeight_le hlam hr
  rcases lt_trichotomy (i + 1) (mnPos lam r k) with hlt | heq | hgt
  · rw [mnFn_of_lt hlt, mnFn_of_lt (by omega)]
    exact hlam.getD_antitone (Nat.le_succ i)
  · -- `i + 1` is the first row of the ribbon
    rw [heq, mnFn_mnPos, mnFn_of_lt (show i < mnPos lam r k by omega)]
    have hP : lam.getD k 0 + r + i < lam.getD i 0 + k :=
      (lt_mnPos_iff (r := r) hlam (by omega)).1 (by omega)
    omega
  · rcases eq_or_ne i (mnPos lam r k) with hij | hij
    · -- `i` is the first row of the ribbon
      rw [hij, mnFn_mnPos]
      rcases Nat.eq_or_lt_of_le hjk with hjk' | hjk'
      · rw [mnFn_of_gt hlam (show k < mnPos lam r k + 1 by omega)]
        have := hlam.getD_antitone (show k ≤ mnPos lam r k + 1 by omega)
        omega
      · rw [mnFn_of_mid (show mnPos lam r k < mnPos lam r k + 1 by omega) (by omega),
          Nat.add_sub_cancel]
        have h1 : ¬ (lam.getD k 0 + r + mnPos lam r k < lam.getD (mnPos lam r k) 0 + k) := by
          intro hcon
          exact absurd ((lt_mnPos_iff (r := r) hlam (le_of_lt hjk')).2 hcon) (lt_irrefl _)
        have h2 := hadd (mnPos lam r k) hjk'
        omega
    · -- `i` is below the first row of the ribbon
      have hji : mnPos lam r k < i := by omega
      by_cases hik : i + 1 ≤ k
      · rw [mnFn_of_mid (by omega) hik, mnFn_of_mid hji (by omega), Nat.add_sub_cancel]
        have := hlam.getD_antitone (show i - 1 ≤ i by omega)
        omega
      · by_cases hik' : i ≤ k
        · rw [mnFn_of_gt hlam (by omega), mnFn_of_mid hji hik']
          have := hlam.getD_antitone (show i - 1 ≤ i + 1 by omega)
          omega
        · rw [mnFn_of_gt hlam (by omega), mnFn_of_gt hlam (by omega)]
          exact hlam.getD_antitone (Nat.le_succ i)

/-! ### The shifted vector of the new shape -/

/-- Adding a ribbon in row `k` corresponds, on the staircase shifted vectors, to adding
`r` to the entry of row `k` and sorting the result. -/
lemma partVec_mnShape (hlam : IsPart lam) (hr : 0 < r) (k' : Fin m)
    (hk' : (k' : ℕ) = k) :
    partVec m (mnShape lam r k)
      = moveVec (Function.update (partVec m lam) k' (partVec m lam k' + r))
          (mnPos lam r k) k' := by
  have hjk : mnPos lam r k ≤ k := mnPos_le (r := r) hlam k
  have hsub : k - mnPos lam r k ≤ lam.getD k 0 + r := mnHeight_le hlam hr
  have hkm : k < m := by rw [← hk']; exact k'.isLt
  funext i
  rw [partVec_apply, getD_mnShape hlam, moveVec_apply, hk']
  by_cases hij : (i : ℕ) = mnPos lam r k
  · rw [ite_eq_left hij, hij, mnFn_mnPos, Function.update_self, partVec_apply, hk']
    omega
  rw [ite_eq_right hij]
  by_cases hmid : mnPos lam r k < (i : ℕ) ∧ (i : ℕ) ≤ k
  · rw [ite_eq_left hmid, mnFn_of_mid hmid.1 hmid.2]
    have hne : (⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ : Fin m) ≠ k' := by
      intro hcon
      have := congrArg (fun x : Fin m => (x : ℕ)) hcon
      simp only at this
      omega
    rw [Function.update_of_ne hne, partVec_apply]
    have hik : (i : ℕ) ≤ k := hmid.2
    simp only []
    omega
  rw [ite_eq_right hmid]
  have hik : (i : ℕ) ≠ k := by
    intro hcon
    rcases Nat.lt_or_ge (mnPos lam r k) (i : ℕ) with h | h
    · exact hmid ⟨h, by omega⟩
    · omega
  have hne : i ≠ k' := by
    intro hcon
    exact hik (by rw [← hk', hcon])
  rw [Function.update_of_ne hne, partVec_apply]
  by_cases hlt : (i : ℕ) < mnPos lam r k
  · rw [mnFn_of_lt hlt]
  · rw [mnFn_of_gt hlam (show k < (i : ℕ) by omega)]

/-! ### The size of the new shape -/

/-- Adding a ribbon of `r` boxes adds `r` to the size of the shape. -/
lemma sum_mnShape (hlam : IsPart lam) (hr : 0 < r) :
    (mnShape lam r k).sum = lam.sum + r := by
  set m := max (k + 1) lam.length with hm
  have hlen : lam.length ≤ m := le_max_right _ _
  have hkm : k < m := lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _)
  set k' : Fin m := ⟨k, hkm⟩ with hk'def
  have hk' : (k' : ℕ) = k := rfl
  have hmulen : (mnShape lam r k).length ≤ m := length_mnShape_le lam r k
  have hvec := partVec_mnShape hlam hr k' hk'
  have h1 : ∑ i, partVec m (mnShape lam r k) i
      = (mnShape lam r k).sum + ∑ i ∈ Finset.range m, (m - 1 - i) := sum_partVec hmulen
  have h2 : ∑ i, partVec m lam i = lam.sum + ∑ i ∈ Finset.range m, (m - 1 - i) :=
    sum_partVec hlen
  have h3 : ∑ i, moveVec (Function.update (partVec m lam) k' (partVec m lam k' + r))
        (mnPos lam r k) k' i
      = ∑ i, Function.update (partVec m lam) k' (partVec m lam k' + r) i :=
    sum_moveVec _ _ _ (by rw [hk']; exact mnPos_le (r := r) hlam k)
  have h4 : ∑ i, Function.update (partVec m lam) k' (partVec m lam k' + r) i
      = (∑ i, partVec m lam i) + r := by
    have hupd : ∀ i : Fin m, Function.update (partVec m lam) k' (partVec m lam k' + r) i
        = partVec m lam i + (if i = k' then r else 0) := by
      intro i
      by_cases h : i = k'
      · subst h; simp
      · simp [h]
    simp only [hupd, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ k' (fun _ => r)]
    simp
  rw [hvec, h3, h4, h2] at h1
  omega

/-- The shape obtained by adding a ribbon contains the original shape. -/
lemma included_mnShape (hlam : IsPart lam) (hr : 0 < r) (hadd : MNAddable lam r k) :
    Included lam (mnShape lam r k) := by
  have hjk : mnPos lam r k ≤ k := mnPos_le (r := r) hlam k
  have hsub : k - mnPos lam r k ≤ lam.getD k 0 + r := mnHeight_le hlam hr
  refine (hlam.included_iff_getD).2 fun i => ?_
  rw [getD_mnShape hlam]
  by_cases hlt : i < mnPos lam r k
  · rw [mnFn_of_lt hlt]
  by_cases hij : i = mnPos lam r k
  · rw [hij, mnFn_mnPos]
    rcases Nat.eq_or_lt_of_le hjk with hjk' | hjk'
    · rw [hjk']
      omega
    · have h1 : ¬ (lam.getD k 0 + r + mnPos lam r k < lam.getD (mnPos lam r k) 0 + k) := by
        intro hcon
        exact absurd ((lt_mnPos_iff (r := r) hlam (le_of_lt hjk')).2 hcon) (lt_irrefl _)
      have h2 := hadd (mnPos lam r k) hjk'
      omega
  by_cases hik : i ≤ k
  · rw [mnFn_of_mid (by omega) hik]
    have := hlam.getD_antitone (show i - 1 ≤ i by omega)
    omega
  · rw [mnFn_of_gt hlam (by omega)]

/-! ### The Murnaghan–Nakayama rule for alternants -/

lemma alt_update_partVec_of_not_addable (k' : Fin m)
    (hk' : (k' : ℕ) = k) (hadd : ¬ MNAddable lam r k) :
    alt m R (Function.update (partVec m lam) k' (partVec m lam k' + r)) = 0 := by
  rw [MNAddable] at hadd
  push Not at hadd
  obtain ⟨i, hik, hi⟩ := hadd
  have him : i < m := by rw [← hk'] at hik; exact lt_trans hik k'.isLt
  refine alt_eq_zero_of_eq (i := (⟨i, him⟩ : Fin m)) (j := k') ?_ ?_
  · intro hcon
    have := congrArg (fun x : Fin m => (x : ℕ)) hcon
    simp only at this
    omega
  · have hne : (⟨i, him⟩ : Fin m) ≠ k' := by
      intro hcon
      have := congrArg (fun x : Fin m => (x : ℕ)) hcon
      simp only at this
      omega
    rw [Function.update_of_ne hne, Function.update_self, partVec_apply, partVec_apply, hk']
    simp only
    omega

/-- The Murnaghan–Nakayama rule for alternants: multiplying the alternant of the shifted
vector of `lam` by the power sum `p_r` gives the signed sum of the alternants of the
shapes obtained by adding a ribbon of `r` boxes. -/
theorem psum_mul_alt_partVec (hlam : IsPart lam) (hr : 0 < r) :
    psum (Fin m) R r * alt m R (partVec m lam)
      = ∑ k : Fin m, if MNAddable lam r (k : ℕ) then
          ((-1 : ℤ) ^ mnHeight lam r (k : ℕ)) • alt m R (partVec m (mnShape lam r (k : ℕ)))
        else 0 := by
  rw [psum_mul_alt]
  refine Finset.sum_congr rfl fun k' _ => ?_
  by_cases hadd : MNAddable lam r (k' : ℕ)
  · rw [ite_eq_left hadd,
      alt_moveVec (R := R) _ (mnPos lam r (k' : ℕ)) k' (mnPos_le (r := r) hlam _),
      ← partVec_mnShape hlam hr k' rfl]
    rfl
  · rw [ite_eq_right hadd]
    exact alt_update_partVec_of_not_addable k' rfl hadd

/-! ### The Murnaghan–Nakayama rule -/

/-- The Murnaghan–Nakayama rule over `ℤ`, obtained by cancelling the Vandermonde
alternant. -/
theorem psum_mul_schurPoly_int (hlam : IsPart lam) (hlen : lam.length ≤ m) (hr : 0 < r) :
    psum (Fin m) ℤ r * schurPoly (Fin m) ℤ lam
      = ∑ k : Fin m, if MNAddable lam r (k : ℕ) then
          ((-1 : ℤ) ^ mnHeight lam r (k : ℕ)) • schurPoly (Fin m) ℤ (mnShape lam r (k : ℕ))
        else 0 := by
  classical
  refine mul_right_cancel₀ (altPart_nil_ne_zero m) ?_
  have hdelta : altPart m ℤ [] = alt m ℤ (partVec m ([] : List ℕ)) :=
    altPart_of_le (by simp)
  have hlhs : psum (Fin m) ℤ r * schurPoly (Fin m) ℤ lam * altPart m ℤ []
      = psum (Fin m) ℤ r * alt m ℤ (partVec m lam) := by
    rw [hdelta, alt_partVec_eq_schurPoly_mul hlam hlen, mul_assoc]
  have hrhs : (∑ k : Fin m, if MNAddable lam r (k : ℕ) then
        ((-1 : ℤ) ^ mnHeight lam r (k : ℕ)) • schurPoly (Fin m) ℤ (mnShape lam r (k : ℕ))
      else 0) * altPart m ℤ []
      = ∑ k : Fin m, if MNAddable lam r (k : ℕ) then
          ((-1 : ℤ) ^ mnHeight lam r (k : ℕ)) • alt m ℤ (partVec m (mnShape lam r (k : ℕ)))
        else 0 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k' _ => ?_
    by_cases hadd : MNAddable lam r (k' : ℕ)
    · rw [ite_eq_left hadd, ite_eq_left hadd, smul_mul_assoc, hdelta,
        alt_partVec_eq_schurPoly_mul (isPart_mnShape hlam hr hadd)
          (le_trans (length_mnShape_le _ _ _) (max_le k'.isLt hlen))]
    · rw [ite_eq_right hadd, ite_eq_right hadd, zero_mul]
  rw [hlhs, hrhs]
  exact psum_mul_alt_partVec hlam hr

/-- **The Murnaghan–Nakayama rule**: the product of a Schur polynomial `s_lam` by the
power sum `p_r` is the signed sum of the Schur polynomials of the shapes obtained from
`lam` by adding a ribbon of `r` boxes, the sign being `(-1)` to the height of the
ribbon. -/
theorem psum_mul_schurPoly (hlam : IsPart lam) (hlen : lam.length ≤ m) (hr : 0 < r) :
    psum (Fin m) R r * schurPoly (Fin m) R lam
      = ∑ k : Fin m, if MNAddable lam r (k : ℕ) then
          ((-1 : ℤ) ^ mnHeight lam r (k : ℕ)) • schurPoly (Fin m) R (mnShape lam r (k : ℕ))
        else 0 := by
  classical
  have h := congrArg (MvPolynomial.map (Int.castRingHom R))
    (psum_mul_schurPoly_int (m := m) hlam hlen hr)
  rw [map_mul, map_schurPoly, map_sum] at h
  have hpsum : MvPolynomial.map (Int.castRingHom R) (psum (Fin m) ℤ r) = psum (Fin m) R r := by
    rw [psum, psum, map_sum]
    simp
  rw [hpsum] at h
  rw [h]
  refine Finset.sum_congr rfl fun k' _ => ?_
  by_cases hadd : MNAddable lam r (k' : ℕ)
  · rw [ite_eq_left hadd, ite_eq_left hadd, map_zsmul, map_schurPoly]
  · rw [ite_eq_right hadd, ite_eq_right hadd, map_zero]

end MvPolynomial
