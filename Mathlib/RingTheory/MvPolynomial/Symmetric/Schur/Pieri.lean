/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Shape.Finset
public import Mathlib.Combinatorics.Young.Shape.HorizontalDiamond
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.Branching

/-!
# The Pieri rule

The Pieri rule expresses the product of a Schur polynomial by a complete homogeneous
symmetric polynomial as a sum of Schur polynomials, over the shapes obtained by adding a
horizontal strip:
`s_rho * h_r = ∑_{lam / rho a horizontal strip of size r} s_lam`.

The proof is by induction on the number of variables.  The branching rule
`MvPolynomial.schurPoly_branching` splits off the last variable on both sides, and the
combinatorial input is the diamond identity `Young.card_upDiamond_eq_card_downDiamondLe`.

## Main results

* `MvPolynomial.schurPoly_mul_hsymm` : the Pieri rule.
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial

variable {R : Type*} [CommRing R]

/-! ### One-row shapes -/

/-- The one-row shape with `k` boxes (the empty shape when `k = 0`). -/
def rowShape (k : ℕ) : List ℕ := if k = 0 then [] else [k]

lemma isPart_rowShape (k : ℕ) : IsPart (rowShape k) := by
  rw [rowShape]
  split_ifs with h
  · exact isPart_nil
  · exact ⟨by simpa using Nat.one_le_iff_ne_zero.2 h, isPart_nil⟩

@[simp] lemma sum_rowShape (k : ℕ) : (rowShape k).sum = k := by
  rw [rowShape]
  split_ifs with h
  · simp [h]
  · simp

lemma schurPoly_rowShape (σ : Type*) [Fintype σ] [LinearOrder σ] (R : Type*) [CommRing R]
    (k : ℕ) : schurPoly σ R (rowShape k) = hsymm σ R k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [show rowShape 0 = ([] : List ℕ) from rfl, schurPoly_nil, hsymm_zero]
  · rw [show rowShape k = [k] from ite_eq_right (by omega), schurPoly_row hk]

lemma getD_rowShape (k i : ℕ) : (rowShape k).getD i 0 = if i = 0 then k else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [rowShape]
  · rw [rowShape, ite_eq_right (by omega)]
    cases i with
    | zero => simp
    | succ j => simp

lemma length_rowShape_le (k : ℕ) : (rowShape k).length ≤ 1 := by
  rw [rowShape]
  split_ifs <;> simp

/-- Adding a horizontal strip to a one-row shape gives a longer one-row shape. -/
lemma horizStrip_rowShape {j r : ℕ} (h : j ≤ r) : HorizStrip (rowShape r) (rowShape j) := by
  refine ⟨(isPart_rowShape j).included_iff_getD.2 fun i => ?_, fun i => ?_⟩
  · rw [getD_rowShape, getD_rowShape]
    split_ifs <;> omega
  · rw [getD_rowShape, getD_rowShape, ite_eq_right (Nat.succ_ne_zero i)]
    omega

/-- A partition contained in a one-row shape is a one-row shape. -/
lemma eq_rowShape_of_included {nu : List ℕ} {r : ℕ} (hnu : IsPart nu)
    (h : Included nu (rowShape r)) : nu = rowShape nu.sum := by
  have hlen : nu.length ≤ 1 := le_trans h.length_le (length_rowShape_le r)
  match nu, hlen with
  | [], _ => simp [rowShape]
  | [a], _ =>
      have ha : 0 < a := hnu.headD_pos (by simp)
      have hs : [a].sum = a := by simp
      rw [hs, rowShape, ite_eq_right (by omega)]

/-! ### The branching rule in the finite-set formulation -/

lemma schurPoly_branching' (m : ℕ) {lam : List ℕ} (hlam : IsPart lam) :
    schurPoly (Fin (m + 1)) R lam
      = ∑ nu ∈ partFinsetLe lam.sum, if HorizStrip lam nu then
          rename Fin.castSucc (schurPoly (Fin m) R nu) * X (Fin.last m) ^ (lam.sum - nu.sum)
        else 0 := by
  rw [schurPoly_branching lam hlam, sum_partFinsetLe_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum_subtype_eq_sum_partFinset k (fun nu => if HorizStrip lam nu then
    rename Fin.castSucc (schurPoly (Fin m) R nu) * X (Fin.last m) ^ (lam.sum - k) else 0)]
  exact Finset.sum_congr rfl fun nu hnu => by rw [(mem_partFinset.1 hnu).2]

/-- The branching rule for the complete homogeneous symmetric polynomials. -/
lemma hsymm_branching (m r : ℕ) :
    hsymm (Fin (m + 1)) R r
      = ∑ j ∈ Finset.range (r + 1),
          rename Fin.castSucc (hsymm (Fin m) R j) * X (Fin.last m) ^ (r - j) := by
  classical
  rw [← schurPoly_rowShape (Fin (m + 1)) R r, schurPoly_branching' m (isPart_rowShape r),
    sum_rowShape, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun nu => nu.sum) (fun j => rowShape j) (fun nu hnu => ?_)
    (fun j hj => ?_) (fun nu hnu => ?_) (fun j _ => sum_rowShape j) (fun nu hnu => ?_)
  · rw [Finset.mem_filter, mem_partFinsetLe] at hnu
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hnu.1.2)
  · rw [Finset.mem_range] at hj
    rw [Finset.mem_filter, mem_partFinsetLe, sum_rowShape]
    exact ⟨⟨isPart_rowShape j, by omega⟩, horizStrip_rowShape (by omega)⟩
  · rw [Finset.mem_filter, mem_partFinsetLe] at hnu
    exact (eq_rowShape_of_included hnu.1.1 hnu.2.included).symm
  · rw [Finset.mem_filter, mem_partFinsetLe] at hnu
    have hnueq : nu = rowShape nu.sum := eq_rowShape_of_included hnu.1.1 hnu.2.included
    rw [show schurPoly (Fin m) R nu = hsymm (Fin m) R nu.sum by
      rw [hnueq, sum_rowShape, schurPoly_rowShape]]

/-! ### The two sides of the Pieri rule in a common form -/

/-- Comparing a cardinality of a set of lists with the cardinality of a finite set. -/
lemma card_set_eq_card_finset {s : Set (List ℕ)} {t : Finset (List ℕ)} (h : s = ↑t) :
    Nat.card s = t.card := by
  rw [h, Nat.card_coe_set_eq, Set.ncard_coe_finset]

lemma pieri_lhs (m : ℕ)
    (IH : ∀ {sigma : List ℕ}, IsPart sigma → ∀ j : ℕ,
      schurPoly (Fin m) R sigma * hsymm (Fin m) R j
        = ∑ tau ∈ partFinset (sigma.sum + j),
            if HorizStrip tau sigma then schurPoly (Fin m) R tau else 0)
    {rho : List ℕ} (hrho : IsPart rho) (r : ℕ) :
    schurPoly (Fin (m + 1)) R rho * hsymm (Fin (m + 1)) R r
      = ∑ tau ∈ partFinsetLe (rho.sum + r),
          Nat.card (downDiamondLe rho tau r) •
            (rename Fin.castSucc (schurPoly (Fin m) R tau)
              * X (Fin.last m) ^ (rho.sum + r - tau.sum)) := by
  classical
  have step : ∀ sigma ∈ partFinsetLe rho.sum, ∀ j ∈ Finset.range (r + 1),
      (if HorizStrip rho sigma then rename Fin.castSucc (schurPoly (Fin m) R sigma)
          * X (Fin.last m) ^ (rho.sum - sigma.sum) else 0)
        * (rename Fin.castSucc (hsymm (Fin m) R j) * X (Fin.last m) ^ (r - j))
      = ∑ tau ∈ partFinsetLe (rho.sum + r),
          if HorizStrip rho sigma ∧ HorizStrip tau sigma ∧ tau.sum = sigma.sum + j then
            rename Fin.castSucc (schurPoly (Fin m) R tau)
              * X (Fin.last m) ^ (rho.sum + r - tau.sum)
          else 0 := by
    intro sigma hsigma j hj
    obtain ⟨hsp, hssum⟩ := mem_partFinsetLe.1 hsigma
    have hjr : j ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    by_cases hstrip : HorizStrip rho sigma
    · rw [ite_eq_left hstrip]
      have hprod : (rename Fin.castSucc (schurPoly (Fin m) R sigma)
            * X (Fin.last m) ^ (rho.sum - sigma.sum))
          * ((rename Fin.castSucc (hsymm (Fin m) R j) : MvPolynomial (Fin (m + 1)) R)
            * X (Fin.last m) ^ (r - j))
          = rename Fin.castSucc (schurPoly (Fin m) R sigma * hsymm (Fin m) R j)
            * X (Fin.last m) ^ (rho.sum - sigma.sum + (r - j)) := by
        rw [map_mul, pow_add]
        ring
      rw [hprod, IH hsp j, map_sum, Finset.sum_mul,
        sum_partFinset_eq_sum_partFinsetLe (show sigma.sum + j ≤ rho.sum + r by omega)]
      refine Finset.sum_congr rfl fun tau _ => ?_
      have hrn : (rename (Fin.castSucc : Fin m → Fin (m + 1))
            (if HorizStrip tau sigma then schurPoly (Fin m) R tau else 0)
              : MvPolynomial (Fin (m + 1)) R)
          = if HorizStrip tau sigma then rename Fin.castSucc (schurPoly (Fin m) R tau) else 0 := by
        split_ifs
        · rfl
        · exact map_zero _
      by_cases htsum : tau.sum = sigma.sum + j
      · rw [ite_eq_left htsum, hrn]
        by_cases hts : HorizStrip tau sigma
        · rw [ite_eq_left hts, ite_eq_left ⟨hstrip, hts, htsum⟩,
            show rho.sum + r - tau.sum = rho.sum - sigma.sum + (r - j) by omega]
        · rw [ite_eq_right hts, ite_eq_right (fun h => hts h.2.1), zero_mul]
      · rw [ite_eq_right htsum, ite_eq_right (fun h => htsum h.2.2)]
    · rw [ite_eq_right hstrip, zero_mul, Finset.sum_eq_zero]
      intro tau _
      rw [ite_eq_right (fun h => hstrip h.1)]
  have expand : schurPoly (Fin (m + 1)) R rho * hsymm (Fin (m + 1)) R r
      = ∑ sigma ∈ partFinsetLe rho.sum, ∑ j ∈ Finset.range (r + 1),
          ∑ tau ∈ partFinsetLe (rho.sum + r),
            if HorizStrip rho sigma ∧ HorizStrip tau sigma ∧ tau.sum = sigma.sum + j then
              rename Fin.castSucc (schurPoly (Fin m) R tau)
                * X (Fin.last m) ^ (rho.sum + r - tau.sum)
            else 0 := by
    rw [schurPoly_branching' m hrho, hsymm_branching m r, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun sigma hs => Finset.sum_congr rfl fun j hj => step sigma hs j hj
  rw [expand, Finset.sum_congr rfl (fun sigma _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl fun tau htau => ?_
  -- the sum over `j` has at most one nonzero term
  have hjsum : ∀ sigma ∈ partFinsetLe rho.sum,
      (∑ j ∈ Finset.range (r + 1),
        if HorizStrip rho sigma ∧ HorizStrip tau sigma ∧ tau.sum = sigma.sum + j then
          rename Fin.castSucc (schurPoly (Fin m) R tau)
            * X (Fin.last m) ^ (rho.sum + r - tau.sum) else 0)
      = if HorizStrip rho sigma ∧ HorizStrip tau sigma ∧ tau.sum ≤ sigma.sum + r then
          rename Fin.castSucc (schurPoly (Fin m) R tau)
            * X (Fin.last m) ^ (rho.sum + r - tau.sum) else 0 := by
    intro sigma _
    by_cases hc : HorizStrip rho sigma ∧ HorizStrip tau sigma ∧ tau.sum ≤ sigma.sum + r
    · have hsigtau : sigma.sum ≤ tau.sum := hc.2.1.included.sum_le
      rw [ite_eq_left hc, Finset.sum_eq_single (tau.sum - sigma.sum)]
      · rw [ite_eq_left ⟨hc.1, hc.2.1, by omega⟩]
      · intro b _ hbne
        refine ite_eq_right ?_
        rintro ⟨-, -, hb⟩
        exact hbne (by omega)
      · intro hnot
        exact absurd (Finset.mem_range.2 (show tau.sum - sigma.sum < r + 1 by omega)) hnot
    · rw [ite_eq_right hc, Finset.sum_eq_zero]
      intro j hj
      refine ite_eq_right ?_
      rintro ⟨h1, h2, h3⟩
      rw [Finset.mem_range] at hj
      exact hc ⟨h1, h2, by omega⟩
  rw [Finset.sum_congr rfl hjsum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const]
  congr 1
  refine (card_set_eq_card_finset ?_).symm
  ext sigma
  simp only [downDiamondLe, Set.mem_ofPred_eq, Finset.coe_filter, mem_partFinsetLe,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2.included.sum_le⟩, h2, h3, h4⟩
  · rintro ⟨⟨h1, -⟩, h2, h3, h4⟩
    exact ⟨h1, h2, h3, h4⟩

lemma pieri_rhs (m : ℕ) {rho : List ℕ} (r : ℕ) :
    (∑ lam ∈ partFinset (rho.sum + r),
        if HorizStrip lam rho then schurPoly (Fin (m + 1)) R lam else 0)
      = ∑ tau ∈ partFinsetLe (rho.sum + r),
          Nat.card (upDiamond rho tau (rho.sum + r)) •
            (rename Fin.castSucc (schurPoly (Fin m) R tau)
              * X (Fin.last m) ^ (rho.sum + r - tau.sum)) := by
  classical
  have step : ∀ lam ∈ partFinset (rho.sum + r),
      (if HorizStrip lam rho then schurPoly (Fin (m + 1)) R lam else 0)
        = ∑ tau ∈ partFinsetLe (rho.sum + r),
            if HorizStrip lam rho ∧ HorizStrip lam tau then
              rename Fin.castSucc (schurPoly (Fin m) R tau)
                * X (Fin.last m) ^ (rho.sum + r - tau.sum)
            else 0 := by
    intro lam hlam
    obtain ⟨hp, hsum⟩ := mem_partFinset.1 hlam
    by_cases hstrip : HorizStrip lam rho
    · rw [ite_eq_left hstrip, schurPoly_branching' m hp, hsum]
      refine Finset.sum_congr rfl fun tau _ => ?_
      by_cases hts : HorizStrip lam tau
      · rw [ite_eq_left hts, ite_eq_left ⟨hstrip, hts⟩]
      · rw [ite_eq_right hts, ite_eq_right (fun h => hts h.2)]
    · rw [ite_eq_right hstrip, Finset.sum_eq_zero]
      intro tau _
      rw [ite_eq_right (fun h => hstrip h.1)]
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  refine Finset.sum_congr rfl fun tau _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  congr 1
  refine (card_set_eq_card_finset ?_).symm
  ext lam
  simp only [upDiamond, Set.mem_ofPred_eq, Finset.coe_filter, mem_partFinset]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h4⟩, h2, h3⟩
  · rintro ⟨⟨h1, h4⟩, h2, h3⟩
    exact ⟨h1, h2, h3, h4⟩

/-! ### The Pieri rule -/

/-- **The Pieri rule**: the product of the Schur polynomial of shape `rho` by the complete
homogeneous symmetric polynomial of degree `r` is the sum of the Schur polynomials of the
shapes obtained from `rho` by adding a horizontal strip with `r` boxes. -/
theorem schurPoly_mul_hsymm : ∀ (m : ℕ) {rho : List ℕ}, IsPart rho → ∀ r : ℕ,
    schurPoly (Fin m) R rho * hsymm (Fin m) R r
      = ∑ lam ∈ partFinset (rho.sum + r),
          if HorizStrip lam rho then schurPoly (Fin m) R lam else 0 := by
  intro m
  induction m with
  | zero =>
      intro rho hrho r
      rcases eq_or_ne rho [] with rfl | hne
      · rw [schurPoly_nil, one_mul, List.sum_nil, Nat.zero_add]
        rcases Nat.eq_zero_or_pos r with rfl | hr
        · rw [hsymm_zero, partFinset_zero, Finset.sum_singleton,
            ite_eq_left (horizStrip_self isPart_nil), schurPoly_nil]
        · have h1 : hsymm (Fin 0) R r = 0 := by
            rw [← schurPoly_row (σ := Fin 0) (R := R) hr]
            exact schurPoly_eq_zero_of_lt_length (by simp)
          rw [h1, Finset.sum_eq_zero]
          intro lam hlam
          obtain ⟨hp, hsum⟩ := mem_partFinset.1 hlam
          have hlen : 0 < lam.length := by
            rcases lam with _ | ⟨a, l⟩
            · simp only [List.sum_nil] at hsum; omega
            · simp
          rw [schurPoly_eq_zero_of_lt_length hlen, ite_self]
      · have h0 : schurPoly (Fin 0) R rho = 0 :=
          schurPoly_eq_zero_of_lt_length (List.length_pos_iff.2 hne)
        rw [h0, zero_mul, Finset.sum_eq_zero]
        intro lam hlam
        by_cases hstrip : HorizStrip lam rho
        · rw [ite_eq_left hstrip]
          refine schurPoly_eq_zero_of_lt_length ?_
          have h1 := hstrip.included.length_le
          have h2 := List.length_pos_iff.2 hne
          omega
        · rw [ite_eq_right hstrip]
  | succ m IH =>
      intro rho hrho r
      rw [pieri_lhs m (fun {sigma} hsigma j => IH hsigma j) hrho r, pieri_rhs m r]
      refine Finset.sum_congr rfl fun tau htau => ?_
      rw [card_upDiamond_eq_card_downDiamondLe hrho (mem_partFinsetLe.1 htau).1 r]

end MvPolynomial
