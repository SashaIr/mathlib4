/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.List.Finset
public import Mathlib.Combinatorics.Enumerative.Partition.List.HorizontalDiamond
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.Branching

/-!
# The Pieri rule

The Pieri rule expresses the product of a Schur polynomial by a complete homogeneous
symmetric polynomial as a sum of Schur polynomials, over the shapes obtained by adding a
horizontal strip:
`s_ρ * h_r = ∑_{μ / ρ a horizontal strip of size r} s_μ`.

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
  · exact isPart_cons.2 ⟨by simpa using Nat.one_le_iff_ne_zero.2 h, isPart_nil⟩

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
lemma eq_rowShape_of_included {ν : List ℕ} {r : ℕ} (hν : IsPart ν)
    (h : Included ν (rowShape r)) : ν = rowShape ν.sum := by
  have hlen : ν.length ≤ 1 := le_trans h.length_le (length_rowShape_le r)
  match ν, hlen with
  | [], _ => simp [rowShape]
  | [a], _ =>
      have ha : 0 < a := hν.headD_pos (by simp)
      have hs : [a].sum = a := by simp
      rw [hs, rowShape, ite_eq_right (by omega)]

/-! ### The branching rule in the finite-set formulation -/

lemma schurPoly_branching' (m : ℕ) {μ : List ℕ} (hμ : IsPart μ) :
    schurPoly (Fin (m + 1)) R μ
      = ∑ ν ∈ partFinsetLe μ.sum, if HorizStrip μ ν then
          rename Fin.castSucc (schurPoly (Fin m) R ν) * X (Fin.last m) ^ (μ.sum - ν.sum)
        else 0 := by
  rw [schurPoly_branching μ hμ, sum_partFinsetLe_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum_subtype_eq_sum_partFinset k (fun ν => if HorizStrip μ ν then
    rename Fin.castSucc (schurPoly (Fin m) R ν) * X (Fin.last m) ^ (μ.sum - k) else 0)]
  exact Finset.sum_congr rfl fun ν hν => by rw [(mem_partFinset.1 hν).2]

/-- The branching rule for the complete homogeneous symmetric polynomials. -/
lemma hsymm_branching (m r : ℕ) :
    hsymm (Fin (m + 1)) R r
      = ∑ j ∈ Finset.range (r + 1),
          rename Fin.castSucc (hsymm (Fin m) R j) * X (Fin.last m) ^ (r - j) := by
  classical
  rw [← schurPoly_rowShape (Fin (m + 1)) R r, schurPoly_branching' m (isPart_rowShape r),
    sum_rowShape, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun ν => ν.sum) (fun j => rowShape j) (fun ν hν => ?_)
    (fun j hj => ?_) (fun ν hν => ?_) (fun j _ => sum_rowShape j) (fun ν hν => ?_)
  · rw [Finset.mem_filter, mem_partFinsetLe] at hν
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hν.1.2)
  · rw [Finset.mem_range] at hj
    rw [Finset.mem_filter, mem_partFinsetLe, sum_rowShape]
    exact ⟨⟨isPart_rowShape j, by omega⟩, horizStrip_rowShape (by omega)⟩
  · rw [Finset.mem_filter, mem_partFinsetLe] at hν
    exact (eq_rowShape_of_included hν.1.1 hν.2.included).symm
  · rw [Finset.mem_filter, mem_partFinsetLe] at hν
    have hνeq : ν = rowShape ν.sum := eq_rowShape_of_included hν.1.1 hν.2.included
    rw [show schurPoly (Fin m) R ν = hsymm (Fin m) R ν.sum by
      rw [hνeq, sum_rowShape, schurPoly_rowShape]]

/-! ### The two sides of the Pieri rule in a common form -/

/-- Comparing a cardinality of a set of lists with the cardinality of a finite set. -/
lemma card_set_eq_card_finset {s : Set (List ℕ)} {t : Finset (List ℕ)} (h : s = ↑t) :
    Nat.card s = t.card := by
  rw [h, Nat.card_coe_set_eq, Set.ncard_coe_finset]

lemma pieri_lhs (m : ℕ)
    (IH : ∀ {κ : List ℕ}, IsPart κ → ∀ j : ℕ,
      schurPoly (Fin m) R κ * hsymm (Fin m) R j
        = ∑ τ ∈ partFinset (κ.sum + j),
            if HorizStrip τ κ then schurPoly (Fin m) R τ else 0)
    {ρ : List ℕ} (hρ : IsPart ρ) (r : ℕ) :
    schurPoly (Fin (m + 1)) R ρ * hsymm (Fin (m + 1)) R r
      = ∑ τ ∈ partFinsetLe (ρ.sum + r),
          Nat.card (downDiamondLe ρ τ r) •
            (rename Fin.castSucc (schurPoly (Fin m) R τ)
              * X (Fin.last m) ^ (ρ.sum + r - τ.sum)) := by
  classical
  have step : ∀ κ ∈ partFinsetLe ρ.sum, ∀ j ∈ Finset.range (r + 1),
      (if HorizStrip ρ κ then rename Fin.castSucc (schurPoly (Fin m) R κ)
          * X (Fin.last m) ^ (ρ.sum - κ.sum) else 0)
        * (rename Fin.castSucc (hsymm (Fin m) R j) * X (Fin.last m) ^ (r - j))
      = ∑ τ ∈ partFinsetLe (ρ.sum + r),
          if HorizStrip ρ κ ∧ HorizStrip τ κ ∧ τ.sum = κ.sum + j then
            rename Fin.castSucc (schurPoly (Fin m) R τ)
              * X (Fin.last m) ^ (ρ.sum + r - τ.sum)
          else 0 := by
    intro κ hκ j hj
    obtain ⟨hsp, hssum⟩ := mem_partFinsetLe.1 hκ
    have hjr : j ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    by_cases hstrip : HorizStrip ρ κ
    · rw [ite_eq_left hstrip]
      have hprod : (rename Fin.castSucc (schurPoly (Fin m) R κ)
            * X (Fin.last m) ^ (ρ.sum - κ.sum))
          * ((rename Fin.castSucc (hsymm (Fin m) R j) : MvPolynomial (Fin (m + 1)) R)
            * X (Fin.last m) ^ (r - j))
          = rename Fin.castSucc (schurPoly (Fin m) R κ * hsymm (Fin m) R j)
            * X (Fin.last m) ^ (ρ.sum - κ.sum + (r - j)) := by
        rw [map_mul, pow_add]
        ring
      rw [hprod, IH hsp j, map_sum, Finset.sum_mul,
        sum_partFinset_eq_sum_partFinsetLe (show κ.sum + j ≤ ρ.sum + r by omega)]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have hrn : (rename (Fin.castSucc : Fin m → Fin (m + 1))
            (if HorizStrip τ κ then schurPoly (Fin m) R τ else 0)
              : MvPolynomial (Fin (m + 1)) R)
          = if HorizStrip τ κ then rename Fin.castSucc (schurPoly (Fin m) R τ) else 0 := by
        split_ifs
        · rfl
        · exact map_zero _
      by_cases htsum : τ.sum = κ.sum + j
      · rw [ite_eq_left htsum, hrn]
        by_cases hts : HorizStrip τ κ
        · rw [ite_eq_left hts, ite_eq_left ⟨hstrip, hts, htsum⟩,
            show ρ.sum + r - τ.sum = ρ.sum - κ.sum + (r - j) by omega]
        · rw [ite_eq_right hts, ite_eq_right (fun h => hts h.2.1), zero_mul]
      · rw [ite_eq_right htsum, ite_eq_right (fun h => htsum h.2.2)]
    · rw [ite_eq_right hstrip, zero_mul, Finset.sum_eq_zero]
      intro τ _
      rw [ite_eq_right (fun h => hstrip h.1)]
  have expand : schurPoly (Fin (m + 1)) R ρ * hsymm (Fin (m + 1)) R r
      = ∑ κ ∈ partFinsetLe ρ.sum, ∑ j ∈ Finset.range (r + 1),
          ∑ τ ∈ partFinsetLe (ρ.sum + r),
            if HorizStrip ρ κ ∧ HorizStrip τ κ ∧ τ.sum = κ.sum + j then
              rename Fin.castSucc (schurPoly (Fin m) R τ)
                * X (Fin.last m) ^ (ρ.sum + r - τ.sum)
            else 0 := by
    rw [schurPoly_branching' m hρ, hsymm_branching m r, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun κ hs => Finset.sum_congr rfl fun j hj => step κ hs j hj
  rw [expand, Finset.sum_congr rfl (fun κ _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  -- the sum over `j` has at most one nonzero term
  have hjsum : ∀ κ ∈ partFinsetLe ρ.sum,
      (∑ j ∈ Finset.range (r + 1),
        if HorizStrip ρ κ ∧ HorizStrip τ κ ∧ τ.sum = κ.sum + j then
          rename Fin.castSucc (schurPoly (Fin m) R τ)
            * X (Fin.last m) ^ (ρ.sum + r - τ.sum) else 0)
      = if HorizStrip ρ κ ∧ HorizStrip τ κ ∧ τ.sum ≤ κ.sum + r then
          rename Fin.castSucc (schurPoly (Fin m) R τ)
            * X (Fin.last m) ^ (ρ.sum + r - τ.sum) else 0 := by
    intro κ _
    by_cases hc : HorizStrip ρ κ ∧ HorizStrip τ κ ∧ τ.sum ≤ κ.sum + r
    · have hκτ : κ.sum ≤ τ.sum := hc.2.1.included.sum_le
      rw [ite_eq_left hc, Finset.sum_eq_single (τ.sum - κ.sum)]
      · rw [ite_eq_left ⟨hc.1, hc.2.1, by omega⟩]
      · intro b _ hbne
        refine ite_eq_right ?_
        rintro ⟨-, -, hb⟩
        exact hbne (by omega)
      · intro hnot
        exact absurd (Finset.mem_range.2 (show τ.sum - κ.sum < r + 1 by omega)) hnot
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
  ext κ
  simp only [downDiamondLe, Set.mem_ofPred_eq, Finset.coe_filter, mem_partFinsetLe,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2.included.sum_le⟩, h2, h3, h4⟩
  · rintro ⟨⟨h1, -⟩, h2, h3, h4⟩
    exact ⟨h1, h2, h3, h4⟩

lemma pieri_rhs (m : ℕ) {ρ : List ℕ} (r : ℕ) :
    (∑ μ ∈ partFinset (ρ.sum + r),
        if HorizStrip μ ρ then schurPoly (Fin (m + 1)) R μ else 0)
      = ∑ τ ∈ partFinsetLe (ρ.sum + r),
          Nat.card (upDiamond ρ τ (ρ.sum + r)) •
            (rename Fin.castSucc (schurPoly (Fin m) R τ)
              * X (Fin.last m) ^ (ρ.sum + r - τ.sum)) := by
  classical
  have step : ∀ μ ∈ partFinset (ρ.sum + r),
      (if HorizStrip μ ρ then schurPoly (Fin (m + 1)) R μ else 0)
        = ∑ τ ∈ partFinsetLe (ρ.sum + r),
            if HorizStrip μ ρ ∧ HorizStrip μ τ then
              rename Fin.castSucc (schurPoly (Fin m) R τ)
                * X (Fin.last m) ^ (ρ.sum + r - τ.sum)
            else 0 := by
    intro μ hμ
    obtain ⟨hp, hsum⟩ := mem_partFinset.1 hμ
    by_cases hstrip : HorizStrip μ ρ
    · rw [ite_eq_left hstrip, schurPoly_branching' m hp, hsum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      by_cases hts : HorizStrip μ τ
      · rw [ite_eq_left hts, ite_eq_left ⟨hstrip, hts⟩]
      · rw [ite_eq_right hts, ite_eq_right (fun h => hts h.2)]
    · rw [ite_eq_right hstrip, Finset.sum_eq_zero]
      intro τ _
      rw [ite_eq_right (fun h => hstrip h.1)]
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  congr 1
  refine (card_set_eq_card_finset ?_).symm
  ext μ
  simp only [upDiamond, Set.mem_ofPred_eq, Finset.coe_filter, mem_partFinset]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h4⟩, h2, h3⟩
  · rintro ⟨⟨h1, h4⟩, h2, h3⟩
    exact ⟨h1, h2, h3, h4⟩

/-! ### The Pieri rule -/

/-- **The Pieri rule**: the product of the Schur polynomial of shape `ρ` by the complete
homogeneous symmetric polynomial of degree `r` is the sum of the Schur polynomials of the
shapes obtained from `ρ` by adding a horizontal strip with `r` boxes. -/
theorem schurPoly_mul_hsymm : ∀ (m : ℕ) {ρ : List ℕ}, IsPart ρ → ∀ r : ℕ,
    schurPoly (Fin m) R ρ * hsymm (Fin m) R r
      = ∑ μ ∈ partFinset (ρ.sum + r),
          if HorizStrip μ ρ then schurPoly (Fin m) R μ else 0 := by
  intro m
  induction m with
  | zero =>
      intro ρ hρ r
      rcases eq_or_ne ρ [] with rfl | hne
      · rw [schurPoly_nil, one_mul, List.sum_nil, Nat.zero_add]
        rcases Nat.eq_zero_or_pos r with rfl | hr
        · rw [hsymm_zero, partFinset_zero, Finset.sum_singleton,
            ite_eq_left (horizStrip_self isPart_nil), schurPoly_nil]
        · have h1 : hsymm (Fin 0) R r = 0 := by
            rw [← schurPoly_row (σ := Fin 0) (R := R) hr]
            exact schurPoly_eq_zero_of_lt_length (by simp)
          rw [h1, Finset.sum_eq_zero]
          intro μ hμ
          obtain ⟨hp, hsum⟩ := mem_partFinset.1 hμ
          have hlen : 0 < μ.length := by
            rcases μ with _ | ⟨a, l⟩
            · simp only [List.sum_nil] at hsum; omega
            · simp
          rw [schurPoly_eq_zero_of_lt_length hlen, ite_self]
      · have h0 : schurPoly (Fin 0) R ρ = 0 :=
          schurPoly_eq_zero_of_lt_length (List.length_pos_iff.2 hne)
        rw [h0, zero_mul, Finset.sum_eq_zero]
        intro μ hμ
        by_cases hstrip : HorizStrip μ ρ
        · rw [ite_eq_left hstrip]
          refine schurPoly_eq_zero_of_lt_length ?_
          have h1 := hstrip.included.length_le
          have h2 := List.length_pos_iff.2 hne
          omega
        · rw [ite_eq_right hstrip]
  | succ m IH =>
      intro ρ hρ r
      rw [pieri_lhs m (fun {κ} hκ j => IH hκ j) hρ r, pieri_rhs m r]
      refine Finset.sum_congr rfl fun τ hτ => ?_
      rw [card_upDiamond_eq_card_downDiamondLe hρ (mem_partFinsetLe.1 hτ).1 r]

end MvPolynomial
