/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.GroupTheory.Perm.SymmetricGroup.Inversions

/-!
# The right weak order on the symmetric group

Following `theories/SymGroup/weak_order.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we describe how the inversions of a
product of two permutations are obtained from those of the factors, and we deduce the
characterisation of the right weak order by inclusion of inversion sets.

Inversions of a permutation `σ` of `Fin N` are pairs of *positions* (`Equiv.Perm.invSet`); the
inversions of `σ⁻¹` are the pairs of *values* `a < b` occurring in the reverse order in
`σ`.  If `p = σ τ`, a pair of positions is an inversion of `p` exactly when it is an
inversion of `τ` or its image under `τ` is an inversion of `σ`, but not both.  Counting
gives `ℓ(σ τ) = ℓ(σ) + ℓ(τ)` if and only if these two sets of pairs are disjoint, and,
after replacing the permutations by their inverses, the theorem that

`ℓ(u) + ℓ(u⁻¹ v) = ℓ(v)` if and only if every inversion of `u⁻¹` is one of `v⁻¹`.

## Main definitions and results

* `Equiv.Perm.IsInvPair σ a b` : the unordered pair `{a, b}` is inverted by `σ`.
* `Equiv.Perm.transportSet σ τ` : the pairs of positions whose image under `τ` is inverted
  by `σ`.
* `Equiv.Perm.invSet_mul` : `invSet (σ * τ)` is the symmetric difference of `invSet τ` and
  `transportSet σ τ`.
* `Equiv.Perm.invCount_mul_eq_add_iff` : the lengths add exactly when the two sets are
  disjoint.
* `Equiv.Perm.RightWeakLe` and `Equiv.Perm.rightWeakLe_iff_subset` : the right weak order and its
  characterisation by inclusion of inversion sets, together with the fact that it is a
  partial order.
-/

open Equiv Finset List

namespace Equiv.Perm


variable {N : ℕ}

/-! ### Inverted unordered pairs -/

/-- The unordered pair `{a, b}` is inverted by `σ`: the larger of `a`, `b` has the smaller
image. -/
def IsInvPair (σ : Equiv.Perm (Fin N)) (a b : Fin N) : Prop := σ (max a b) < σ (min a b)

instance (σ : Equiv.Perm (Fin N)) (a b : Fin N) : Decidable (IsInvPair σ a b) :=
  inferInstanceAs (Decidable (_ < _))

lemma isInvPair_comm (σ : Equiv.Perm (Fin N)) (a b : Fin N) :
    IsInvPair σ a b ↔ IsInvPair σ b a := by
  rw [IsInvPair, IsInvPair, max_comm, min_comm]

lemma isInvPair_of_lt {σ : Equiv.Perm (Fin N)} {a b : Fin N} (hab : a < b) :
    IsInvPair σ a b ↔ σ b < σ a := by
  rw [IsInvPair, max_eq_right hab.le, min_eq_left hab.le]

lemma mem_invSet_iff_isInvPair {σ : Equiv.Perm (Fin N)} {i j : Fin N} (hij : i < j) :
    (i, j) ∈ invSet σ ↔ IsInvPair σ i j := by
  rw [mem_invSet, isInvPair_of_lt hij]
  exact ⟨fun h => h.2, fun h => ⟨hij, h⟩⟩

/-- The pair `{a, b}` written in increasing order. -/
def sortPair (a b : Fin N) : Fin N × Fin N := if a < b then (a, b) else (b, a)

lemma sortPair_def (a b : Fin N) : sortPair a b = if a < b then (a, b) else (b, a) := rfl

lemma sortPair_fst_lt_snd {a b : Fin N} (hab : a ≠ b) :
    (sortPair a b).1 < (sortPair a b).2 := by
  rw [sortPair_def]
  by_cases h : a < b
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact lt_of_le_of_ne (not_lt.1 h) hab.symm

lemma isInvPair_sortPair (σ : Equiv.Perm (Fin N)) (a b : Fin N) :
    IsInvPair σ (sortPair a b).1 (sortPair a b).2 ↔ IsInvPair σ a b := by
  rw [sortPair_def]
  by_cases h : a < b
  · rw [if_pos h]
  · rw [if_neg h]
    exact isInvPair_comm σ b a

/-! ### Inversions of a product -/

variable (σ τ : Equiv.Perm (Fin N))

/-- The pairs of positions whose image under `τ` is inverted by `σ`. -/
def transportSet : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ IsInvPair σ (τ p.1) (τ p.2))

@[simp] lemma mem_transportSet {p : Fin N × Fin N} :
    p ∈ transportSet σ τ ↔ p.1 < p.2 ∧ IsInvPair σ (τ p.1) (τ p.2) := by
  simp [transportSet]

/-- Transporting the inversions of `σ` along `τ` does not change their number. -/
lemma card_transportSet : (transportSet σ τ).card = invCount σ := by
  classical
  refine Finset.card_bij' (i := fun p _ => sortPair (τ p.1) (τ p.2))
    (j := fun p _ => sortPair (τ⁻¹ p.1) (τ⁻¹ p.2)) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hp
    obtain ⟨hij, hinv⟩ := (mem_transportSet σ τ).1 hp
    simp only at hij hinv
    have hne : τ i ≠ τ j := fun h => absurd (τ.injective h) (ne_of_lt hij)
    exact mem_invSet_iff_isInvPair (sortPair_fst_lt_snd hne) |>.2
      ((isInvPair_sortPair σ (τ i) (τ j)).2 hinv)
  · rintro ⟨a, b⟩ hp
    obtain ⟨hab, hinv⟩ := mem_invSet.1 hp
    simp only at hab hinv
    have hne : τ⁻¹ a ≠ τ⁻¹ b := fun h => absurd (τ.symm.injective h) (ne_of_lt hab)
    have hinv' : IsInvPair σ a b := (isInvPair_of_lt hab).2 hinv
    refine (mem_transportSet σ τ).2 ⟨sortPair_fst_lt_snd hne, ?_⟩
    change IsInvPair σ (τ (sortPair (τ⁻¹ a) (τ⁻¹ b)).1) (τ (sortPair (τ⁻¹ a) (τ⁻¹ b)).2)
    rw [sortPair_def]
    by_cases h : τ⁻¹ a < τ⁻¹ b
    · rw [if_pos h]
      simpa using hinv'
    · rw [if_neg h]
      simpa using (isInvPair_comm σ a b).1 hinv'
  · rintro ⟨i, j⟩ hp
    obtain ⟨hij, -⟩ := (mem_transportSet σ τ).1 hp
    simp only at hij
    change sortPair (τ⁻¹ (sortPair (τ i) (τ j)).1) (τ⁻¹ (sortPair (τ i) (τ j)).2) = (i, j)
    rw [sortPair_def (τ i) (τ j)]
    by_cases h : τ i < τ j
    · rw [if_pos h]
      simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
      rw [sortPair_def, if_pos hij]
    · rw [if_neg h]
      simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
      rw [sortPair_def, if_neg (asymm hij)]
  · rintro ⟨a, b⟩ hp
    obtain ⟨hab, -⟩ := mem_invSet.1 hp
    simp only at hab
    change sortPair (τ (sortPair (τ⁻¹ a) (τ⁻¹ b)).1) (τ (sortPair (τ⁻¹ a) (τ⁻¹ b)).2) = (a, b)
    rw [sortPair_def (τ⁻¹ a) (τ⁻¹ b)]
    by_cases h : τ⁻¹ a < τ⁻¹ b
    · rw [if_pos h]
      simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
      rw [sortPair_def, if_pos hab]
    · rw [if_neg h]
      simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
      rw [sortPair_def, if_neg (asymm hab)]

/-- A pair of positions is an inversion of `σ τ` exactly when it is an inversion of `τ` or
its image under `τ` is an inversion of `σ`, but not both. -/
theorem invSet_mul : invSet (σ * τ) = symmDiff (invSet τ) (transportSet σ τ) := by
  classical
  ext p
  obtain ⟨i, j⟩ := p
  rw [Finset.mem_symmDiff, mem_invSet, mem_invSet, mem_transportSet]
  simp only
  constructor
  · rintro ⟨hij, hlt⟩
    by_cases hτ : τ j < τ i
    · refine Or.inl ⟨⟨hij, hτ⟩, ?_⟩
      rintro ⟨-, hinv⟩
      rw [isInvPair_comm, isInvPair_of_lt hτ] at hinv
      exact absurd hinv (not_lt.2 (le_of_lt hlt))
    · have hτ' : τ i < τ j :=
        lt_of_le_of_ne (not_lt.1 hτ) fun h => absurd (τ.injective h) (ne_of_lt hij)
      refine Or.inr ⟨⟨hij, (isInvPair_of_lt hτ').2 hlt⟩, ?_⟩
      rintro ⟨-, hcon⟩
      exact absurd hcon (not_lt.2 (le_of_lt hτ'))
  · rintro (⟨⟨hij, hτ⟩, hnot⟩ | ⟨⟨hij, hinv⟩, hnot⟩)
    · refine ⟨hij, ?_⟩
      have hne : ¬ IsInvPair σ (τ i) (τ j) := fun hcon => hnot ⟨hij, hcon⟩
      rw [isInvPair_comm, isInvPair_of_lt hτ] at hne
      have hne' : σ (τ i) ≠ σ (τ j) := fun h =>
        absurd (τ.injective (σ.injective h)) (ne_of_lt hij)
      exact lt_of_le_of_ne (not_lt.1 hne) fun h => hne' h.symm
    · refine ⟨hij, ?_⟩
      have hτ : ¬ τ j < τ i := fun hcon => hnot ⟨hij, hcon⟩
      have hτ' : τ i < τ j :=
        lt_of_le_of_ne (not_lt.1 hτ) fun h => absurd (τ.injective h) (ne_of_lt hij)
      exact (isInvPair_of_lt hτ').1 hinv

/-- Counting the inversions of a product. -/
theorem invCount_mul_add_two_mul_card_inter :
    invCount (σ * τ) + 2 * ((invSet τ) ∩ (transportSet σ τ)).card
      = invCount σ + invCount τ := by
  classical
  have hsymm : (symmDiff (invSet τ) (transportSet σ τ)).card
      + 2 * ((invSet τ) ∩ (transportSet σ τ)).card
      = (invSet τ).card + (transportSet σ τ).card := by
    have h1 : symmDiff (invSet τ) (transportSet σ τ)
        = ((invSet τ) \ (transportSet σ τ)) ∪ ((transportSet σ τ) \ (invSet τ)) := rfl
    rw [h1, Finset.card_union_of_disjoint (by simp [Finset.disjoint_left]; tauto)]
    have h2 := Finset.card_sdiff_add_card_inter (invSet τ) (transportSet σ τ)
    have h3 := Finset.card_sdiff_add_card_inter (transportSet σ τ) (invSet τ)
    rw [Finset.inter_comm (transportSet σ τ) (invSet τ)] at h3
    omega
  rw [invCount, invSet_mul, hsymm, card_transportSet]
  rw [invCount, invCount]
  omega

/-- The number of inversions of a product is the sum of the numbers of inversions exactly
when no pair is counted twice. -/
theorem invCount_mul_eq_add_iff :
    invCount (σ * τ) = invCount σ + invCount τ
      ↔ _root_.Disjoint (invSet τ) (transportSet σ τ) := by
  classical
  have h := invCount_mul_add_two_mul_card_inter σ τ
  constructor
  · intro heq
    by_contra hcon
    have hpos : 0 < ((invSet τ) ∩ (transportSet σ τ)).card :=
      Finset.card_pos.2 (Finset.not_disjoint_iff_nonempty_inter.1 hcon)
    omega
  · intro hdis
    have hz : ((invSet τ) ∩ (transportSet σ τ)).card = 0 :=
      Finset.card_eq_zero.2 (Finset.disjoint_iff_inter_eq_empty.1 hdis)
    omega

/-! ### A permutation is determined by its inversions -/

/-- The image of a point is the number of points with a smaller image. -/
lemma val_apply_eq_card_filter (π : Equiv.Perm (Fin N)) (i : Fin N) :
    ((π i : Fin N) : ℕ) = (Finset.univ.filter (fun j => π j < π i)).card := by
  classical
  have : (Finset.univ.filter (fun j => π j < π i)).card = (Finset.Iio (π i)).card := by
    refine Finset.card_bij' (i := fun j _ => π j) (j := fun a _ => π⁻¹ a) ?_ ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_Iio.2 (Finset.mem_filter.1 hj).2
    · intro a ha
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      simpa using Finset.mem_Iio.1 ha
    · intro j _
      simp
    · intro a _
      simp
  rw [this, Fin.card_Iio]

/-- Two permutations with the same inversions are equal. -/
theorem invSet_injective {σ τ : Equiv.Perm (Fin N)} (h : invSet σ = invSet τ) : σ = τ := by
  classical
  have hpair : ∀ i j : Fin N, i ≠ j → (IsInvPair σ i j ↔ IsInvPair τ i j) := by
    intro i j hij
    have h1 : (sortPair i j).1 < (sortPair i j).2 := sortPair_fst_lt_snd hij
    rw [← isInvPair_sortPair σ i j, ← isInvPair_sortPair τ i j,
      ← mem_invSet_iff_isInvPair h1, ← mem_invSet_iff_isInvPair h1, h]
  have hlt : ∀ i j : Fin N, (σ j < σ i ↔ τ j < τ i) := by
    intro i j
    rcases eq_or_ne i j with rfl | hij
    · simp
    · rcases lt_or_gt_of_ne hij with hlt | hlt
      · rw [← isInvPair_of_lt hlt, ← isInvPair_of_lt hlt]
        exact hpair i j hij
      · constructor
        · intro hcon
          have h1 : ¬ IsInvPair σ j i := by
            rw [isInvPair_of_lt hlt]
            exact not_lt.2 (le_of_lt hcon)
          have h2 : ¬ IsInvPair τ j i := fun hc => h1 ((hpair j i hij.symm).2 hc)
          rw [isInvPair_of_lt hlt, not_lt] at h2
          exact lt_of_le_of_ne h2 fun hc => absurd (τ.injective hc) hij.symm
        · intro hcon
          have h1 : ¬ IsInvPair τ j i := by
            rw [isInvPair_of_lt hlt]
            exact not_lt.2 (le_of_lt hcon)
          have h2 : ¬ IsInvPair σ j i := fun hc => h1 ((hpair j i hij.symm).1 hc)
          rw [isInvPair_of_lt hlt, not_lt] at h2
          exact lt_of_le_of_ne h2 fun hc => absurd (σ.injective hc) hij.symm
  ext i
  rw [val_apply_eq_card_filter σ i, val_apply_eq_card_filter τ i]
  exact congrArg Finset.card (Finset.filter_congr fun j _ => by
    simpa using hlt i j)

/-! ### The right weak order -/

/-- The right weak order: `u ≤ v` when the lengths of `u` and of `u⁻¹ v` add up to the
length of `v`, that is, when a reduced word for `u` can be completed into one for `v`. -/
def RightWeakLe (u v : Equiv.Perm (Fin N)) : Prop :=
  invCount u + invCount (u⁻¹ * v) = invCount v

lemma rightWeakLe_iff_length {n : ℕ} (u v : Equiv.Perm (Fin (n + 1))) :
    RightWeakLe u v ↔ (permCoxeterSystem n).length u + (permCoxeterSystem n).length (u⁻¹ * v)
      = (permCoxeterSystem n).length v := by
  rw [RightWeakLe, length_eq_invCount, length_eq_invCount, length_eq_invCount]

lemma subset_symmDiff_iff_disjoint {α : Type*} [DecidableEq α] (s t : Finset α) :
    s ⊆ symmDiff s t ↔ _root_.Disjoint s t := by
  constructor
  · intro h
    rw [Finset.disjoint_left]
    intro a ha hat
    have := h ha
    rw [Finset.mem_symmDiff] at this
    tauto
  · intro h a ha
    rw [Finset.mem_symmDiff]
    exact Or.inl ⟨ha, fun hc => (Finset.disjoint_left.1 h ha) hc⟩

/-- **The right weak order is the inclusion of inversion sets**: the lengths of `u` and
of `u⁻¹ v` add up to the length of `v` exactly when every inversion of `u⁻¹` is an
inversion of `v⁻¹`. -/
theorem rightWeakLe_iff_subset {n : ℕ} (u v : Equiv.Perm (Fin (n + 1))) :
    RightWeakLe u v ↔ invSet u⁻¹ ⊆ invSet v⁻¹ := by
  classical
  set t : Equiv.Perm (Fin (n + 1)) := u⁻¹ * v with htdef
  have hv : v⁻¹ = t⁻¹ * u⁻¹ := by
    rw [htdef]
    group
  have hset : invSet v⁻¹ = symmDiff (invSet u⁻¹) (transportSet t⁻¹ u⁻¹) := by
    rw [hv, invSet_mul]
  have hcard := invCount_mul_add_two_mul_card_inter t⁻¹ u⁻¹
  rw [← hv, invCount_inv, invCount_inv, invCount_inv] at hcard
  rw [RightWeakLe, ← htdef, hset, subset_symmDiff_iff_disjoint]
  constructor
  · intro heq
    have hz : ((invSet u⁻¹) ∩ (transportSet t⁻¹ u⁻¹)).card = 0 := by omega
    exact Finset.disjoint_iff_inter_eq_empty.2 (Finset.card_eq_zero.1 hz)
  · intro hdis
    have hz : ((invSet u⁻¹) ∩ (transportSet t⁻¹ u⁻¹)).card = 0 :=
      Finset.card_eq_zero.2 (Finset.disjoint_iff_inter_eq_empty.1 hdis)
    omega

lemma rightWeakLe_refl {n : ℕ} (u : Equiv.Perm (Fin (n + 1))) : RightWeakLe u u := by
  rw [rightWeakLe_iff_subset]

lemma rightWeakLe_trans {n : ℕ} {u v w : Equiv.Perm (Fin (n + 1))}
    (huv : RightWeakLe u v) (hvw : RightWeakLe v w) : RightWeakLe u w := by
  rw [rightWeakLe_iff_subset] at *
  exact huv.trans hvw

lemma rightWeakLe_antisymm {n : ℕ} {u v : Equiv.Perm (Fin (n + 1))}
    (huv : RightWeakLe u v) (hvu : RightWeakLe v u) : u = v := by
  rw [rightWeakLe_iff_subset] at huv hvu
  have : invSet u⁻¹ = invSet v⁻¹ := Finset.Subset.antisymm huv hvu
  exact inv_injective (invSet_injective this)

/-! ### Extremal elements -/

/-- The identity is the least element of the right weak order. -/
lemma rightWeakLe_one {n : ℕ} (u : Equiv.Perm (Fin (n + 1))) : RightWeakLe 1 u := by
  rw [rightWeakLe_iff_subset, inv_one, invSet_one]
  exact Finset.empty_subset _

/-- The reversal permutation is the greatest element of the right weak order. -/
lemma rightWeakLe_revPerm {n : ℕ} (u : Equiv.Perm (Fin (n + 1))) :
    RightWeakLe u (Fin.revPerm : Equiv.Perm (Fin (n + 1))) := by
  rw [rightWeakLe_iff_subset]
  intro p hp
  have hrev : (Fin.revPerm : Equiv.Perm (Fin (n + 1)))⁻¹ = Fin.revPerm := by
    ext i
    simp [Equiv.Perm.inv_def]
  rw [hrev, invSet_revPerm]
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (mem_invSet.1 hp).1⟩

/-! ### The left weak order -/

/-- The left weak order: `u ≤ v` when the lengths of `u` and of `v u⁻¹` add up to the
length of `v`, that is, when a reduced word for `u` can be completed on the left into one
for `v`. -/
def LeftWeakLe (u v : Equiv.Perm (Fin N)) : Prop :=
  invCount u + invCount (v * u⁻¹) = invCount v

/-- The left weak order is the right weak order on the inverses. -/
lemma leftWeakLe_iff_rightWeakLe {n : ℕ} (u v : Equiv.Perm (Fin (n + 1))) :
    LeftWeakLe u v ↔ RightWeakLe u⁻¹ v⁻¹ := by
  rw [LeftWeakLe, RightWeakLe, invCount_inv, invCount_inv]
  have hp : (u⁻¹)⁻¹ * v⁻¹ = (v * u⁻¹)⁻¹ := by group
  rw [hp, invCount_inv]

/-- **The left weak order is the inclusion of inversion sets** (of the permutations
themselves, rather than of their inverses). -/
theorem leftWeakLe_iff_subset {n : ℕ} (u v : Equiv.Perm (Fin (n + 1))) :
    LeftWeakLe u v ↔ invSet u ⊆ invSet v := by
  rw [leftWeakLe_iff_rightWeakLe, rightWeakLe_iff_subset, inv_inv, inv_inv]

lemma leftWeakLe_refl {n : ℕ} (u : Equiv.Perm (Fin (n + 1))) : LeftWeakLe u u := by
  rw [leftWeakLe_iff_subset]

lemma leftWeakLe_trans {n : ℕ} {u v w : Equiv.Perm (Fin (n + 1))}
    (huv : LeftWeakLe u v) (hvw : LeftWeakLe v w) : LeftWeakLe u w := by
  rw [leftWeakLe_iff_subset] at *
  exact huv.trans hvw

lemma leftWeakLe_antisymm {n : ℕ} {u v : Equiv.Perm (Fin (n + 1))}
    (huv : LeftWeakLe u v) (hvu : LeftWeakLe v u) : u = v := by
  rw [leftWeakLe_iff_subset] at huv hvu
  exact invSet_injective (Finset.Subset.antisymm huv hvu)

end Equiv.Perm
