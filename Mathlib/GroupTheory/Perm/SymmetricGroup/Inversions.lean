/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.Perm.SymmetricGroup.Presentation

/-!
# Inversions of a permutation and the Coxeter length

Following `theories/SymGroup/weak_order.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we study the inversions of a
permutation of `Fin N`: the pairs `i < j` with `σ j < σ i`.  The main theorem is that the
number of inversions of a permutation is its Coxeter length for the Coxeter system of
`Equiv.Perm.permCoxeterSystem`, that is, the minimal number of adjacent transpositions needed
to write it.

## Main definitions and results

* `Equiv.Perm.invSet σ` : the set of inversions of `σ`, `Equiv.Perm.invCount σ` its cardinality.
* `Equiv.Perm.invCount_mul_adjSwap` : multiplying on the right by an adjacent transposition
  changes the number of inversions by exactly one.
* `Equiv.Perm.length_eq_invCount` : the Coxeter length of a permutation is its number of
  inversions.
* `Equiv.Perm.sign_eq_invCount` : the signature of a permutation is `(-1)` to its number of
  inversions.
* `Equiv.Perm.invCount_le`, `Equiv.Perm.invCount_revPerm` : the number of inversions is at most
  `N.choose 2`, with equality for the reversal permutation, which therefore is the longest
  element of the symmetric group.
-/

open Equiv Finset

namespace Equiv.Perm


variable {N : ℕ}

/-! ### Inversions -/

/-- The set of inversions of a permutation: the pairs `i < j` with `σ j < σ i`. -/
def invSet (σ : Equiv.Perm (Fin N)) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ σ p.2 < σ p.1)

/-- The number of inversions of a permutation. -/
def invCount (σ : Equiv.Perm (Fin N)) : ℕ := (invSet σ).card

@[simp] lemma mem_invSet {σ : Equiv.Perm (Fin N)} {p : Fin N × Fin N} :
    p ∈ invSet σ ↔ p.1 < p.2 ∧ σ p.2 < σ p.1 := by
  simp [invSet]

@[simp] lemma invSet_one : invSet (1 : Equiv.Perm (Fin N)) = ∅ := by
  ext p
  simp only [mem_invSet, Finset.notMem_empty, iff_false, not_and, not_lt]
  intro h
  exact le_of_lt h

@[simp] lemma invCount_one : invCount (1 : Equiv.Perm (Fin N)) = 0 := by
  simp [invCount]

/-- A permutation without inversions is the identity. -/
lemma eq_one_of_invCount_eq_zero {σ : Equiv.Perm (Fin N)} (h : invCount σ = 0) : σ = 1 := by
  have hempty : invSet σ = ∅ := Finset.card_eq_zero.1 h
  have hmono : StrictMono (⇑σ) := by
    intro a b hab
    have : (a, b) ∉ invSet σ := by simp [hempty]
    rw [mem_invSet] at this
    push Not at this
    exact lt_of_le_of_ne (this hab) fun hcon => absurd (σ.injective hcon) (ne_of_lt hab)
  have hinv : StrictMono (⇑σ⁻¹) := by
    intro a b hab
    by_contra hcon
    push Not at hcon
    have h2 : b ≤ a := by simpa using hmono.monotone hcon
    exact absurd hab (not_lt.2 h2)
  ext i
  have h1 : i ≤ σ i := hmono.le_apply
  have h2 : σ i ≤ i := by simpa using hinv.le_apply (x := σ i)
  simp [le_antisymm h2 h1]

/-- If a permutation is not the identity, it has an adjacent descent. -/
lemma exists_adjacent_descent {n : ℕ} {σ : Equiv.Perm (Fin (n + 1))} (h : σ ≠ 1) :
    ∃ i : Fin n, σ i.succ < σ i.castSucc := by
  by_contra hcon
  push Not at hcon
  refine h ?_
  have hmono : StrictMono (⇑σ) := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    exact lt_of_le_of_ne (hcon i) fun hc => absurd (σ.injective hc)
      (ne_of_lt Fin.castSucc_lt_succ)
  have hzero : invSet σ = ∅ := by
    ext p
    simp only [mem_invSet, Finset.notMem_empty, iff_false, not_and, not_lt]
    exact fun hp => le_of_lt (hmono hp)
  exact eq_one_of_invCount_eq_zero (by simp [invCount, hzero])

/-! ### Multiplication by an adjacent transposition -/

section Adjacent

variable {c d : Fin N} (hcd : (c : ℕ) + 1 = (d : ℕ))

include hcd

/-- Except for the pair `(c, d)` itself, the transposition of two adjacent points
preserves the order of pairs. -/
lemma swap_lt_swap {a b : Fin N} (hab : a < b) (hne : (a, b) ≠ (c, d)) :
    Equiv.swap c d a < Equiv.swap c d b := by
  have hval : ∀ x : Fin N, ((Equiv.swap c d x : Fin N) : ℕ)
      = if (x : ℕ) = (c : ℕ) then (d : ℕ) else if (x : ℕ) = (d : ℕ) then (c : ℕ) else (x : ℕ) := by
    intro x
    by_cases h1 : x = c
    · rw [h1, Equiv.swap_apply_left, ite_eq_left rfl]
    by_cases h2 : x = d
    · rw [h2, Equiv.swap_apply_right, ite_eq_right (show ¬((d : ℕ) = (c : ℕ)) by omega),
        ite_eq_left rfl]
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2, ite_eq_right (fun h => h1 (Fin.ext h)),
        ite_eq_right (fun h => h2 (Fin.ext h))]
  have hab' : (a : ℕ) < (b : ℕ) := hab
  have hne' : ¬ ((a : ℕ) = (c : ℕ) ∧ (b : ℕ) = (d : ℕ)) := by
    intro ⟨h1, h2⟩
    exact hne (Prod.ext (Fin.ext h1) (Fin.ext h2))
  rw [Fin.lt_def, hval a, hval b]
  split_ifs <;> omega

/-- The inversions of `σ * (c d)` other than `(c, d)` are in bijection with those of `σ`
other than `(c, d)`. -/
lemma card_invSet_erase_swap (σ : Equiv.Perm (Fin N)) :
    ((invSet (σ * Equiv.swap c d)).erase (c, d)).card
      = ((invSet σ).erase (c, d)).card := by
  classical
  have hcltd : c < d := by rw [Fin.lt_def]; omega
  refine Finset.card_bij (fun p _ => (Equiv.swap c d p.1, Equiv.swap c d p.2)) ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    have hne : (a, b) ≠ (c, d) := Finset.ne_of_mem_erase hp
    obtain ⟨hab, hσ⟩ := mem_invSet.1 (Finset.mem_of_mem_erase hp)
    simp only at hab hσ
    have hswap := swap_lt_swap hcd hab hne
    refine Finset.mem_erase.2 ⟨?_, ?_⟩
    · intro hcon
      have h1 : Equiv.swap c d a = c := congrArg Prod.fst hcon
      have h2 : Equiv.swap c d b = d := congrArg Prod.snd hcon
      have ha : a = d := by
        have := congrArg (Equiv.swap c d) h1
        simpa using this
      have hb : b = c := by
        have := congrArg (Equiv.swap c d) h2
        simpa using this
      rw [ha, hb] at hab
      exact absurd hab (not_lt.2 (le_of_lt hcltd))
    · exact mem_invSet.2 ⟨hswap, by simpa using hσ⟩
  · rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' heq
    have h1 : Equiv.swap c d a = Equiv.swap c d a' := congrArg Prod.fst heq
    have h2 : Equiv.swap c d b = Equiv.swap c d b' := congrArg Prod.snd heq
    exact Prod.ext ((Equiv.swap c d).injective h1) ((Equiv.swap c d).injective h2)
  · rintro ⟨a, b⟩ hp
    have hne : (a, b) ≠ (c, d) := Finset.ne_of_mem_erase hp
    obtain ⟨hab, hσ⟩ := mem_invSet.1 (Finset.mem_of_mem_erase hp)
    simp only at hab hσ
    have hswap := swap_lt_swap hcd hab hne
    refine ⟨(Equiv.swap c d a, Equiv.swap c d b), Finset.mem_erase.2 ⟨?_, ?_⟩, ?_⟩
    · intro hcon
      have h1 : Equiv.swap c d a = c := congrArg Prod.fst hcon
      have h2 : Equiv.swap c d b = d := congrArg Prod.snd hcon
      have ha : a = d := by
        have := congrArg (Equiv.swap c d) h1
        simpa using this
      have hb : b = c := by
        have := congrArg (Equiv.swap c d) h2
        simpa using this
      rw [ha, hb] at hab
      exact absurd hab (not_lt.2 (le_of_lt hcltd))
    · refine mem_invSet.2 ⟨hswap, ?_⟩
      simpa using hσ
    · simp

/-- Multiplying on the right by the transposition of two adjacent points changes the
number of inversions by exactly one. -/
lemma invCount_mul_swap (σ : Equiv.Perm (Fin N)) :
    invCount (σ * Equiv.swap c d)
      = if σ c < σ d then invCount σ + 1 else invCount σ - 1 := by
  classical
  have hcltd : c < d := by rw [Fin.lt_def]; omega
  have hcard := card_invSet_erase_swap hcd σ
  have hmemσ : (c, d) ∈ invSet σ ↔ σ d < σ c := by
    simp [mem_invSet, hcltd]
  have hmemσ' : (c, d) ∈ invSet (σ * Equiv.swap c d) ↔ σ c < σ d := by
    simp [mem_invSet, hcltd, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hne : σ c ≠ σ d := fun hcon => absurd (σ.injective hcon) (ne_of_lt hcltd)
  by_cases hlt : σ c < σ d
  · rw [ite_eq_left hlt]
    have h1 : (c, d) ∈ invSet (σ * Equiv.swap c d) := hmemσ'.2 hlt
    have h2 : (c, d) ∉ invSet σ := fun hcon => absurd (hmemσ.1 hcon) (not_lt.2 (le_of_lt hlt))
    rw [Finset.erase_eq_of_notMem h2] at hcard
    have := Finset.card_erase_add_one h1
    rw [invCount, invCount, ← this, hcard]
  · rw [ite_eq_right hlt]
    have hgt : σ d < σ c := lt_of_le_of_ne (not_lt.1 hlt) (fun hcon => hne hcon.symm)
    have h1 : (c, d) ∈ invSet σ := hmemσ.2 hgt
    have h2 : (c, d) ∉ invSet (σ * Equiv.swap c d) := fun hcon =>
      absurd (hmemσ'.1 hcon) hlt
    rw [Finset.erase_eq_of_notMem h2] at hcard
    have := Finset.card_erase_add_one h1
    rw [invCount, invCount, hcard, ← this]
    omega

end Adjacent

/-- Multiplying on the right by an adjacent transposition changes the number of inversions
by exactly one. -/
lemma invCount_mul_adjSwap {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    invCount (σ * adjSwap n i)
      = if σ i.castSucc < σ i.succ then invCount σ + 1 else invCount σ - 1 := by
  have hcd : ((i.castSucc : Fin (n + 1)) : ℕ) + 1 = ((i.succ : Fin (n + 1)) : ℕ) := rfl
  exact invCount_mul_swap hcd σ

lemma invCount_mul_adjSwap_cases {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    invCount (σ * adjSwap n i) = invCount σ + 1 ∨
      invCount (σ * adjSwap n i) + 1 = invCount σ := by
  rw [invCount_mul_adjSwap]
  by_cases h : σ i.castSucc < σ i.succ
  · exact Or.inl (by rw [ite_eq_left h])
  · refine Or.inr ?_
    rw [ite_eq_right h]
    have hpos : 0 < invCount σ := by
      have hne : σ i.succ < σ i.castSucc :=
        lt_of_le_of_ne (not_lt.1 h) fun hcon =>
          absurd (σ.injective hcon) (Fin.castSucc_lt_succ (i := i)).ne'
      have : (i.castSucc, i.succ) ∈ invSet σ :=
        mem_invSet.2 ⟨Fin.castSucc_lt_succ, hne⟩
      exact Finset.card_pos.2 ⟨_, this⟩
    omega

/-! ### The Coxeter length -/

/-- **The Coxeter length of a permutation is its number of inversions**: the minimal
number of adjacent transpositions needed to write a permutation of `Fin (n + 1)` is the
number of its inversions. -/
theorem length_eq_invCount {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    (permCoxeterSystem n).length σ = invCount σ := by
  refine le_antisymm ?_ ?_
  · -- `ℓ σ ≤ inv σ`, by induction on the number of inversions
    induction hk : invCount σ using Nat.strong_induction_on generalizing σ with
    | _ k ih =>
      subst hk
      rcases eq_or_ne σ 1 with rfl | hσ
      · simp
      obtain ⟨i, hi⟩ := exists_adjacent_descent hσ
      have hstep : invCount (σ * adjSwap n i) + 1 = invCount σ := by
        rw [invCount_mul_adjSwap, ite_eq_right (not_lt.2 (le_of_lt hi))]
        have : (i.castSucc, i.succ) ∈ invSet σ :=
          mem_invSet.2 ⟨Fin.castSucc_lt_succ, hi⟩
        have hpos : 0 < invCount σ := Finset.card_pos.2 ⟨_, this⟩
        omega
      have hih := ih (invCount (σ * adjSwap n i)) (by omega) (σ * adjSwap n i) rfl
      have hs : (permCoxeterSystem n).length (adjSwap n i) = 1 := by
        rw [← permCoxeterSystem_simple]
        exact (permCoxeterSystem n).length_simple i
      have hmul : (σ * adjSwap n i) * adjSwap n i = σ := by
        rw [mul_assoc, adjSwap, Equiv.swap_mul_self, mul_one]
      have hlen : (permCoxeterSystem n).length σ
          ≤ (permCoxeterSystem n).length (σ * adjSwap n i) + 1 := by
        have h := (permCoxeterSystem n).length_mul_le (σ * adjSwap n i) (adjSwap n i)
        rwa [hmul, hs] at h
      omega
  · -- `inv σ ≤ ℓ σ`, by induction on the length
    induction hk : (permCoxeterSystem n).length σ using Nat.strong_induction_on
      generalizing σ with
    | _ k ih =>
      subst hk
      rcases eq_or_ne σ 1 with rfl | hσ
      · simp
      obtain ⟨i, hi⟩ := (permCoxeterSystem n).exists_rightDescent_of_ne_one hσ
      have hlt : (permCoxeterSystem n).length (σ * adjSwap n i) + 1
          = (permCoxeterSystem n).length σ := by
        have h := ((permCoxeterSystem n).isRightDescent_iff).1 hi
        rwa [permCoxeterSystem_simple] at h
      have hih := ih ((permCoxeterSystem n).length (σ * adjSwap n i)) (by omega)
        (σ * adjSwap n i) rfl
      rcases invCount_mul_adjSwap_cases σ i with h | h <;> omega

/-- The signature of a permutation is `(-1)` to the number of its inversions. -/
theorem sign_eq_invCount {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm.sign σ = (-1) ^ invCount σ := by
  rw [← length_eq_invCount]
  obtain ⟨w, hw, hσ⟩ := (permCoxeterSystem n).exists_isReduced σ
  rw [hσ, hw.eq]
  clear hw hσ
  induction w with
  | nil => simp [CoxeterSystem.wordProd_nil]
  | cons i w ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, ih, List.length_cons, pow_succ]
    rw [permCoxeterSystem_simple, adjSwap, Equiv.Perm.sign_swap (Fin.ne_of_lt Fin.castSucc_lt_succ)]
    exact mul_comm _ _

/-- A simple reflection is a right descent of a permutation exactly when the permutation
has a descent at the corresponding pair of adjacent positions. -/
theorem isRightDescent_iff_lt {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    (permCoxeterSystem n).IsRightDescent σ i ↔ σ i.succ < σ i.castSucc := by
  rw [CoxeterSystem.IsRightDescent, permCoxeterSystem_simple, length_eq_invCount,
    length_eq_invCount, invCount_mul_adjSwap]
  constructor
  · intro h
    by_contra hcon
    rw [ite_eq_left (lt_of_le_of_ne (not_lt.1 hcon) fun hc =>
      absurd (σ.injective hc) (Fin.castSucc_lt_succ (i := i)).ne)] at h
    omega
  · intro h
    rw [ite_eq_right (not_lt.2 (le_of_lt h))]
    have hmem : (i.castSucc, i.succ) ∈ invSet σ := mem_invSet.2 ⟨Fin.castSucc_lt_succ, h⟩
    have : 0 < invCount σ := Finset.card_pos.2 ⟨_, hmem⟩
    omega

/-- The number of inversions is subadditive. -/
lemma invCount_mul_le {n : ℕ} (σ τ : Equiv.Perm (Fin (n + 1))) :
    invCount (σ * τ) ≤ invCount σ + invCount τ := by
  rw [← length_eq_invCount, ← length_eq_invCount, ← length_eq_invCount]
  exact (permCoxeterSystem n).length_mul_le σ τ

/-! ### The maximal number of inversions -/

/-- The number of pairs `i < j` of `Fin N`. -/
lemma card_pairs_lt (N : ℕ) :
    (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)).card = N.choose 2 := by
  classical
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  have h1 : ∀ j : Fin N, (∑ i : Fin N, if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter]
    have : (Finset.univ.filter (fun i : Fin N => i < j)) = Finset.Iio j := by ext i; simp
    rw [this, Fin.card_Iio]
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Fin.sum_univ_eq_sum_range (fun i => i) N]
  have h2 := Finset.sum_range_id_mul_two N
  have h3 : N.choose 2 = N * (N - 1) / 2 := Nat.choose_two_right N
  omega

/-- The inversions of a permutation of `Fin N` are among the `N.choose 2` pairs `i < j`. -/
lemma invCount_le (σ : Equiv.Perm (Fin N)) : invCount σ ≤ N.choose 2 := by
  classical
  have hsub : invSet σ ⊆ Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2) := by
    intro p hp
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (mem_invSet.1 hp).1⟩
  rw [invCount, ← card_pairs_lt N]
  exact Finset.card_le_card hsub

/-- Every pair is an inversion of the reversal permutation. -/
lemma invSet_revPerm :
    invSet (Fin.revPerm : Equiv.Perm (Fin N))
      = Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2) := by
  ext p
  simp only [mem_invSet, Finset.mem_filter, Finset.mem_univ, true_and, Fin.revPerm_apply]
  exact ⟨fun h => h.1, fun h => ⟨h, Fin.rev_lt_rev.2 h⟩⟩

/-- The reversal permutation has the maximal number of inversions. -/
lemma invCount_revPerm : invCount (Fin.revPerm : Equiv.Perm (Fin N)) = N.choose 2 := by
  rw [invCount, invSet_revPerm, card_pairs_lt]

/-- The reversal permutation is the longest element of the symmetric group. -/
theorem length_revPerm (n : ℕ) :
    (permCoxeterSystem n).length (Fin.revPerm : Equiv.Perm (Fin (n + 1)))
      = (n + 1).choose 2 := by
  rw [length_eq_invCount, invCount_revPerm]

theorem length_le_choose_two {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    (permCoxeterSystem n).length σ ≤ (n + 1).choose 2 := by
  rw [length_eq_invCount]
  exact invCount_le σ

/-- The number of inversions is invariant under taking the inverse. -/
lemma invCount_inv {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) : invCount σ⁻¹ = invCount σ := by
  rw [← length_eq_invCount, ← length_eq_invCount, CoxeterSystem.length_inv]

end Equiv.Perm
