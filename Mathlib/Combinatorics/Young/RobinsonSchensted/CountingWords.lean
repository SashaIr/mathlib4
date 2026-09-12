/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.RobinsonSchensted.Counting

/-!
# Counting words over a finite alphabet with the Robinson–Schensted correspondence

Applying the bijection `Young.RS_RSQ_bijOn` to the words of length `n` over the alphabet
`Fin m` gives the classical identity

`∑_μ K_μ(m) · f^μ = m ^ n`,

the sum being over the partitions `μ` of `n`, where `K_μ(m)` is the number of tableaux of
shape `μ` with entries in `Fin m` and `f^μ` is the number of standard tableaux of shape
`μ`.

## Main definitions

* `Young.tabPair m n` : the pairs consisting of a tableau over `Fin m` and a standard
  tableau of the same shape with `n` boxes.
* `Young.numTab m μ` : the number of tableaux of shape `μ` with entries in `Fin m`.

## Main results

* `Young.card_word` : there are `m ^ n` words of length `n` over `Fin m`.
* `Young.RS_RSQ_bijOn_word` : the Robinson–Schensted correspondence restricted to the
  words of length `n` over `Fin m`.
* `Young.sum_numTab_mul_numStdTab` : `∑_μ K_μ(m) · f^μ = m ^ n`.
-/

@[expose] public section

namespace Young

open List

/-! ### Words of a given length over a finite alphabet -/

/-- The words of length `n` over the alphabet `Fin m`. -/
def wordSet (m n : ℕ) : Set (List (Fin m)) := {w | w.length = n}

/-- There are `m ^ n` words of length `n` over `Fin m`. -/
theorem card_word (m n : ℕ) : Nat.card (wordSet m n) = m ^ n := by
  have h : Nat.card (List.Vector (Fin m) n) = m ^ n := by
    rw [Nat.card_eq_fintype_card, card_vector, Fintype.card_fin]
  exact h

instance finite_wordSet (m n : ℕ) : Finite (wordSet m n) :=
  Finite.of_equiv (List.Vector (Fin m) n) (Equiv.refl _)

/-! ### Pairs of a tableau and a standard tableau -/

/-- The pairs consisting of a tableau over `Fin m` and a standard tableau of the same
shape with `n` boxes. -/
def tabPair (m n : ℕ) : Set (List (List (Fin m)) × List (List ℕ)) :=
  {p | IsTableau p.1 ∧ IsStdTab p.2 ∧ shape p.2 = shape p.1 ∧ sizeTab p.1 = n}

/-- The Robinson–Schensted correspondence is a bijection between the words of length `n`
over `Fin m` and the pairs consisting of a tableau over `Fin m` and a standard tableau of
the same shape with `n` boxes. -/
theorem RS_RSQ_bijOn_word (m n : ℕ) :
    Set.BijOn (fun w : List (Fin m) => (RS w, RSQ w)) (wordSet m n) (tabPair m n) := by
  have hbij := RS_RSQ_bijOn (T := Fin m)
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨h1, h2, h3⟩ := hbij.mapsTo (Set.mem_univ w)
    exact ⟨h1, h2, h3, by rw [sizeTab_RS, hw]⟩
  · exact hbij.injOn.mono (Set.subset_univ _)
  · rintro p ⟨h1, h2, h3, h4⟩
    obtain ⟨w, -, hfw⟩ := hbij.surjOn ⟨h1, h2, h3⟩
    have hlen : w.length = n := by
      have hp : RS w = p.1 := congrArg Prod.fst hfw
      rw [← sizeTab_RS w, hp, h4]
    exact ⟨w, hlen, hfw⟩

theorem card_tabPair (m n : ℕ) : Nat.card (tabPair m n) = m ^ n := by
  rw [← card_word m n]
  exact (Nat.card_congr (RS_RSQ_bijOn_word m n).equiv).symm

instance finite_tabPair (m n : ℕ) : Finite (tabPair m n) :=
  Finite.of_equiv _ (RS_RSQ_bijOn_word m n).equiv

/-! ### The identity `∑_μ K_μ(m) · f^μ = m ^ n` -/

/-- The number `K_μ(m)` of tableaux of shape `μ` with entries in `Fin m`. -/
noncomputable def numTab (m : ℕ) (μ : List ℕ) : ℕ :=
  Nat.card {P : List (List (Fin m)) // IsTableau P ∧ shape P = μ}

/-- The common shape of such a pair, as a partition of `n`. -/
def tabPairShape (m n : ℕ) (p : tabPair m n) : Nat.Partition n :=
  listPartEquivNatPartition n ⟨shape p.1.1, isPart_shape p.2.1, p.2.2.2.2⟩

lemma partsList_tabPairShape (m n : ℕ) (p : tabPair m n) :
    (tabPairShape m n p).partsList = shape p.1.1 :=
  sortDesc_coe (isPart_shape p.2.1)

/-- The pairs with prescribed shape `μ` are the pairs of a tableau over `Fin m` of shape
`μ` and a standard tableau of shape `μ`. -/
def tabPairFiberEquiv (m n : ℕ) (μ : Nat.Partition n) :
    {p : tabPair m n // tabPairShape m n p = μ} ≃
      {P : List (List (Fin m)) // IsTableau P ∧ shape P = μ.partsList} ×
        {Q : List (List ℕ) // IsStdTab Q ∧ shape Q = μ.partsList} where
  toFun p :=
    have h1 : shape p.1.1.1 = μ.partsList := by
      rw [← partsList_tabPairShape m n p.1, p.2]
    (⟨p.1.1.1, p.1.2.1, h1⟩, ⟨p.1.1.2, p.1.2.2.1, by rw [p.1.2.2.2.1, h1]⟩)
  invFun q :=
    ⟨⟨(q.1.1, q.2.1), q.1.2.1, q.2.2.1, by rw [q.1.2.2, q.2.2.2], by
        change (shape q.1.1).sum = n
        rw [q.1.2.2, Nat.Partition.sum_partsList]⟩,
      Nat.Partition.ext (by
        change ((shape q.1.1 : List ℕ) : Multiset ℕ) = μ.parts
        rw [q.1.2.2, Nat.Partition.coe_partsList])⟩
  left_inv p := rfl
  right_inv q := rfl

/-- The Robinson–Schensted identity `∑_μ K_μ(m) · f^μ = m ^ n`, the sum being over the
partitions `μ` of `n`. -/
theorem sum_numTab_mul_numStdTab (m n : ℕ) :
    ∑ μ : Nat.Partition n, numTab m μ.partsList * numStdTab μ.partsList = m ^ n := by
  have h1 : Nat.card (tabPair m n) = ∑ μ : Nat.Partition n,
      Nat.card {p : tabPair m n // tabPairShape m n p = μ} := by
    rw [← Nat.card_sigma]
    exact (Nat.card_congr (Equiv.sigmaFiberEquiv (tabPairShape m n))).symm
  rw [← card_tabPair m n, h1]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Nat.card_congr (tabPairFiberEquiv m n μ), Nat.card_prod, numTab, numStdTab]

end Young
