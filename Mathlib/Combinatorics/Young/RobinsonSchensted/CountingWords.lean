/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.RobinsonSchensted.Counting

/-!
# Counting words over a finite alphabet with the Robinson–Schensted correspondence

Applying the bijection `List.RS_RSQ_bijOn` to the words of length `n` over the alphabet
`Fin m` gives the classical identity

`∑_λ K_λ(m) · f^λ = m ^ n`,

the sum being over the partitions `λ` of `n`, where `K_λ(m)` is the number of tableaux of
shape `λ` with entries in `Fin m` and `f^λ` is the number of standard tableaux of shape
`λ`.

## Main definitions

* `List.tabPair m n` : the pairs consisting of a tableau over `Fin m` and a standard
  tableau of the same shape with `n` boxes.
* `List.numTab m sh` : the number of tableaux of shape `sh` with entries in `Fin m`.

## Main results

* `List.card_word` : there are `m ^ n` words of length `n` over `Fin m`.
* `List.RS_RSQ_bijOn_word` : the Robinson–Schensted correspondence restricted to the
  words of length `n` over `Fin m`.
* `List.sum_numTab_mul_numStdTab` : `∑_λ K_λ(m) · f^λ = m ^ n`.
-/

namespace List

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

/-! ### The identity `∑_λ K_λ(m) · f^λ = m ^ n` -/

/-- The number `K_sh(m)` of tableaux of shape `sh` with entries in `Fin m`. -/
noncomputable def numTab (m : ℕ) (sh : List ℕ) : ℕ :=
  Nat.card {P : List (List (Fin m)) // IsTableau P ∧ shape P = sh}

/-- The common shape of such a pair, as a partition of `n`. -/
def tabPairShape (m n : ℕ) (p : tabPair m n) : Nat.Partition n :=
  listPartEquivNatPartition n ⟨shape p.1.1, isPart_shape p.2.1, p.2.2.2.2⟩

lemma partsList_tabPairShape (m n : ℕ) (p : tabPair m n) :
    (tabPairShape m n p).partsList = shape p.1.1 :=
  sortDesc_coe (isPart_shape p.2.1)

/-- The pairs with prescribed shape `lam` are the pairs of a tableau over `Fin m` of shape
`lam` and a standard tableau of shape `lam`. -/
def tabPairFiberEquiv (m n : ℕ) (lam : Nat.Partition n) :
    {p : tabPair m n // tabPairShape m n p = lam} ≃
      {P : List (List (Fin m)) // IsTableau P ∧ shape P = lam.partsList} ×
        {Q : List (List ℕ) // IsStdTab Q ∧ shape Q = lam.partsList} where
  toFun p :=
    have h1 : shape p.1.1.1 = lam.partsList := by
      rw [← partsList_tabPairShape m n p.1, p.2]
    (⟨p.1.1.1, p.1.2.1, h1⟩, ⟨p.1.1.2, p.1.2.2.1, by rw [p.1.2.2.2.1, h1]⟩)
  invFun q :=
    ⟨⟨(q.1.1, q.2.1), q.1.2.1, q.2.2.1, by rw [q.1.2.2, q.2.2.2], by
        change (shape q.1.1).sum = n
        rw [q.1.2.2, Nat.Partition.sum_partsList]⟩,
      Nat.Partition.ext (by
        change ((shape q.1.1 : List ℕ) : Multiset ℕ) = lam.parts
        rw [q.1.2.2, Nat.Partition.coe_partsList])⟩
  left_inv p := rfl
  right_inv q := rfl

/-- The Robinson–Schensted identity `∑_λ K_λ(m) · f^λ = m ^ n`, the sum being over the
partitions `λ` of `n`. -/
theorem sum_numTab_mul_numStdTab (m n : ℕ) :
    ∑ lam : Nat.Partition n, numTab m lam.partsList * numStdTab lam.partsList = m ^ n := by
  have h1 : Nat.card (tabPair m n) = ∑ lam : Nat.Partition n,
      Nat.card {p : tabPair m n // tabPairShape m n p = lam} := by
    rw [← Nat.card_sigma]
    exact (Nat.card_congr (Equiv.sigmaFiberEquiv (tabPairShape m n))).symm
  rw [← card_tabPair m n, h1]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [Nat.card_congr (tabPairFiberEquiv m n lam), Nat.card_prod, numTab, numStdTab]

end List
