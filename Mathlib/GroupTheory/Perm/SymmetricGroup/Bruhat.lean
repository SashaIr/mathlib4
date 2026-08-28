/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.GroupTheory.Perm.SymmetricGroup.Rank

/-!
# The strong Bruhat order on the symmetric group

Following `theories/SymGroup/Bruhat.v` of [Coq-Combi](https://github.com/math-comp/Coq-Combi), we
define the (strong) Bruhat order on the symmetric group of `Fin n` through the rank functions of
`Mathlib/GroupTheory/Perm/SymmetricGroup/Rank.lean`: a permutation `s` is smaller than `t`
when all the values of the rank function of `t` are at most those of `s`.

## Main definitions and results

* `Equiv.Perm.BruhatLE s t` : the Bruhat order `s ≤ t` (Coq `Bruhat`).
* `Equiv.Perm.bruhatLE_refl`, `Equiv.Perm.bruhatLE_trans`, `Equiv.Perm.bruhatLE_antisymm` : it is a
  partial order, packaged as `Equiv.Perm.bruhatPartialOrder`.
* `Equiv.Perm.bruhatLE_one_left` : the identity is the smallest element (Coq `Bruhat1s`).
* `Equiv.Perm.bruhatLE_revPerm_right` : the reversal permutation, that is the longest element
  of the symmetric group, is the largest element (Coq `Bruhat_maxperm`).
* `Equiv.Perm.bruhatLE_inv_iff` : the Bruhat order is invariant under taking inverses (Coq
  `BruhatV`).
* `Equiv.Perm.bruhatLE_revPerm_mul_iff`, `Equiv.Perm.bruhatLE_mul_revPerm_iff` : multiplying by the
  longest element on either side reverses the Bruhat order (Coq `Bruhat_Mmax` and
  `Bruhat_maxM`), while conjugating by it preserves the order
  (`Equiv.Perm.bruhatLE_conj_revPerm_iff`, Coq `Bruhat_conj_max`).
-/

open Equiv

namespace Equiv.Perm


variable {n : ℕ}

/-- The (strong) Bruhat order on the symmetric group: `s` is below `t` when every value
of the rank function of `t` is at most the corresponding value for `s`. -/
def BruhatLE (s t : Perm (Fin n)) : Prop := ∀ i j : ℕ, permRank t i j ≤ permRank s i j

lemma bruhatLE_refl (s : Perm (Fin n)) : BruhatLE s s := fun _ _ => le_rfl

lemma bruhatLE_trans {s t u : Perm (Fin n)} (hst : BruhatLE s t) (htu : BruhatLE t u) :
    BruhatLE s u := fun i j => (htu i j).trans (hst i j)

lemma bruhatLE_antisymm {s t : Perm (Fin n)} (hst : BruhatLE s t) (hts : BruhatLE t s) :
    s = t :=
  permRank_injective (funext fun i => funext fun j => le_antisymm (hts i j) (hst i j))

/-- The Bruhat order is a partial order on the symmetric group. -/
def bruhatPartialOrder : PartialOrder (Perm (Fin n)) where
  le := BruhatLE
  le_refl := bruhatLE_refl
  le_trans _ _ _ := bruhatLE_trans
  le_antisymm _ _ := bruhatLE_antisymm

/-- The identity is the smallest permutation for the Bruhat order (Coq `Bruhat1s`). -/
theorem bruhatLE_one_left (s : Perm (Fin n)) : BruhatLE 1 s := by
  intro i j
  have h1 := permRank_le_left s i j
  have h2 := permRank_le_right s i j
  rw [permRank_one]
  omega

/-- The reversal permutation, the longest element of the symmetric group, is the largest
permutation for the Bruhat order (Coq `Bruhat_maxperm`). -/
theorem bruhatLE_revPerm_right (s : Perm (Fin n)) :
    BruhatLE s (Fin.revPerm : Perm (Fin n)) := by
  intro i j
  have h := le_permRank_add s i j
  rw [permRank_revPerm]
  omega

/-- The Bruhat order is invariant under taking inverses (Coq `BruhatV`). -/
theorem bruhatLE_inv_iff (s t : Perm (Fin n)) : BruhatLE s⁻¹ t⁻¹ ↔ BruhatLE s t := by
  constructor
  · intro h i j
    have := h j i
    rwa [permRank_inv, permRank_inv] at this
  · intro h i j
    rw [permRank_inv, permRank_inv]
    exact h j i

/-- Multiplying on the left by the longest element reverses the Bruhat order (Coq
`Bruhat_Mmax`). -/
theorem bruhatLE_revPerm_mul_iff (s t : Perm (Fin n)) :
    BruhatLE ((Fin.revPerm : Perm (Fin n)) * s) ((Fin.revPerm : Perm (Fin n)) * t)
      ↔ BruhatLE t s := by
  constructor
  · intro h i j
    have hj := h i (n - min j n)
    rw [permRank_revPerm_mul, permRank_revPerm_mul,
      show n - (n - min j n) = min j n by have := min_le_right j n; omega,
      permRank_min_right, permRank_min_right] at hj
    have h1 := permRank_le_left s i j
    have h2 := permRank_le_left t i j
    omega
  · intro h i j
    rw [permRank_revPerm_mul, permRank_revPerm_mul]
    have hj := h i (n - j)
    have h1 := permRank_le_left s i (n - j)
    have h2 := permRank_le_left t i (n - j)
    omega

/-- Multiplying on the right by the longest element reverses the Bruhat order (Coq
`Bruhat_maxM`). -/
theorem bruhatLE_mul_revPerm_iff (s t : Perm (Fin n)) :
    BruhatLE (s * (Fin.revPerm : Perm (Fin n))) (t * (Fin.revPerm : Perm (Fin n)))
      ↔ BruhatLE t s := by
  constructor
  · intro h i j
    have hi := h (n - min i n) j
    rw [permRank_mul_revPerm, permRank_mul_revPerm,
      show n - (n - min i n) = min i n by have := min_le_right i n; omega,
      permRank_min_left, permRank_min_left] at hi
    have h1 := permRank_le_right s i j
    have h2 := permRank_le_right t i j
    omega
  · intro h i j
    rw [permRank_mul_revPerm, permRank_mul_revPerm]
    have hi := h (n - i) j
    have h1 := permRank_le_right s (n - i) j
    have h2 := permRank_le_right t (n - i) j
    omega

/-- Conjugating by the longest element preserves the Bruhat order (Coq
`Bruhat_conj_max`). -/
theorem bruhatLE_conj_revPerm_iff (s t : Perm (Fin n)) :
    BruhatLE ((Fin.revPerm : Perm (Fin n)) * s * (Fin.revPerm : Perm (Fin n)))
        ((Fin.revPerm : Perm (Fin n)) * t * (Fin.revPerm : Perm (Fin n)))
      ↔ BruhatLE s t := by
  rw [bruhatLE_mul_revPerm_iff, bruhatLE_revPerm_mul_iff]

end Equiv.Perm
