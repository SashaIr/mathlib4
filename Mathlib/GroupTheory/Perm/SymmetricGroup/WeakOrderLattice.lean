/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.GroupTheory.Perm.SymmetricGroup.Biclosed
public import Mathlib.GroupTheory.Perm.SymmetricGroup.WeakOrder
public import Mathlib.Order.Finite.Lattice

/-!
# The right weak order on the symmetric group is a lattice

Following `theories/SymGroup/weak_order.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we equip the symmetric group with the
right weak order and show that it is a lattice.

By `Equiv.Perm.rightWeakLe_iff_subset`, the right weak order is the inclusion order on the
sets `invSet u⁻¹` of inversions, and by `Equiv.Perm.isBiclosed_iff_exists_invSet` these
sets are exactly the biclosed sets of pairs.  The transitive closure of the union of two
biclosed sets is biclosed (`Equiv.Perm.isBiclosed_closurePairs_union`), so it is the
inversion set of a permutation, which is then the join of the two permutations.  A finite
join-semilattice with a least element (here the identity) is a lattice, so the right weak
order is a lattice.

The order is carried by the type synonym `Equiv.Perm.RightWeakOrder n` for
`Equiv.Perm (Fin (n + 1))`, so that the order instances do not interfere with the group
structure.

## Main definitions and results

* `Equiv.Perm.joinPerm` : the join of two permutations for the right weak order, and
  `Equiv.Perm.invSet_inv_joinPerm` : its inversion set is the transitive closure of the
  union of the two inversion sets.
* `Equiv.Perm.RightWeakOrder` : the symmetric group with the right weak order, with
  instances `PartialOrder`, `OrderBot`, `OrderTop`, `SemilatticeSup` and
  **`Lattice`**.
-/

@[expose] public section

open Equiv Finset

namespace Equiv.Perm

variable {n : ℕ}

/-! ### The join of two permutations -/

/-- The join of two permutations for the right weak order: the permutation whose inverse
has as inversions the transitive closure of the union of the inversions of `u⁻¹` and of
`v⁻¹`. -/
noncomputable def joinPerm (u v : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Fin (n + 1)) :=
  (permOfBiclosed
    (isBiclosed_closurePairs_union (isBiclosed_invSet u⁻¹) (isBiclosed_invSet v⁻¹)))⁻¹

/-- The inversions of the inverse of `joinPerm u v` are the transitive closure of the
union of the inversions of `u⁻¹` and of `v⁻¹`. -/
lemma invSet_inv_joinPerm (u v : Equiv.Perm (Fin (n + 1))) :
    invSet (joinPerm u v)⁻¹ = closurePairs (invSet u⁻¹ ∪ invSet v⁻¹) := by
  rw [joinPerm, inv_inv, invSet_permOfBiclosed]

/-- An inversion set is closed under transitivity. -/
lemma invSet_trans {N : ℕ} {σ : Equiv.Perm (Fin N)} {a b c : Fin N} (hab : (a, b) ∈ invSet σ)
    (hbc : (b, c) ∈ invSet σ) : (a, c) ∈ invSet σ :=
  (isBiclosed_invSet σ).closed ((isBiclosed_invSet σ).lt _ hab)
    ((isBiclosed_invSet σ).lt _ hbc) hab hbc

lemma rightWeakLe_joinPerm_left (u v : Equiv.Perm (Fin (n + 1))) :
    RightWeakLe u (joinPerm u v) := by
  rw [rightWeakLe_iff_subset, invSet_inv_joinPerm]
  exact (Finset.subset_union_left).trans (subset_closurePairs _)

lemma rightWeakLe_joinPerm_right (u v : Equiv.Perm (Fin (n + 1))) :
    RightWeakLe v (joinPerm u v) := by
  rw [rightWeakLe_iff_subset, invSet_inv_joinPerm]
  exact (Finset.subset_union_right).trans (subset_closurePairs _)

lemma joinPerm_rightWeakLe {u v w : Equiv.Perm (Fin (n + 1))} (hu : RightWeakLe u w)
    (hv : RightWeakLe v w) : RightWeakLe (joinPerm u v) w := by
  rw [rightWeakLe_iff_subset] at hu hv ⊢
  rw [invSet_inv_joinPerm]
  rintro ⟨a, b⟩ hp
  exact closurePairs_subset (Finset.union_subset hu hv) invSet_trans hp

/-! ### The lattice structure -/

/-- The symmetric group on `n + 1` letters, seen as an ordered set for the right weak
order. -/
def RightWeakOrder (n : ℕ) : Type := Equiv.Perm (Fin (n + 1))

namespace RightWeakOrder

/-- The permutation underlying an element of `RightWeakOrder n`. -/
def toPerm (u : RightWeakOrder n) : Equiv.Perm (Fin (n + 1)) := u

/-- An element of `RightWeakOrder n` from a permutation. -/
def ofPerm (u : Equiv.Perm (Fin (n + 1))) : RightWeakOrder n := u

@[simp] lemma toPerm_ofPerm (u : Equiv.Perm (Fin (n + 1))) : toPerm (ofPerm u) = u := rfl

@[simp] lemma ofPerm_toPerm (u : RightWeakOrder n) : ofPerm (toPerm u) = u := rfl

lemma toPerm_injective : Function.Injective (toPerm (n := n)) := fun _ _ h => h

instance : Finite (RightWeakOrder n) := inferInstanceAs (Finite (Equiv.Perm (Fin (n + 1))))

instance : DecidableEq (RightWeakOrder n) :=
  inferInstanceAs (DecidableEq (Equiv.Perm (Fin (n + 1))))

instance instPartialOrder : PartialOrder (RightWeakOrder n) where
  le u v := RightWeakLe (toPerm u) (toPerm v)
  le_refl u := rightWeakLe_refl (toPerm u)
  le_trans _ _ _ huv hvw := rightWeakLe_trans huv hvw
  le_antisymm _ _ huv hvu := toPerm_injective (rightWeakLe_antisymm huv hvu)

lemma le_def {u v : RightWeakOrder n} : u ≤ v ↔ RightWeakLe (toPerm u) (toPerm v) := Iff.rfl

/-- The right weak order is the inclusion of the inversion sets of the inverses. -/
lemma le_iff_subset {u v : RightWeakOrder n} :
    u ≤ v ↔ invSet (toPerm u)⁻¹ ⊆ invSet (toPerm v)⁻¹ :=
  rightWeakLe_iff_subset _ _

/-- The identity is the least element of the right weak order. -/
instance instOrderBot : OrderBot (RightWeakOrder n) where
  bot := ofPerm 1
  bot_le u := rightWeakLe_one (toPerm u)

/-- The reversal permutation is the greatest element of the right weak order. -/
instance instOrderTop : OrderTop (RightWeakOrder n) where
  top := ofPerm Fin.revPerm
  le_top u := rightWeakLe_revPerm (toPerm u)

@[simp] lemma toPerm_bot : toPerm (⊥ : RightWeakOrder n) = 1 := rfl

@[simp] lemma toPerm_top : toPerm (⊤ : RightWeakOrder n) = Fin.revPerm := rfl

noncomputable instance instSemilatticeSup : SemilatticeSup (RightWeakOrder n) where
  sup u v := ofPerm (joinPerm (toPerm u) (toPerm v))
  le_sup_left u v := rightWeakLe_joinPerm_left (toPerm u) (toPerm v)
  le_sup_right u v := rightWeakLe_joinPerm_right (toPerm u) (toPerm v)
  sup_le _ _ _ hu hv := joinPerm_rightWeakLe hu hv

@[simp] lemma toPerm_sup (u v : RightWeakOrder n) :
    toPerm (u ⊔ v) = joinPerm (toPerm u) (toPerm v) := rfl

/-- **The right weak order on the symmetric group is a lattice.** -/
noncomputable instance instLattice : Lattice (RightWeakOrder n) := Finite.toLatticeOfSup _

end RightWeakOrder

end Equiv.Perm
