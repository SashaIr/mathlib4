/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.Perm.SymmetricGroup.CycleType

/-!
# The tower of symmetric groups

This file ports the group-theoretic part of Coq-Combi's `SymGroup/towerSn.v`: the canonical
injection of `S_m × S_n` into `S_{m+n}` and the fact that it adds cycle types.

A permutation of `Fin m` and a permutation of `Fin n` are glued into a permutation of
`Fin (m + n)` by acting on the first `m` and on the last `n` letters separately; formally
this is the composition of `Equiv.Perm.sumCongr` with the transport of structure along
`finSumFinEquiv`.

## Main definitions

* `Equiv.Perm.tinj` : the monoid morphism `Perm (Fin m) × Perm (Fin n) →* Perm (Fin (m + n))`
  gluing two permutations (Coq: `tinj`).

## Main results

* `Equiv.Perm.cycleType_permCongr`, `Equiv.Perm.cycleType_sumCongr` : cycle types are
  invariant under transport of structure and add up under `Equiv.Perm.sumCongr`.
* `Equiv.Perm.tinj_injective` : `tinj` is injective (Coq: `tinj_inj`).
* `Equiv.Perm.cycleType_tinj` : `(tinj (u, v)).cycleType = u.cycleType + v.cycleType`
  (Coq: `cycle_type_tinj`).
* `Equiv.Perm.cycleTypeList_tinj` : the list-based cycle type of `tinj (u, v)` is the union of
  those of `u` and `v`.
-/

open Equiv

namespace Equiv.Perm


variable {α β : Type*}

/-! ### Transport of structure -/

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Cycle types are invariant under transport of structure. -/
@[simp] lemma cycleType_permCongr (e : α ≃ β) (σ : Perm α) :
    (e.permCongr σ).cycleType = σ.cycleType := by
  classical
  have h : e.permCongr σ
      = σ.extendDomain (e.trans (Equiv.subtypeUnivEquiv (fun _ : β => trivial)).symm) := by
    ext x
    rw [Perm.extendDomain_apply_subtype _ _ trivial]
    simp
  rw [h, cycleType_extendDomain]

/-! ### Gluing two permutations -/

/-- A permutation of `α` acting on the left summand of `α ⊕ β` has the same cycle type. -/
lemma cycleType_sumCongr_one (u : Perm α) :
    (Perm.sumCongr u (1 : Perm β)).cycleType = u.cycleType := by
  classical
  have h : Perm.sumCongr u (1 : Perm β)
      = u.extendDomain (Equiv.ofInjective (Sum.inl : α → α ⊕ β) Sum.inl_injective) := by
    ext x
    cases x with
    | inl a =>
      rw [Perm.extendDomain_apply_subtype _ _ ⟨a, rfl⟩]
      simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.ofInjective_apply,
        Equiv.ofInjective_symm_apply]
    | inr b =>
      rw [Perm.extendDomain_apply_not_subtype]
      · simp
      · rintro ⟨a, ha⟩; exact absurd ha (by simp)
  rw [h, cycleType_extendDomain]

/-- A permutation of `β` acting on the right summand of `α ⊕ β` has the same cycle type. -/
lemma cycleType_one_sumCongr (v : Perm β) :
    (Perm.sumCongr (1 : Perm α) v).cycleType = v.cycleType := by
  classical
  have h : Perm.sumCongr (1 : Perm α) v
      = v.extendDomain (Equiv.ofInjective (Sum.inr : β → α ⊕ β) Sum.inr_injective) := by
    ext x
    cases x with
    | inr b =>
      rw [Perm.extendDomain_apply_subtype _ _ ⟨b, rfl⟩]
      simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.ofInjective_apply,
        Equiv.ofInjective_symm_apply]
    | inl a =>
      rw [Perm.extendDomain_apply_not_subtype]
      · simp
      · rintro ⟨b, hb⟩; exact absurd hb (by simp)
  rw [h, cycleType_extendDomain]

/-- The cycle type of a permutation acting separately on the two summands of `α ⊕ β` is the
union of the two cycle types. -/
lemma cycleType_sumCongr (u : Perm α) (v : Perm β) :
    (Perm.sumCongr u v).cycleType = u.cycleType + v.cycleType := by
  have hmul : Perm.sumCongr u v = Perm.sumCongr u 1 * Perm.sumCongr 1 v := by
    ext x; cases x <;> simp
  have hdisj : Perm.Disjoint (Perm.sumCongr u (1 : Perm β)) (Perm.sumCongr (1 : Perm α) v) := by
    intro x
    cases x with
    | inl a => right; simp
    | inr b => left; simp
  rw [hmul, hdisj.cycleType_mul, cycleType_sumCongr_one, cycleType_one_sumCongr]

variable {m n : ℕ}

/-- The canonical injection of `S_m × S_n` into `S_{m+n}`: the two permutations act on the
first `m` and on the last `n` letters respectively (Coq: `tinj`). -/
def tinj (m n : ℕ) : Perm (Fin m) × Perm (Fin n) →* Perm (Fin (m + n)) :=
  (Equiv.permCongrHom finSumFinEquiv).toMonoidHom.comp (Perm.sumCongrHom (Fin m) (Fin n))

lemma tinj_apply (u : Perm (Fin m)) (v : Perm (Fin n)) (x : Fin (m + n)) :
    tinj m n (u, v) x = finSumFinEquiv (Sum.map u v (finSumFinEquiv.symm x)) := rfl

/-- The injection of the tower of symmetric groups is injective (Coq: `tinj_inj`). -/
lemma tinj_injective (m n : ℕ) : Function.Injective (tinj m n) :=
  (Equiv.permCongrHom finSumFinEquiv).injective.comp Perm.sumCongrHom_injective

/-- The cycle type of a glued pair of permutations is the union of the two cycle types
(Coq: `cycle_type_tinj`). -/
theorem cycleType_tinj (u : Perm (Fin m)) (v : Perm (Fin n)) :
    (tinj m n (u, v)).cycleType = u.cycleType + v.cycleType := by
  rw [tinj, MonoidHom.comp_apply, Perm.sumCongrHom_apply]
  exact (cycleType_permCongr _ _).trans (cycleType_sumCongr u v)

/-- The partition attached to a glued pair of permutations is the union of the two
partitions. -/
lemma partition_parts_tinj (u : Perm (Fin m)) (v : Perm (Fin n)) :
    (tinj m n (u, v)).partition.parts = u.partition.parts + v.partition.parts := by
  have hu : u.support.card ≤ m := by simpa using Finset.card_le_univ u.support
  have hv : v.support.card ≤ n := by simpa using Finset.card_le_univ v.support
  have hcard : (tinj m n (u, v)).support.card = u.support.card + v.support.card := by
    rw [← Equiv.Perm.sum_cycleType, ← Equiv.Perm.sum_cycleType, ← Equiv.Perm.sum_cycleType,
      cycleType_tinj, Multiset.sum_add]
  simp only [Equiv.Perm.partition, cycleType_tinj, Fintype.card_fin, hcard]
  rw [show m + n - (u.support.card + v.support.card)
      = (m - u.support.card) + (n - v.support.card) by omega,
    Multiset.replicate_add]
  abel

/-- The list-based cycle type of a glued pair of permutations is the union of the cycle
types of the two factors. -/
theorem cycleTypeList_tinj (u : Perm (Fin m)) (v : Perm (Fin n)) :
    cycleTypeList (tinj m n (u, v))
      = List.sortDesc ((cycleTypeList u : Multiset ℕ) + (cycleTypeList v : Multiset ℕ)) := by
  rw [cycleTypeList, partition_parts_tinj, coe_cycleTypeList, coe_cycleTypeList]

end Equiv.Perm
