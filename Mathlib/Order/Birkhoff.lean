/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Filipo A. E. Nuccio, Sam van Gool
-/
import Mathlib.Data.Finset.LocallyFinite.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.Order.Irreducible
import Mathlib.Order.UpperLower.Basic

/-!
# Birkhoff's representation theorem

This file proves the Birkhoff representation theorem: Any finite partial order can be
represented as a sublattice of some powerset algebra. If it is a distributive lattice, this can
be refined.

Precisely, any nonempty partial order is isomorphic to the order of its irreducible lower sets.
Conversely, any nonempty finite distributive lattice is isomorphic to the lattice of lower sets of
its irreducible elements.

## Main declarations

For a nonempty partial order `α`:
* `OrderEmbeddng.supIrredLowerSet`: `α` is isomorphic to the order of its irreducible lower sets.
If, moreover, `a` is a finite distributive lattice:
* `OrderIso.lowerSetSupIrred`: `α` is isomorphic to the lattice of lower sets of its irreducible
  elements.
* `OrderEmbedding.birkhoffSet`, `OrderEmbedding.birkhoffFinset`: Order embedding of `α` into the
  powerset lattice of its irreducible elements.
* `LatticeHom.birkhoffSet`, `LatticeHom.birkhoffFinet`: Same as the previous two, but bundled as
  an injective lattice homomorphism.
* `exists_birkhoff_representation`: `α` embeds into some powerset algebra. You should prefer using
  this over the explicit Birkhoff embedding because the Birkhoff embedding is littered with
  decidability footguns that this existential-packaged version can afford to avoid.

## See also

This correspondence between finite distributive lattices and finite boolean algebras is made
functorial in... TODO: Actually do it.

## Tags

birkhoff, representation, stone duality, lattice embedding
-/

open Finset Function OrderDual

variable {α : Type*}

namespace UpperSet
variable [SemilatticeInf α] {s : UpperSet α} {a : α}

@[simp] lemma infIrred_Ici (a : α) : InfIrred (Ici a) := by
  refine ⟨fun h ↦ Ici_ne_top h.eq_top, fun s t hst ↦ ?_⟩
  have := mem_Ici_iff.2 (le_refl a)
  rw [← hst] at this
  exact this.imp (fun ha ↦ le_antisymm (le_Ici.2 ha) <| hst.ge.trans inf_le_left) fun ha ↦
      le_antisymm (le_Ici.2 ha) <| hst.ge.trans inf_le_right

variable [Finite α]

@[simp] lemma infIrred_iff_of_finite : InfIrred s ↔ ∃ a, Ici a = s := by
  refine' ⟨fun hs ↦ _, _⟩
  · obtain ⟨a, ha, has⟩ := (s : Set α).toFinite.exists_minimal_wrt id _ (coe_nonempty.2 hs.ne_top)
    exact ⟨a, (hs.2 <| erase_inf_Ici ha <| by simpa [eq_comm] using has).resolve_left
      (lt_erase.2 ha).ne'⟩
  · rintro ⟨a, rfl⟩
    exact infIrred_Ici _

end UpperSet

namespace LowerSet
variable [PartialOrder α] {s : LowerSet α}

@[simp] lemma supIrred_Iic (a : α) : SupIrred (Iic a) := by
  refine' ⟨fun h ↦ Iic_ne_bot h.eq_bot, fun s t hst ↦ _⟩
  have := mem_Iic_iff.2 (le_refl a)
  rw [← hst] at this
  exact this.imp (fun ha ↦ (le_sup_left.trans_eq hst).antisymm <| Iic_le.2 ha) fun ha ↦
    (le_sup_right.trans_eq hst).antisymm <| Iic_le.2 ha

@[simp] lemma  supIrred_iff_of_finite [Finite α] : SupIrred s ↔ ∃ a, Iic a = s := by
  refine' ⟨fun hs ↦ _, _⟩
  · obtain ⟨a, ha, has⟩ := (s : Set α).toFinite.exists_maximal_wrt id _ (coe_nonempty.2 hs.ne_bot)
    exact ⟨a, (hs.2 <| erase_sup_Iic ha <| by simpa [eq_comm] using has).resolve_left
      (erase_lt.2 ha).ne⟩
  · rintro ⟨a, rfl⟩
    exact supIrred_Iic _

end LowerSet
section PartialOrder
variable [PartialOrder α] [Fintype α]

open LowerSet

open scoped Classical

variable (α)

/-- **Birkhoff's Embedding Theorem**. Any nonempty finite distributive lattice can be embedded
into its lattice of sup-irreducible lower sets. -/
def OrderEmbedding.supIrredLowerSet : α ↪o {s : LowerSet α // SupIrred s} where
  toFun := fun a => ⟨LowerSet.Iic a, by simp only [supIrred_Iic]⟩
  inj' := fun _ => by simp_all only [Subtype.mk.injEq, LowerSet.Iic_inj, implies_true]
  map_rel_iff' := by simp only [Function.Embedding.coeFn_mk, Subtype.mk_le_mk, Iic_le, mem_Iic_iff,
    implies_true]

variable {α}

lemma OrderEmbedding.supIrredLowerSet_apply {a : α} {s : LowerSet α} (ha : LowerSet.Iic a = s) :
    ((OrderEmbedding.supIrredLowerSet α) a) = s := by
  unfold OrderEmbedding.supIrredLowerSet
  simp_all only [supIrred_iff_of_finite, RelEmbedding.coe_mk, Embedding.coeFn_mk]

-- Birkhoff's Embedding is actually surjective
lemma supIrredLowerSet_surjective : Function.Surjective (OrderEmbedding.supIrredLowerSet α) := by
  intro ⟨_, hs⟩
  obtain ⟨a, ha⟩ := supIrred_iff_of_finite.mp hs
  use a
  exact Subtype.ext <| OrderEmbedding.supIrredLowerSet_apply ha

/-- **Birkhoff's Representation Theorem**. Any nonempty finite distributive lattice is isomorphic
to its lattice of sup-irreducible lower sets. This is one version of Birkhoff's representation
theorem. -/
noncomputable def OrderIso.supIrredLowerSet : α ≃o {s : LowerSet α // SupIrred s} :=
    RelIso.ofSurjective  _ (supIrredLowerSet_surjective)

end PartialOrder
section DistribLattice
variable [DistribLattice α]

open Fintype

variable [Fintype α] [@DecidablePred α SupIrred]

open scoped Classical

/-- **Birkhoff's Representation Theorem**. Any nonempty finite distributive lattice is isomorphic to
the lattice of lower sets of its sup-irreducible elements. Second version of Birkhoff's
representation theorem -/
noncomputable def OrderIso.lowerSetSupIrred [OrderBot α] : α ≃o LowerSet {a : α // SupIrred a} :=
  Equiv.toOrderIso
    { toFun := fun a ↦ ⟨{b | ↑b ≤ a}, fun b c hcb hba ↦ hba.trans' hcb⟩
      invFun := fun s ↦ (s : Set {a : α // SupIrred a}).toFinset.sup (↑)
      left_inv := fun a ↦ by
        refine' le_antisymm (Finset.sup_le fun b ↦ Set.mem_toFinset.1) _
        obtain ⟨s, rfl, hs⟩ := exists_supIrred_decomposition a
        exact Finset.sup_le fun i hi ↦
          le_sup_of_le (b := ⟨i, hs hi⟩) (Set.mem_toFinset.2 <| le_sup (f := id) hi) le_rfl
      right_inv := fun s ↦ by
        ext a
        dsimp
        refine' ⟨fun ha ↦ _, fun ha ↦ _⟩
        · obtain ⟨i, hi, ha⟩ := a.2.supPrime.le_finset_sup.1 ha
          exact s.lower ha (Set.mem_toFinset.1 hi)
        · dsimp
          exact le_sup (Set.mem_toFinset.2 ha) }
    (fun b c hbc d ↦ le_trans' hbc) fun s t hst ↦ Finset.sup_mono <| Set.toFinset_mono hst

variable (α)

namespace OrderEmbedding
variable [Fintype α]

/-- **Birkhoff's Representation Theorem**. Any finite distributive lattice can be embedded in a
powerset lattice. -/
noncomputable def birkhoffSet : α ↪o Set {a : α // SupIrred a} := by
  by_cases h : IsEmpty α
  · exact OrderEmbedding.ofIsEmpty
  rw [not_isEmpty_iff] at h
  have := Fintype.toOrderBot α
  exact OrderIso.lowerSetSupIrred.toOrderEmbedding.trans ⟨⟨_, SetLike.coe_injective⟩, Iff.rfl⟩

/-- **Birkhoff's Representation Theorem**. Any finite distributive lattice can be embedded in a
powerset lattice. -/
noncomputable def birkhoffFinset : α ↪o Finset {a : α // SupIrred a} := by
  exact (birkhoffSet _).trans Fintype.finsetOrderIsoSet.symm.toOrderEmbedding


variable {α}

@[simp] lemma coe_birkhoffFinset (a : α) : birkhoffFinset α a = birkhoffSet α a := by
  classical
  -- TODO: This should be a single `simp` call but `simp` refuses to use
  -- `OrderIso.coe_toOrderEmbedding` and `Fintype.coe_finsetOrderIsoSet_symm`
  simp [birkhoffFinset]
  rw [OrderIso.coe_toOrderEmbedding, Fintype.coe_finsetOrderIsoSet_symm]
  simp

@[simp] lemma birkhoffSet_sup (a b : α) :
    birkhoffSet α (a ⊔ b) = birkhoffSet α a ∪ birkhoffSet α b := by
  unfold OrderEmbedding.birkhoffSet; split <;> simp [eq_iff_true_of_subsingleton]


@[simp] lemma birkhoffSet_inf (a b : α) :
    birkhoffSet α (a ⊓ b) = birkhoffSet α a ∩ birkhoffSet α b := by
  unfold OrderEmbedding.birkhoffSet; split <;> simp [eq_iff_true_of_subsingleton]

variable [DecidableEq α]

@[simp] lemma birkhoffFinset_sup (a b : α) :
    birkhoffFinset α (a ⊔ b) = birkhoffFinset α a ∪ birkhoffFinset α b := by
  dsimp [OrderEmbedding.birkhoffFinset]
  rw [birkhoffSet_sup, OrderIso.coe_toOrderEmbedding]
  simpa using OrderIso.map_sup _ _ _

@[simp] lemma birkhoffFinset_inf (a b : α) :
    birkhoffFinset α (a ⊓ b) = birkhoffFinset α a ∩ birkhoffFinset α b := by
  dsimp [OrderEmbedding.birkhoffFinset]
  rw [birkhoffSet_inf, OrderIso.coe_toOrderEmbedding]
  simpa using OrderIso.map_inf _ _ _

@[simp] lemma birkhoffSet_apply [OrderBot α] (a : α) :
    birkhoffSet α a = OrderIso.lowerSetSupIrred a := by
  simp [birkhoffSet]; convert rfl

end OrderEmbedding

namespace LatticeHom
variable [Fintype α]

/-- **Birkhoff's Representation Theorem**. Any finite distributive lattice can be embedded in a
powerset lattice. -/
noncomputable def birkhoffSet : LatticeHom α (Set {a : α // SupIrred a}) where
  toFun := OrderEmbedding.birkhoffSet α
  map_sup' := OrderEmbedding.birkhoffSet_sup
  map_inf' := OrderEmbedding.birkhoffSet_inf

/-- **Birkhoff's Representation Theorem**. Any finite distributive lattice can be embedded in a
powerset lattice. -/
noncomputable def birkhoffFinset : LatticeHom α (Finset {a : α // SupIrred a}) where
  toFun := OrderEmbedding.birkhoffFinset α
  map_sup' := OrderEmbedding.birkhoffFinset_sup
  map_inf' := OrderEmbedding.birkhoffFinset_inf

lemma birkhoffFinset_injective : Injective (birkhoffFinset α) :=
  (OrderEmbedding.birkhoffFinset α).injective

end LatticeHom

variable [DecidableEq α] [@DecidablePred α SupIrred]


lemma exists_birkhoff_representation.{u} (α : Type u) [Finite α] [DistribLattice α] :
    ∃ (β : Type u) (_ : DecidableEq β) (_ : Fintype β) (f : LatticeHom α (Finset β)),
      Injective f := by
  classical
  cases nonempty_fintype α
  exact ⟨{a : α // SupIrred a}, _, by infer_instance, LatticeHom.birkhoffFinset _,
    LatticeHom.birkhoffFinset_injective _⟩

end DistribLattice
