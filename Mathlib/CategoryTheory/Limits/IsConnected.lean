/-
Copyright (c) 2024 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/

import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Limits.Final

/-!
# Colimits of connected index categories

This file proves that a category $\mathsf{C}$ is connected if and only if
$\operatorname{colim}_{c \in \mathsf{C}} \{*\} \cong \{*\}$ in the category
$\mathsf{Set}$ (i.e. `Type v`).

See `connected_iff_colimit_const_pUnit_iso_pUnit` for the proof of this characterization and
`unitValuedFunctor` for the definition of the constant functor used in the statement.

## Tags

unit-valued, singleton, colimit
-/


universe v u

namespace CategoryTheory.Limits.Types

open CategoryTheory.Limits
open CategoryTheory.Limits.Types
open CategoryTheory.Functor.Final

variable (C : Type u) [Category.{v} C]

/-- The functor mapping every object to `PUnit`. -/
def unitValuedFunctor : C ⥤ TypeMax.{u, v} := (Functor.const C).obj PUnit.{(max u v) + 1}

instance instSubsingletonColimitPUnit [IsPreconnected C] :
    Subsingleton (colimit (unitValuedFunctor C)) where
  allEq a b := by
    obtain ⟨c, ⟨⟩, rfl⟩ := jointly_surjective' a
    obtain ⟨d, ⟨⟩, rfl⟩ := jointly_surjective' b
    apply constant_of_preserves_morphisms (colimit.ι (unitValuedFunctor C) · PUnit.unit)
    exact fun c d f => colimit_sound f rfl

/-- Given a connected index category, the colimit of the constant unit-valued functor is `PUnit`. -/
noncomputable def colimitConstPUnitIsoPUnit [IsConnected C] :
    colimit (unitValuedFunctor C) ≅ PUnit where
  hom := fun _ => PUnit.unit
  inv := fun _ => colimit.ι (unitValuedFunctor C) Classical.ofNonempty PUnit.unit

/-- If a colimit is nonempty, also its index category is nonempty. -/
theorem nonempty_of_nonempty_colimit {F : C ⥤ TypeMax.{u, v}} :
    Nonempty (colimit F) → Nonempty C :=
  Nonempty.map <| Sigma.fst ∘ Quot.out ∘ (colimitEquivQuot F).toFun

/-- Let `F` be a `Type`-valued functor. If two elements `a : F c` and `b : F d` represent the same
element of `colimit F`, then `c` and `d` are related by a `Zigzag`.
-/
theorem zigzag_of_eqvGen_quot_rel (F : C ⥤ TypeMax.{u, v}) (c d : Σ j, F.obj j)
    (h : EqvGen (Quot.Rel F) c d) : Zigzag c.1 d.1 := by
  induction h with
  | rel _ _ h => exact zigzag_of_hom <| Exists.choose h
  | refl _ => rfl
  | symm _ _ _ ih => exact zigzag_symmetric ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- An index category is connected iff the colimit of the constant singleton-valued functor is a
singleton.
-/
theorem connected_iff_colimit_const_pUnit_iso_pUnit :
    IsConnected C ↔ Nonempty (colimit (unitValuedFunctor C) ≅ PUnit) := by
  refine ⟨fun _ => ⟨colimitConstPUnitIsoPUnit C⟩, fun ⟨h⟩ => ?_⟩
  have : Nonempty C := nonempty_of_nonempty_colimit _ <| Nonempty.map h.inv inferInstance
  refine zigzag_isConnected <| fun c d => ?_
  refine zigzag_of_eqvGen_quot_rel _ (unitValuedFunctor C) ⟨c, PUnit.unit⟩ ⟨d, PUnit.unit⟩ ?_
  exact colimit_eq <| h.toEquiv.injective rfl

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

theorem iso_congr_left {α β γ : C} (f: α ≅ β) : (α ≅ γ) ≃ (β ≅ γ) :=
  ⟨ f.symm.trans, f.trans, by aesop_cat, by aesop_cat ⟩

theorem irgendwas (F : C ⥤ D) [CategoryTheory.Functor.Final F] : IsConnected C ↔ IsConnected D := by
  refine Iff.trans (connected_iff_colimit_const_pUnit_iso_pUnit C) ?_
  refine Iff.trans ?_ (connected_iff_colimit_const_pUnit_iso_pUnit D).symm
  exact Equiv.nonempty_congr <| iso_congr_left
    <| CategoryTheory.Functor.Final.colimitIso F (unitValuedFunctor D)

end CategoryTheory.Limits.Types
