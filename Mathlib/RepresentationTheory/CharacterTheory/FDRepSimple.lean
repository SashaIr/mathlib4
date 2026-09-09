/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RepresentationTheory.FinGroupCharZero
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Simple objects of `FDRep` and decomposition of characters

Mathlib knows Schur's lemma and the orthogonality of the characters of simple objects of
`FDRep k G`, but it has no bridge between the categorical notion `CategoryTheory.Simple`
and the concrete notion `Representation.IsIrreducible`.  This is a prerequisite for the
identification of the Schur class functions with the irreducible characters of the
symmetric group; it is proved here.

## Main definitions

* `FDRep.fdrepHomEquivIntertwiningMap` : the morphisms `FDRep.of ρ ⟶ FDRep.of σ` are the
  intertwining maps from `ρ` to `σ`.

## Main results

* `FDRep.simple_of_isIrreducible` : an irreducible representation gives a simple object
  of `FDRep k G`.
* `FDRep.exists_subrepresentation_of_not_simple` : conversely, a nonzero object of
  `FDRep k G` which is not simple has a subrepresentation other than `⊥` and `⊤`.
-/

@[expose] public section

namespace FDRep

open CategoryTheory Representation LinearMap Module

universe u

variable {k G V W : Type u} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [Module.Finite k V] [Module.Finite k W]

/-! ### Morphisms of `FDRep` and intertwining maps -/

/-- The morphisms `FDRep.of ρ ⟶ FDRep.of σ` are exactly the intertwining maps from `ρ` to
`σ`. -/
noncomputable def fdrepHomEquivIntertwiningMap (ρ : Representation k G V)
    (σ : Representation k G W) : (FDRep.of ρ ⟶ FDRep.of σ) ≃ₗ[k] IntertwiningMap ρ σ where
  toFun f := ⟨f.hom.hom.hom, fun g => by
    ext1
    exact ConcreteCategory.congr_hom ((forget (FGModuleCat k)).congr_map (f.comm g)) _⟩
  invFun f := ⟨FGModuleCat.ofHom f.toLinearMap, by
    intro g
    ext v
    change f (ρ g v) = σ g (f v)
    exact IntertwiningMap.isIntertwining ρ σ f g v⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [IsAlgClosed k] [Finite G] [NeZero (Nat.card G : k)]

/-- An irreducible representation is a simple object of `FDRep k G`. -/
theorem simple_of_isIrreducible (ρ : Representation k G V) [ρ.IsIrreducible] :
    Simple (FDRep.of ρ) := by
  rw [FDRep.simple_iff_end_is_rank_one, (fdrepHomEquivIntertwiningMap ρ ρ).finrank_eq]
  have hb : Function.Bijective (algebraMap k (IntertwiningMap ρ ρ)) :=
    Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
  have h := (LinearEquiv.ofBijective (Algebra.linearMap k (IntertwiningMap ρ ρ)) hb).finrank_eq
  simp [h.symm]

/-- A nonzero object of `FDRep k G` which is not simple has a subrepresentation which is
neither `⊥` nor `⊤`. -/
theorem exists_subrepresentation_of_not_simple (X : FDRep k G) (hX : 0 < finrank k X)
    (hns : ¬ Simple X) :
    ∃ U : Subrepresentation X.ρ, U ≠ ⊥ ∧ U ≠ ⊤ := by
  by_contra hcon
  push Not at hcon
  have hnt : Nontrivial (Subrepresentation X.ρ) := by
    refine ⟨⊥, ⊤, fun h => ?_⟩
    obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := k)).1 hX
    have hmem : v ∈ (⊥ : Subrepresentation X.ρ) := h ▸ (trivial : v ∈ (⊤ : Subrepresentation X.ρ))
    exact hv hmem
  have : Representation.IsIrreducible X.ρ := ⟨fun U => by
    rcases eq_or_ne U ⊥ with h | h
    · exact Or.inl h
    · exact Or.inr (hcon U h)⟩
  exact hns (simple_of_isIrreducible X.ρ)

end FDRep
