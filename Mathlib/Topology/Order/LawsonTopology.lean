/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Topology.Order.LowerUpperTopology
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.ZMod.Defs

/-!
# Lawson topology

This file introduces the Lawson topology on a preorder.

## Main definitions

- `LawsonTopology'` - the Lawson topology is defined as the meet of the `LowerTopology` and the
  `ScottTopology`.

## Main statements

## Implementation notes

A type synonym `WithLawsonTopology` is introduced and for a preorder `α`, `WithLawsonTopology α`
is made an instance of `topological_space` by the `LawsonTopology'`.

We define a mixin class `LawsonTopology` for the class of types which are both a preorder and a
topology and where the topology is the `LawsonTopology'`.
It is shown that `WithLawsonTopology α` is an instance of `LawsonTopology`.

## References

* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]

## Tags
Lawson topology, preorder
-/

open Set

open TopologicalSpace

section inf

variable {X Y Z} [tY : TopologicalSpace Y] [tZ : TopologicalSpace Z] (fY : X → Y) (fZ : X → Z)

theorem induced_to_prod (f : X → Y × Z) :
    induced f inferInstance = induced (fun x ↦ (f x).1) tY ⊓ induced (fun x ↦ (f x).2) tZ := by
  erw [induced_inf]
  simp_rw [induced_compose]
  rfl

theorem inducing_inf_to_prod :
    @Inducing X (Y × Z) (induced fY tY ⊓ induced fZ tZ) _ fun x ↦ (fY x, fZ x) :=
  letI := induced fY tY ⊓ induced fZ tZ; ⟨(induced_to_prod fun x ↦ (fY x, fZ x)).symm⟩

theorem TopologicalSpace.IsTopologicalBasis.inf
    {BY : Set (Set Y)} {BZ : Set (Set Z)} (bY : IsTopologicalBasis BY) (bZ : IsTopologicalBasis BZ) :
    @IsTopologicalBasis X (induced fY tY ⊓ induced fZ tZ) (BY.image2 (fY ⁻¹' · ∩ fZ ⁻¹' ·) BZ) := by
  letI := induced fY tY ⊓ induced fZ tZ
  convert (bY.prod bZ).inducing (inducing_inf_to_prod fY fZ)
  rw [Set.image_image2]; rfl

example {t₁ t₂ B₁ B₂} (h₁ : @IsTopologicalBasis X t₁ B₁) (h₂ : @IsTopologicalBasis X t₂ B₂) :
    @IsTopologicalBasis X (t₁ ⊓ t₂) (Set.image2 (· ∩ ·) B₁ B₂) := by
  convert @IsTopologicalBasis.inf X X X t₁ t₂ id id B₁ B₂ h₁ h₂ <;> rw [@induced_id _ (_)]
-- need to specify all implicit arguments because multiple instances on the same type
-- would be easier if `TopologicalSpace` arguments in `TopologicalSpace.IsTopologicalBasis.inf`
-- are regular implicit rather than instance implicit

end inf





variable {α β : Type*}

variable [TopologicalSpace α]

--instance : TopologicalSpace (α×α) := by exact instTopologicalSpaceProd


namespace Topology

/-! ### Lawson topology -/

section Lawson
section Preorder

variable [Preorder α]

/--
The Lawson topology is defined as the meet of the `LowerTopology` and the `ScottTopology`.
-/
def lawson : TopologicalSpace α := lower α ⊓ scott

variable (α) [TopologicalSpace α]

/-- Predicate for an ordered topological space to be equipped with its Lawson topology.

The Lawson topology is defined as the meet of the `LowerTopology` and the `ScottTopology`.
-/
class IsLawson : Prop where
  topology_eq_lawson : ‹TopologicalSpace α› = lawson

end Preorder

namespace IsLawson
section Preorder
variable (α) [Preorder α] [TopologicalSpace α] [IsLawson α]



lemma topology_eq : ‹_› = lawson := topology_eq_lawson

/-- The complements of the upper closures of finite sets intersected with Scott open sets form
a basis for the lawson topology. -/
def lawsonBasis (α : Type*) [Preorder α] :=
  { s : Set α | ∃ u : Set α, IsOpen[scott] u ∧ ∃ t : Set α, t.Finite ∧
    u ∩ (upperClosure t : Set α)ᶜ = s }

open TopologicalSpace

#check IsLower.lowerBasis
#check IsScott.scottBasis

#check IsLower.isTopologicalBasis
#check IsScott.isTopologicalBasis α

#check image2

#check WithScott.toScott

#check TopologicalSpace.isTopologicalBasis_opens (α := WithScott α)

def lawson_basis := (image2 (fun x x_1 ↦ ⇑WithLower.toLower ⁻¹' x ∩ ⇑WithScott.toScott ⁻¹' x_1) (IsLower.lowerBasis (WithLower α)) {U | @IsOpen (WithScott α) _ U})

#check lawson_basis

#check IsTopologicalBasis.inf WithLower.toLower WithScott.toScott IsLower.isTopologicalBasis (TopologicalSpace.isTopologicalBasis_opens (α := WithScott α))

#check IsTopologicalBasis.inf id id (IsScott.isTopologicalBasis α) IsLower.isTopologicalBasis


protected theorem isTopologicalBasis : TopologicalSpace.IsTopologicalBasis (lawson_basis α) := by
  rw [lawson_basis]
  --apply IsTopologicalBasis.inf

  convert IsTopologicalBasis.inf WithLower.toLower WithScott.toScott IsLower.isTopologicalBasis (TopologicalSpace.isTopologicalBasis_opens (α := WithScott α))
  erw [topology_eq α]
  rw [lawson]
  --rw [TopologicalSpace.induced]
  apply (congrArg₂ Inf.inf _) _
  rw [WithLower.toLower, Equiv.refl]
  simp_rw [isOpen_induced_iff]
  ext


  --apply congrFun (congrArg Inf.inf _) _
  --rw [induced]
  --rw [induced]
  --ext


  --refine TopologicalSpace.ext ?h.e'_2.a



  --rw [topology_eq_lawson]
  --rw [lawsonBasis]
  --sorry

variable (s : Set α) (h: IsUpperSet s) (hs: IsOpen[Topology.scottHausdorff] s)



#check IsScottHausdorff.isOpen_of_isLowerSet (IsLower.isLowerSet_of_isOpen _)






-- Have the lower open sets are SH by
-- IsScottHausdorff.isOpen_of_isLowerSet (IsLower.isLowerSet_of_isOpen _)
-- Have the Scott open sets are SH by scottHausdorff_le_scott I think)
-- Together these are a subbasis
lemma isOpen_implies_scottHausdorff_open {s : Set α} : IsOpen s → IsOpen[scottHausdorff] s := by
  erw [topology_eq α];
  intro hs
  sorry

--#check ⟨h, hs⟩

--#check IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open.mpr ⟨h, hs⟩

#check scott

--variable [IsScott α]

-- Get the statement deliberately wrong for now
lemma LawsonOpen_iff_ScottOpen (s : Set α) (h : IsUpperSet s) :
  IsOpen s ↔ IsOpen[Topology.scottHausdorff] s := by
  constructor
  · intro hs
    rw [IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open.mpr ⟨h, hs⟩]
    --convert IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open.mpr _
    --rw [IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open]
    rw [@IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open _ _ _ _ s]
    constructor
    · exact h
    · exact fun d d₁ d₂ d₃ => (@LawsonOpen_implies_ScottHausdorffOpen' _ _ l S _ _ _ _ s)
        hs d d₁ d₂ d₃
  · apply TopologicalSpace.le_def.mp (Scott_le_Lawson _ _)

end Preorder
end IsLawson

/--
Type synonym for a preorder equipped with the Lawson topology
-/
def WithLawson (α : Type*) := α

namespace WithLawson

/-- `toLawson` is the identity function to the `WithLawson` of a type.  -/
@[match_pattern] def toLawson : α ≃ WithLawson α := Equiv.refl _

/-- `ofLawson` is the identity function from the `WithLawson` of a type.  -/
@[match_pattern] def ofLawson : WithLawson α ≃ α := Equiv.refl _

@[simp] lemma to_Lawson_symm_eq : (@toLawson α).symm = ofLawson := rfl
@[simp] lemma of_Lawson_symm_eq : (@ofLawson α).symm = toLawson := rfl
@[simp] lemma toLawson_ofLawson (a : WithLawson α) : toLawson (ofLawson a) = a := rfl
@[simp] lemma ofLawson_toLawson (a : α) : ofLawson (toLawson a) = a := rfl

@[simp, nolint simpNF]
lemma toLawson_inj {a b : α} : toLawson a = toLawson b ↔ a = b := Iff.rfl

@[simp, nolint simpNF]
lemma ofLawson_inj {a b : WithLawson α} : ofLawson a = ofLawson b ↔ a = b :=
Iff.rfl

/-- A recursor for `WithLawson`. Use as `induction x using WithLawson.rec`. -/
protected def rec {β : WithLawson α → Sort _}
    (h : ∀ a, β (toLawson a)) : ∀ a, β a := fun a => h (ofLawson a)

instance [Nonempty α] : Nonempty (WithLawson α) := ‹Nonempty α›
instance [Inhabited α] : Inhabited (WithLawson α) := ‹Inhabited α›

variable [Preorder α]

instance : Preorder (WithLawson α) := ‹Preorder α›
instance : TopologicalSpace (WithLawson α) := lawson
instance : IsLawson (WithLawson α) := ⟨rfl⟩

/-- If `α` is equipped with the Lawson topology, then it is homeomorphic to `WithLawson α`.
-/
def withLawsonTopologyHomeomorph [TopologicalSpace α] [IsLawson α]  : WithLawson α ≃ₜ α :=
  WithLawson.ofLawson.toHomeomorphOfInducing ⟨by erw [IsLawson.topology_eq α, induced_id]; rfl⟩

/-
theorem isOpen_preimage_ofLawson (S : Set α) :
    IsOpen (WithLawsonTopology.ofLawson ⁻¹' S) ↔
      LawsonTopology'.IsOpen S :=
  Iff.rfl

theorem isOpen_def (T : Set (WithLawsonTopology α)) :
    IsOpen T ↔
      LawsonTopology'.IsOpen (WithLawsonTopology.toLawson ⁻¹' T) :=
  Iff.rfl
-/

end WithLawson
end Lawson

/-

namespace LawsonTopology

section preorder

variable [Preorder α]

variable [TopologicalSpace α] [LawsonTopology α]

variable (α)

lemma topology_eq : ‹_› = LawsonTopology' := topology_eq_LawsonTopology

variable {α}




lemma isOpen_iff_Lower_and_Scott_Open (u : Set α) : LawsonTopology'.IsOpen u
↔ (LowerTopology'.IsOpen u ∧ ScottTopology'.IsOpen u) := by




end preorder

end LawsonTopology

section ts

variable [Preorder α]

lemma Lawson_le_Scott' : @LawsonTopology' α ≤ @ScottTopology' α := inf_le_right

lemma Lawson_le_Lower' : @LawsonTopology' α ≤ @LowerTopology' α := inf_le_left

lemma Scott_Hausdorff_le_Lawson' : @ScottHausdorffTopology α _ ≤ @LawsonTopology' α _ := by
  rw [LawsonTopology', le_inf_iff]
  constructor
  · exact @Scott_Hausdorff_le_Lower' α _
  · exact @Scott_Hausdorff_le_Scott' α _



lemma LawsonOpen_implies_ScottHausdorffOpen''' (s : Set α) :
  IsOpen (WithLawsonTopology.ofLawson ⁻¹' s) → ScottHausdorffTopology.IsOpen s :=
  Scott_Hausdorff_le_Lawson' _

lemma ScottOpen_implies_LawsonOpen (s : Set α) :
  IsOpen (WithScottTopology.ofScott ⁻¹' s) → IsOpen (WithLawsonTopology.ofLawson ⁻¹' s) :=
  Lawson_le_Scott' _ s



lemma LowerOpen_implies_LawsonOpen (s : Set α) :
  IsOpen (WithLowerTopology.ofLower ⁻¹' s) → IsOpen (WithLawsonTopology.ofLawson ⁻¹' s) :=
  Lawson_le_Lower' _ s

end ts

section csh

variable [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
  [ScottTopology α] [LawsonTopology β] (e : OrderIso α β) (s : Set α)


lemma Lawson_le_Scott'' [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
    [ScottTopology α] [LawsonTopology β] (e : OrderIso α β) :
    Equiv.toHomeomorphOfInducing e  ≤ α := inf_le_right

#check image e s

#check e '' s

lemma ScottOpen_implies_LawsonOpen' [Preorder α] [Preorder β] [TopologicalSpace α]
    [TopologicalSpace β][ScottTopology α] [LawsonTopology β] (e : OrderIso α β) (s : Set α) :
    IsOpen s → IsOpen (e '' s) := by
  apply   Lawson_le_Scott'

example [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
  [ScottTopology α] [LawsonTopology β] (e : OrderIso α β) : Continuous e := by
  rw [continuous_def]
  intro s hs
  apply ScottOpen_implies_LawsonOpen'
  --apply ScottOpen_implies_LawsonOpen
  --apply Lawson_le_Scott'


lemma ScottLawsonCont' [Preorder α] :
  Continuous (WithScott.toScott ∘ WithLawson.ofLawson : WithLawson α → _) := by
  rw [continuous_def]
  intro s hs
  apply ScottOpen_implies_LawsonOpen _ hs

lemma LawsonOpen_iff_ScottOpen' [Preorder α] (s : Set α) (h : IsUpperSet s) :
  IsOpen (WithScottTopology.ofScott ⁻¹' s) ↔ IsOpen (WithLawsonTopology.ofLawson ⁻¹' s) := by
  constructor
  · apply ScottOpen_implies_LawsonOpen
  · intro hs
    rw [ScottTopology.isOpen_iff_upper_and_Scott_Hausdorff_Open']
    constructor
    · exact h
    · apply LawsonOpen_implies_ScottHausdorffOpen''' _ hs

variable  (L : TopologicalSpace α) (l : TopologicalSpace α) (S : TopologicalSpace α)

variable [Preorder α]  [@LawsonTopology α L _] [@LowerTopology α l _] [@ScottTopology α S _]

lemma Scott_le_Lawson : L ≤ S := by
  rw [@ScottTopology.topology_eq α _ S _, @LawsonTopology.topology_eq α _ L _,  LawsonTopology']
  apply inf_le_right

lemma Scott_Hausdorff_le_Lawson : (@ScottHausdorffTopology α _) ≤ L := by
  rw [@LawsonTopology.topology_eq α _ L _,  LawsonTopology', le_inf_iff,
    ← @LowerTopology.topology_eq α _ l _, ← @ScottTopology.topology_eq α _ S _]
  constructor
  · exact @Scott_Hausdorff_le_Lower  α _ l _
  · exact Scott_Hausdorff_le_Scott

open Topology

lemma LawsonOpen_implies_ScottHausdorffOpen : IsOpen[L] ≤ IsOpen[ScottHausdorffTopology] := by
  rw [←TopologicalSpace.le_def]
  apply (@Scott_Hausdorff_le_Lawson _ L l _ _ _)


lemma LawsonOpen_implies_ScottHausdorffOpen' (s : Set α) :
IsOpen[L] s → IsOpen[ScottHausdorffTopology] s := by
  apply (@LawsonOpen_implies_ScottHausdorffOpen _ _ l)

end csh

-- Can we say something without CL?
section CompleteLattice

variable [CompleteLattice α]
  (S :TopologicalSpace α) (l : TopologicalSpace α) (L : TopologicalSpace α)
  [@ScottTopology α S _]  [@LawsonTopology α L _] [@LowerTopology α l _]

-- Scott open iff UpperSet and STopology open

open Topology

variable [Preorder α] [TopologicalSpace α] (s : Set α)

#check @Topology.IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open _ _ Topology.scott _  s

lemma LawsonOpen_iff_ScottOpen (s : Set α) (h : IsUpperSet s) :
  IsOpen[Topology.lawson] s ↔ IsOpen[Topology.scott] s := by
  constructor
  · intro hs
    rw [@Topology.IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open _ _ Topology.scott _ s]
    constructor
    · exact h
    · exact fun d d₁ d₂ d₃ => (@LawsonOpen_implies_ScottHausdorffOpen' _ _ l S _ _ _ _ s)
        hs d d₁ d₂ d₃
  · apply TopologicalSpace.le_def.mp (Scott_le_Lawson _ _)

end CompleteLattice
-/
