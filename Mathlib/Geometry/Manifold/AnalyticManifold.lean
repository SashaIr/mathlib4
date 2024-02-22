/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

/-!
# Analytic manifolds (possibly with boundary or corners)

An analytic manifold is a manifold modelled on a normed vector space, or a subset like a
half-space (to get manifolds with boundaries) for which changes of coordinates are analytic in the
interior and smooth everywhere (including at the boundary).  The definition mirrors
`SmoothManifoldWithCorners`, but using an `analyticGroupoid` in place of `contDiffGroupoid`.  All
analytic manifolds are smooth manifolds.
-/

noncomputable section

open Set Filter Function

open scoped Manifold Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M]

/-!
## `analyticGroupoid`

`f ∈ PartialHomeomorph H H` is in `analyticGroupoid I` if `f` and `f.symm` are smooth everywhere,
analytic on the interior, and map the interior to itself.  This allows us to define
`AnalyticManifold` including in cases with boundary.
-/

section analyticGroupoid

/-- Given a model with corners `(E, H)`, we define the groupoid of analytic transformations of `H`
as the maps that are analytic and map interior to interior when read in `E` through `I`. We also
explicitly define that they are `C^∞` on the whole domain, since we are only requiring
analyticity on the interior of the domain. -/
def analyticGroupoid : StructureGroupoid H :=
  (contDiffGroupoid ∞ I) ⊓ Pregroupoid.groupoid
    { property := fun f s => AnalyticOn 𝕜 (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ interior (range I)) ∧
        (I.symm ⁻¹' s ∩ interior (range I)).image (I ∘ f ∘ I.symm) ⊆ interior (range I)
      comp := fun {f g u v} hf hg _ _ _ => by
        simp only [] at hf hg ⊢
        have comp : I ∘ (g ∘ f) ∘ I.symm = (I ∘ g ∘ I.symm) ∘ I ∘ f ∘ I.symm := by ext x; simp
        apply And.intro
        · simp only [comp, preimage_inter]
          refine hg.left.comp (hf.left.mono ?_) ?_
          · simp only [subset_inter_iff, inter_subset_right]
            rw [inter_assoc]
            simp
          · intro x hx
            apply And.intro
            · rw [mem_preimage, comp_apply, I.left_inv]
              exact hx.left.right
            · apply hf.right
              rw [mem_image]
              exact ⟨x, ⟨⟨hx.left.left, hx.right⟩, rfl⟩⟩
        · simp only [comp]
          rw [image_comp]
          intro x hx
          rw [mem_image] at hx
          rcases hx with ⟨x', hx'⟩
          refine hg.right ⟨x', And.intro ?_ hx'.right⟩
          apply And.intro
          · have hx'1 : x' ∈ ((v.preimage f).preimage (I.symm)).image (I ∘ f ∘ I.symm) := by
              refine image_subset (I ∘ f ∘ I.symm) ?_ hx'.left
              rw [preimage_inter]
              refine Subset.trans ?_ (inter_subset_right (u.preimage I.symm)
                ((v.preimage f).preimage I.symm))
              apply inter_subset_left
            rcases hx'1 with ⟨x'', hx''⟩
            rw [hx''.right.symm]
            simp only [comp_apply, mem_preimage, I.left_inv]
            exact hx''.left
          · rw [mem_image] at hx'
            rcases hx'.left with ⟨x'', hx''⟩
            exact hf.right ⟨x'', ⟨⟨hx''.left.left.left, hx''.left.right⟩, hx''.right⟩⟩
      id_mem := by
        apply And.intro
        · simp only [preimage_univ, univ_inter]
          exact AnalyticOn.congr isOpen_interior
            (f := (1 : E →L[𝕜] E)) (fun x _ => (1 : E →L[𝕜] E).analyticAt x)
            (fun z hz => (I.right_inv (interior_subset hz)).symm)
        · intro x hx
          simp only [id_comp, comp_apply, preimage_univ, univ_inter, mem_image] at hx
          rcases hx with ⟨y, hy⟩
          rw [← hy.right, I.right_inv (interior_subset hy.left)]
          exact hy.left
      locality := fun {f u} _ h => by
        simp only [] at h
        simp only [AnalyticOn]
        apply And.intro
        · intro x hx
          rcases h (I.symm x) (mem_preimage.mp hx.left) with ⟨v, hv⟩
          exact hv.right.right.left x ⟨mem_preimage.mpr ⟨hx.left, hv.right.left⟩, hx.right⟩
        · apply mapsTo'.mp
          simp only [MapsTo]
          intro x hx
          rcases h (I.symm x) hx.left with ⟨v, hv⟩
          apply hv.right.right.right
          rw [mem_image]
          have hx' := And.intro hx (mem_preimage.mpr hv.right.left)
          rw [← mem_inter_iff, inter_comm, ← inter_assoc, ← preimage_inter, inter_comm v u] at hx'
          exact ⟨x, ⟨hx', rfl⟩⟩
      congr := fun {f g u} hu fg hf => by
        simp only [] at hf ⊢
        apply And.intro
        · refine AnalyticOn.congr (IsOpen.inter (hu.preimage I.continuous_symm) isOpen_interior)
            hf.left ?_
          intro z hz
          simp only [comp_apply]
          rw [fg (I.symm z) hz.left]
        · intro x hx
          apply hf.right
          rw [mem_image] at hx ⊢
          rcases hx with ⟨y, hy⟩
          refine ⟨y, ⟨hy.left, ?_⟩⟩
          rw [comp_apply, comp_apply, fg (I.symm y) hy.left.left] at hy
          exact hy.right }

/-- An identity partial homeomorphism belongs to the analytic groupoid. -/
theorem ofSet_mem_analyticGroupoid {s : Set H} (hs : IsOpen s) :
    PartialHomeomorph.ofSet s hs ∈ analyticGroupoid I := by
  rw [analyticGroupoid]
  refine And.intro (ofSet_mem_contDiffGroupoid ∞ I hs) ?_
  apply mem_groupoid_of_pregroupoid.mpr
  suffices h : AnalyticOn 𝕜 (I ∘ I.symm) (I.symm ⁻¹' s ∩ interior (range I)) ∧
      (I.symm ⁻¹' s ∩ interior (range I)).image (I ∘ I.symm) ⊆ interior (range I) by
    simp only [PartialHomeomorph.ofSet_apply, id_comp, PartialHomeomorph.ofSet_toPartialEquiv,
      PartialEquiv.ofSet_source, h, comp_apply, mem_range, image_subset_iff, true_and,
      PartialHomeomorph.ofSet_symm, PartialEquiv.ofSet_target, and_self]
    intro x hx
    refine mem_preimage.mpr ?_
    rw [← I.right_inv (interior_subset hx.right)] at hx
    exact hx.right
  apply And.intro
  · have : AnalyticOn 𝕜 (1 : E →L[𝕜] E) (univ : Set E) := (fun x _ => (1 : E →L[𝕜] E).analyticAt x)
    exact (this.mono (subset_univ (s.preimage (I.symm) ∩ interior (range I)))).congr
      ((hs.preimage I.continuous_symm).inter isOpen_interior)
      fun z hz => (I.right_inv (interior_subset hz.right)).symm
  · intro x hx
    simp only [comp_apply, mem_image] at hx
    rcases hx with ⟨y, hy⟩
    rw [← hy.right, I.right_inv (interior_subset hy.left.right)]
    exact hy.left.right

/-- The composition of a partial homeomorphism from `H` to `M` and its inverse belongs to
the analytic groupoid. -/
theorem symm_trans_mem_analyticGroupoid (e : PartialHomeomorph M H) :
    e.symm.trans e ∈ analyticGroupoid I :=
  haveI : e.symm.trans e ≈ PartialHomeomorph.ofSet e.target e.open_target :=
    PartialHomeomorph.symm_trans_self _
  StructureGroupoid.mem_of_eqOnSource _ (ofSet_mem_analyticGroupoid I e.open_target) this

/-- The analytic groupoid is closed under restriction. -/
instance : ClosedUnderRestriction (analyticGroupoid I) :=
  (closedUnderRestriction_iff_id_le _).mpr
    (by
      apply StructureGroupoid.le_iff.mpr
      rintro e ⟨s, hs, hes⟩
      apply (analyticGroupoid I).mem_of_eqOnSource' _ _ _ hes
      exact ofSet_mem_analyticGroupoid I hs)

/-- `f ∈ analyticGroupoid` iff it is in the `contDiffGroupoid`, and it and its inverse are analytic
in the interior, and map interior to interior. -/
lemma mem_analyticGroupoid {E A : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace A] [CompleteSpace E] {I : ModelWithCorners 𝕜 E A}
    {f : PartialHomeomorph A A} :
    f ∈ analyticGroupoid I ↔ f ∈ contDiffGroupoid ∞ I ∧
      (AnalyticOn 𝕜 (I ∘ f ∘ I.symm) (I.symm ⁻¹' f.source ∩ interior (range I)) ∧
        (I.symm ⁻¹' f.source ∩ interior (range I)).image (I ∘ f ∘ I.symm) ⊆ interior (range I)) ∧
      (AnalyticOn 𝕜 (I ∘ f.symm ∘ I.symm) (I.symm ⁻¹' f.target ∩ interior (range I)) ∧
        (I.symm ⁻¹' f.target ∩ interior (range I)).image (I ∘ f.symm ∘ I.symm) ⊆ interior (range I))
    := by
  rfl

/-- The analytic groupoid on a boundaryless charted space modeled on a complete vector space
consists of the partial homeomorphisms which are analytic and have analytic inverse. -/
theorem mem_analyticGroupoid_of_boundaryless [CompleteSpace E] [I.Boundaryless]
    (e : PartialHomeomorph H H) :
    e ∈ analyticGroupoid I ↔ AnalyticOn 𝕜 (I ∘ e ∘ I.symm) (I '' e.source) ∧
    AnalyticOn 𝕜 (I ∘ e.symm ∘ I.symm) (I '' e.target) := by
  apply Iff.intro
  · intro he
    have := mem_groupoid_of_pregroupoid.mp he.right
    simp only [I.image_eq, I.range_eq_univ, interior_univ, subset_univ, and_true] at this ⊢
    exact this
  · intro he
    apply And.intro
    all_goals apply mem_groupoid_of_pregroupoid.mpr; simp only [I.image_eq, I.range_eq_univ,
      interior_univ, subset_univ, and_true, contDiffPregroupoid] at he ⊢
    · exact ⟨he.left.contDiffOn, he.right.contDiffOn⟩
    · exact he

/-- `analyticGroupoid` is closed under products -/
theorem analyticGroupoid_prod {E A : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace A] [CompleteSpace E] {F B : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace B] [CompleteSpace F] {I : ModelWithCorners 𝕜 E A} {J : ModelWithCorners 𝕜 F B}
    {f : PartialHomeomorph A A} {g : PartialHomeomorph B B}
    (fa : f ∈ analyticGroupoid I) (ga : g ∈ analyticGroupoid J) :
    f.prod g ∈ analyticGroupoid (I.prod J) := by
  have er : (range fun x : A × B ↦ (I x.1, J x.2)) = range I ×ˢ range J := range_prod_map
  have ei : interior (range fun x : A × B ↦ (I x.1, J x.2)) =
      interior (range I) ×ˢ interior (range J) := by rw [er, interior_prod_eq]
  -- This proof is a lot messier because `simp`s tend to fail.  E.g., we can't simplify via
  -- the above `ei` lemma, because the `TopologicalSpace` instances aren't defeq.  Instead, we use
  -- it via `subset_of_eq`.
  simp only [mem_analyticGroupoid, Function.comp, image_subset_iff] at fa ga ⊢
  refine ⟨contDiffGroupoid_prod fa.1 ga.1, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply AnalyticOn.prod
    · simp only [ModelWithCorners.symm, modelWithCorners_prod_toPartialEquiv,
        PartialEquiv.prod_symm, PartialEquiv.prod_coe, ModelWithCorners.toPartialEquiv_coe_symm,
        PartialHomeomorph.prod_apply, PartialHomeomorph.prod_toPartialEquiv,
        PartialEquiv.prod_source]
      refine fa.2.1.1.comp (analyticOn_fst _) ?_
      intro x m
      simp only [ModelWithCorners.prod, ModelWithCorners.source_eq, mem_univ, and_self, setOf_true,
        PartialEquiv.prod_target, ModelWithCorners.target_eq, ModelWithCorners.mk_coe,
        mem_inter_iff, mem_preimage, mem_prod] at m ⊢
      exact ⟨m.1.1, (subset_of_eq ei m.2).1⟩
    · simp only [ModelWithCorners.symm, modelWithCorners_prod_toPartialEquiv,
        PartialEquiv.prod_symm, PartialEquiv.prod_coe, ModelWithCorners.toPartialEquiv_coe_symm,
        PartialHomeomorph.prod_apply, PartialHomeomorph.prod_toPartialEquiv,
        PartialEquiv.prod_source]
      refine ga.2.1.1.comp (analyticOn_snd _) ?_
      intro x m
      simp only [ModelWithCorners.prod, ModelWithCorners.source_eq, mem_univ, and_self, setOf_true,
        PartialEquiv.prod_target, ModelWithCorners.target_eq, ModelWithCorners.mk_coe,
        mem_inter_iff, mem_preimage, mem_prod] at m ⊢
      exact ⟨m.1.2, (subset_of_eq ei m.2).2⟩
  · simp only [ModelWithCorners.prod, ModelWithCorners.source_eq, mem_univ, and_self, setOf_true,
      PartialEquiv.prod_target, ModelWithCorners.target_eq, ModelWithCorners.mk_symm,
      PartialEquiv.coe_symm_mk, PartialHomeomorph.prod_apply, ModelWithCorners.mk_coe,
      PartialHomeomorph.prod_toPartialEquiv, PartialEquiv.prod_source, mk_preimage_prod,
      image_subset_iff]
    intro x ⟨⟨m0,m1⟩,m2⟩
    replace m2 := subset_of_eq ei m2
    exact subset_of_eq ei.symm ⟨fa.2.1.2 ⟨m0,m2.1⟩, ga.2.1.2 ⟨m1,m2.2⟩⟩
  · apply AnalyticOn.prod
    · simp only [ModelWithCorners.symm, modelWithCorners_prod_toPartialEquiv,
        PartialEquiv.prod_symm, PartialEquiv.prod_coe, ModelWithCorners.toPartialEquiv_coe_symm,
        PartialHomeomorph.prod_apply, PartialHomeomorph.prod_toPartialEquiv,
        PartialEquiv.prod_source]
      refine fa.2.2.1.comp (analyticOn_fst _) ?_
      intro x m
      simp only [ModelWithCorners.prod, ModelWithCorners.source_eq, mem_univ, and_self, setOf_true,
        PartialEquiv.prod_target, ModelWithCorners.target_eq, ModelWithCorners.mk_coe,
        mem_inter_iff, mem_preimage, mem_prod] at m ⊢
      exact ⟨m.1.1, (subset_of_eq ei m.2).1⟩
    · simp only [ModelWithCorners.symm, modelWithCorners_prod_toPartialEquiv,
        PartialEquiv.prod_symm, PartialEquiv.prod_coe, ModelWithCorners.toPartialEquiv_coe_symm,
        PartialHomeomorph.prod_apply, PartialHomeomorph.prod_toPartialEquiv,
        PartialEquiv.prod_source]
      refine ga.2.2.1.comp (analyticOn_snd _) ?_
      intro x m
      simp only [ModelWithCorners.prod, ModelWithCorners.source_eq, mem_univ, and_self, setOf_true,
        PartialEquiv.prod_target, ModelWithCorners.target_eq, ModelWithCorners.mk_coe,
        mem_inter_iff, mem_preimage, mem_prod] at m ⊢
      exact ⟨m.1.2, (subset_of_eq ei m.2).2⟩
  · simp only [ModelWithCorners.prod, ModelWithCorners.source_eq, mem_univ, and_self, setOf_true,
      PartialEquiv.prod_target, ModelWithCorners.target_eq, ModelWithCorners.mk_symm,
      PartialEquiv.coe_symm_mk, PartialHomeomorph.prod_apply, ModelWithCorners.mk_coe,
      PartialHomeomorph.prod_toPartialEquiv, PartialEquiv.prod_source, mk_preimage_prod,
      image_subset_iff]
    intro x ⟨⟨m0,m1⟩,m2⟩
    replace m2 := subset_of_eq ei m2
    exact subset_of_eq ei.symm ⟨fa.2.2.2 ⟨m0,m2.1⟩, ga.2.2.2 ⟨m1,m2.2⟩⟩

end analyticGroupoid

section AnalyticManifold

/-- An analytic manifold w.r.t. a model `I : ModelWithCorners 𝕜 E H` is a charted space over H
    s.t. all extended chart conversion maps are analytic. -/
class AnalyticManifold (I : ModelWithCorners 𝕜 E H) (M : Type*) [TopologicalSpace M]
  [ChartedSpace H M] extends HasGroupoid M (analyticGroupoid I) : Prop

/-- Normed spaces are analytic manifolds over themselves -/
instance AnalyticManifold.self : AnalyticManifold 𝓘(𝕜, E) E where

/-- `M × N` is a analytic manifold if `M` and `N` are -/
instance AnalyticManifold.prod {E A : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace A] [CompleteSpace E] {F B : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace B] [CompleteSpace F] {I : ModelWithCorners 𝕜 E A} {J : ModelWithCorners 𝕜 F B}
    {M : Type} [TopologicalSpace M] [ChartedSpace A M] [m : AnalyticManifold I M]
    {N : Type} [TopologicalSpace N] [ChartedSpace B N] [n : AnalyticManifold J N] :
    AnalyticManifold (I.prod J) (M × N) where
  compatible := by
    intro f g ⟨f1, f2, hf1, hf2, fe⟩ ⟨g1, g2, hg1, hg2, ge⟩
    rw [← fe, ← ge, PartialHomeomorph.prod_symm, PartialHomeomorph.prod_trans]
    exact analyticGroupoid_prod (m.toHasGroupoid.compatible f2 g2)
      (n.toHasGroupoid.compatible hf2 hg2)

/-- Complex manifolds are smooth manifolds -/
instance AnalyticManifold.smoothManifoldWithCorners [ChartedSpace H M] [cm : AnalyticManifold I M] :
    SmoothManifoldWithCorners I M := by
  have h : HasGroupoid M (analyticGroupoid I) := cm.toHasGroupoid
  simp only [analyticGroupoid, hasGroupoid_inf_iff] at h
  exact SmoothManifoldWithCorners.mk' (gr := h.1)

end AnalyticManifold
