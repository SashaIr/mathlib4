/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot
-/
import Mathlib.Tactic.ApplyFun
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.Separation

#align_import topology.uniform_space.separation from "leanprover-community/mathlib"@"0c1f285a9f6e608ae2bdffa3f993eafb01eba829"

/-!
# Hausdorff properties of uniform spaces. Separation quotient.

This file studies uniform spaces whose underlying topological spaces are separated
(also known as Hausdorff or T₂).
This turns out to be equivalent to asking that the intersection of all entourages
is the diagonal only. This condition actually implies the stronger separation property
that the space is T₃, hence those conditions are equivalent for topologies coming from
a uniform structure.

More generally, the intersection `𝓢 X` of all entourages of `X`, which has type `Set (X × X)` is an
equivalence relation on `X`. Points which are equivalent under the relation are basically
undistinguishable from the point of view of the uniform structure. For instance any uniformly
continuous function will send equivalent points to the same value.

The quotient `SeparationQuotient X` of `X` by `𝓢 X` has a natural uniform structure which is
separated, and satisfies a universal property: every uniformly continuous function
from `X` to a separated uniform space uniquely factors through `SeparationQuotient X`.
As usual, this allows to turn `SeparationQuotient` into a functor (but we don't use the
category theory library in this file).

These notions admit relative versions, one can ask that `s : Set X` is separated, this
is equivalent to asking that the uniform structure induced on `s` is separated.

## Main definitions

* `separationRel X : Set (X × X)`: the separation relation
* `SeparatedSpace X`: a predicate class asserting that `X` is separated
* `SeparationQuotient X`: the maximal separated quotient of `X`.
* `SeparationQuotient.lift f`: factors a map `f : X → Y` through the separation quotient of `X`.
* `SeparationQuotient.map f`: turns a map `f : X → Y` into a map between the separation quotients
  of `X` and `Y`.

## Main results

* `separated_iff_t2`: the equivalence between being separated and being Hausdorff for uniform
  spaces.
* `SeparationQuotient.uniformContinuous_lift`: factoring a uniformly continuous map through the
  separation quotient gives a uniformly continuous map.
* `SeparationQuotient.uniformContinuous_map`: maps induced between separation quotients are
  uniformly continuous.

## Notations

Localized in `uniformity`, we have the notation `𝓢 X` for the separation relation
on a uniform space `X`,

## Implementation notes

The separation setoid `separationSetoid` is not declared as a global instance.
It is made a local instance while building the theory of `SeparationQuotient`.
The factored map `SeparationQuotient.lift f` is defined without imposing any condition on
`f`, but returns junk if `f` is not uniformly continuous (constant junk hence it is always
uniformly continuous).

-/

open Filter Set Function Topology Uniformity UniformSpace
open scoped Classical

noncomputable section

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
variable [UniformSpace α] [UniformSpace β] [UniformSpace γ]

/-!
### Separated uniform spaces
-/

instance (priority := 100) UniformSpace.to_regularSpace : RegularSpace α :=
  .ofBasis
    (fun _ => nhds_basis_uniformity' uniformity_hasBasis_closed)
    fun _ _ h => h.2.preimage <| continuous_const.prod_mk continuous_id
#align uniform_space.to_regular_space UniformSpace.to_regularSpace

#align separation_rel Inseparable
#noalign separated_equiv
#noalign filter.has_basis.mem_separation_rel
#noalign separation_rel_iff_specializes
#noalign separation_rel_iff_inseparable

theorem Filter.HasBasis.specializes_iff_uniformity {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)}
    (h : (𝓤 α).HasBasis p s) {x y : α} : x ⤳ y ↔ ∀ i, p i → (x, y) ∈ s i :=
  (nhds_basis_uniformity h).specializes_iff

theorem Filter.HasBasis.inseparable_iff_uniformity {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)}
    (h : (𝓤 α).HasBasis p s) {x y : α} : Inseparable x y ↔ ∀ i, p i → (x, y) ∈ s i :=
  specializes_iff_inseparable.symm.trans h.specializes_iff_uniformity

#align separated_space T0Space
#noalign separated_space_iff

theorem t0Space_iff_uniformity :
    T0Space α ↔ ∀ x y, (∀ r ∈ 𝓤 α, (x, y) ∈ r) → x = y := by
  simp only [t0Space_iff_inseparable, (𝓤 α).basis_sets.inseparable_iff_uniformity, id]
#align separated_def t0Space_iff_uniformity

theorem t0Space_iff_uniformity' :
    T0Space α ↔ ∀ x y, x ≠ y → ∃ r ∈ 𝓤 α, (x, y) ∉ r := by
  simp [t0Space_iff_not_inseparable, (𝓤 α).basis_sets.inseparable_iff_uniformity]
#align separated_def' t0Space_iff_uniformity'

theorem eq_of_uniformity {α : Type*} [UniformSpace α] [T0Space α] {x y : α}
    (h : ∀ {V}, V ∈ 𝓤 α → (x, y) ∈ V) : x = y :=
  t0Space_iff_uniformity.mp ‹T0Space α› x y @h
#align eq_of_uniformity eq_of_uniformity

theorem eq_of_uniformity_basis {α : Type*} [UniformSpace α] [T0Space α] {ι : Sort*}
    {p : ι → Prop} {s : ι → Set (α × α)} (hs : (𝓤 α).HasBasis p s) {x y : α}
    (h : ∀ {i}, p i → (x, y) ∈ s i) : x = y :=
  (hs.inseparable_iff_uniformity.2 @h).eq
#align eq_of_uniformity_basis eq_of_uniformity_basis

theorem eq_of_forall_symmetric {α : Type*} [UniformSpace α] [T0Space α] {x y : α}
    (h : ∀ {V}, V ∈ 𝓤 α → SymmetricRel V → (x, y) ∈ V) : x = y :=
  eq_of_uniformity_basis hasBasis_symmetric (by simpa)
#align eq_of_forall_symmetric eq_of_forall_symmetric

theorem eq_of_clusterPt_uniformity [T0Space α] {x y : α} (h : ClusterPt (x, y) (𝓤 α)) : x = y :=
  eq_of_uniformity_basis uniformity_hasBasis_closed fun ⟨hV, hVc⟩ =>
    isClosed_iff_clusterPt.1 hVc _ <| h.mono <| le_principal_iff.2 hV
#align eq_of_cluster_pt_uniformity eq_of_clusterPt_uniformity

#noalign id_rel_sub_separation_relation
#align separation_rel_comap Inducing.inseparable_iff
#noalign filter.has_basis.separation_rel
#noalign separation_rel_eq_inter_closure
#align is_closed_separation_rel isClosed_setOf_inseparable
#noalign separated_iff_t2
#noalign separated_t3
#align subtype.separated_space Subtype.t0Space

theorem isClosed_of_spaced_out [T0Space α] {V₀ : Set (α × α)} (V₀_in : V₀ ∈ 𝓤 α) {s : Set α}
    (hs : s.Pairwise fun x y => (x, y) ∉ V₀) : IsClosed s := by
  rcases comp_symm_mem_uniformity_sets V₀_in with ⟨V₁, V₁_in, V₁_symm, h_comp⟩
  apply isClosed_of_closure_subset
  intro x hx
  rw [mem_closure_iff_ball] at hx
  rcases hx V₁_in with ⟨y, hy, hy'⟩
  suffices x = y by rwa [this]
  apply eq_of_forall_symmetric
  intro V V_in _
  rcases hx (inter_mem V₁_in V_in) with ⟨z, hz, hz'⟩
  obtain rfl : z = y := by
    by_contra hzy
    exact hs hz' hy' hzy (h_comp <| mem_comp_of_mem_ball V₁_symm (ball_inter_left x _ _ hz) hy)
  exact ball_inter_right x _ _ hz
#align is_closed_of_spaced_out isClosed_of_spaced_out

theorem isClosed_range_of_spaced_out {ι} [T0Space α] {V₀ : Set (α × α)} (V₀_in : V₀ ∈ 𝓤 α)
    {f : ι → α} (hf : Pairwise fun x y => (f x, f y) ∉ V₀) : IsClosed (range f) :=
  isClosed_of_spaced_out V₀_in <| by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
    exact hf (ne_of_apply_ne f h)
#align is_closed_range_of_spaced_out isClosed_range_of_spaced_out

/-!
### Separation quotient
-/

#align uniform_space.separation_setoid inseparableSetoid

namespace SeparationQuotient

theorem comap_map_mk_uniformity : comap (Prod.map mk mk) (map (Prod.map mk mk) (𝓤 α)) = 𝓤 α := by
  refine le_antisymm ?_ le_comap_map
  refine ((((𝓤 α).basis_sets.map _).comap _).le_basis_iff uniformity_hasBasis_open).2 fun U hU ↦ ?_
  refine ⟨U, hU.1, fun (x₁, x₂) ⟨(y₁, y₂), hyU, hxy⟩ ↦ ?_⟩
  simp only [Prod.map, Prod.ext_iff, mk_eq_mk] at hxy
  exact ((hxy.1.prod hxy.2).mem_open_iff hU.2).1 hyU

instance instUniformSpace : UniformSpace (SeparationQuotient α) :=
  .ofNhdsEqComap
    { uniformity := map (Prod.map mk mk) (𝓤 α)
      refl := le_trans (by simpa using surjective_mk) (Filter.map_mono refl_le_uniformity)
      symm := tendsto_map' <| tendsto_map.comp tendsto_swap_uniformity
      comp := fun t ht ↦ by
        rcases comp_open_symm_mem_uniformity_sets ht with ⟨U, hU, hUo, -, hUt⟩
        refine mem_of_superset (mem_lift' <| image_mem_map hU) ?_
        simp only [subset_def, Prod.forall, mem_compRel, mem_image, Prod.ext_iff]
        rintro _ _ ⟨_, ⟨⟨x, y⟩, hxyU, rfl, rfl⟩, ⟨⟨y', z⟩, hyzU, hy, rfl⟩⟩
        have : y' ⤳ y := (mk_eq_mk.1 hy).specializes
        exact @hUt (x, z) ⟨y', this.mem_open (UniformSpace.isOpen_ball _ hUo) hxyU, hyzU⟩ }
    inferInstance <| surjective_mk.forall.2 fun x ↦ comap_injective surjective_mk <| by
      conv_lhs => rw [comap_mk_nhds_mk, nhds_eq_comap_uniformity, ← comap_map_mk_uniformity]
      simp only [Filter.comap_comap]; rfl

end SeparationQuotient

namespace UniformSpace

alias SeparationQuotient := _root_.SeparationQuotient

namespace SeparationQuotient

instance instUniformSpace : UniformSpace (SeparationQuotient α) :=
  _root_.SeparationQuotient.instUniformSpace
#align uniform_space.separation_setoid.uniform_space UniformSpace.SeparationQuotient.instUniformSpace

attribute [local instance] inseparableSetoid

theorem uniformity_quotient :
    𝓤 (SeparationQuotient α) = (𝓤 α).map fun p : α × α => (⟦p.1⟧, ⟦p.2⟧) :=
  rfl
#align uniform_space.uniformity_quotient UniformSpace.SeparationQuotient.uniformity_quotient

theorem uniformContinuous_quotient_mk' :
    UniformContinuous (Quotient.mk' : α → SeparationQuotient α) :=
  le_rfl
#align uniform_space.uniform_continuous_quotient_mk UniformSpace.uniformContinuous_quotient_mk'

theorem uniformContinuous_quotient_mk : UniformContinuous (Quotient.mk (separationSetoid α)) :=
  le_rfl

theorem uniformContinuous_quotient {f : Quotient (separationSetoid α) → β}
    (hf : UniformContinuous fun x => f ⟦x⟧) : UniformContinuous f :=
  hf
#align uniform_space.uniform_continuous_quotient UniformSpace.uniformContinuous_quotient

theorem uniformContinuous_quotient_lift {f : α → β} {h : ∀ a b, (a, b) ∈ 𝓢 α → f a = f b}
    (hf : UniformContinuous f) : UniformContinuous fun a => Quotient.lift f h a :=
  uniformContinuous_quotient hf
#align uniform_space.uniform_continuous_quotient_lift UniformSpace.uniformContinuous_quotient_lift

theorem uniformContinuous_quotient_lift₂ {f : α → β → γ}
    {h : ∀ a c b d, (a, b) ∈ 𝓢 α → (c, d) ∈ 𝓢 β → f a c = f b d}
    (hf : UniformContinuous fun p : α × β => f p.1 p.2) :
    UniformContinuous fun p : _ × _ => Quotient.lift₂ f h p.1 p.2 := by
  rw [UniformContinuous, uniformity_prod_eq_prod, uniformity_quotient, uniformity_quotient,
    Filter.prod_map_map_eq, Filter.tendsto_map'_iff, Filter.tendsto_map'_iff]
  rwa [UniformContinuous, uniformity_prod_eq_prod, Filter.tendsto_map'_iff] at hf
#align uniform_space.uniform_continuous_quotient_lift₂ UniformSpace.uniformContinuous_quotient_lift₂

theorem comap_quotient_le_uniformity :
    ((𝓤 <| Quotient <| separationSetoid α).comap fun p : α × α => (⟦p.fst⟧, ⟦p.snd⟧)) ≤ 𝓤 α :=
  ((((𝓤 α).basis_sets.map _).comap _).le_basis_iff uniformity_hasBasis_open).2 fun U hU =>
    ⟨U, hU.1, fun ⟨x, y⟩ ⟨⟨x', y'⟩, hx', h⟩ => by
      simp only [Prod.ext_iff, Quotient.eq] at h
      exact (((separationRel_iff_inseparable.1 h.1).prod
        (separationRel_iff_inseparable.1 h.2)).mem_open_iff hU.2).1 hx'⟩
#align uniform_space.comap_quotient_le_uniformity UniformSpace.comap_quotient_le_uniformity

theorem comap_quotient_eq_uniformity :
    ((𝓤 <| Quotient <| separationSetoid α).comap fun p : α × α => (⟦p.fst⟧, ⟦p.snd⟧)) = 𝓤 α :=
  le_antisymm comap_quotient_le_uniformity le_comap_map
#align uniform_space.comap_quotient_eq_uniformity UniformSpace.comap_quotient_eq_uniformity

instance separated_separation : SeparatedSpace (Quotient (separationSetoid α)) :=
  ⟨Set.ext fun ⟨a, b⟩ =>
      Quotient.inductionOn₂ a b fun a b =>
        ⟨fun h =>
          have : a ≈ b := fun s hs =>
            have :
              s ∈ (𝓤 <| Quotient <| separationSetoid α).comap fun p : α × α => (⟦p.1⟧, ⟦p.2⟧) :=
              comap_quotient_le_uniformity hs
            let ⟨t, ht, hts⟩ := this
            hts (by dsimp [preimage]; exact h t ht)
          show ⟦a⟧ = ⟦b⟧ from Quotient.sound this,
          fun heq : ⟦a⟧ = ⟦b⟧ => fun h hs => heq ▸ refl_mem_uniformity hs⟩⟩
#align uniform_space.separated_separation UniformSpace.separated_separation

theorem separated_of_uniformContinuous {f : α → β} {x y : α} (H : UniformContinuous f) (h : x ≈ y) :
    f x ≈ f y := fun _ h' => h _ (H h')
#align uniform_space.separated_of_uniform_continuous UniformSpace.separated_of_uniformContinuous

theorem eq_of_separated_of_uniformContinuous [SeparatedSpace β] {f : α → β} {x y : α}
    (H : UniformContinuous f) (h : x ≈ y) : f x = f y :=
  separated_def.1 (by infer_instance) _ _ <| separated_of_uniformContinuous H h
#align uniform_space.eq_of_separated_of_uniform_continuous UniformSpace.eq_of_separated_of_uniformContinuous

/-- The maximal separated quotient of a uniform space `α`. -/
def SeparationQuotient (α : Type*) [UniformSpace α] :=
  Quotient (separationSetoid α)
#align uniform_space.separation_quotient UniformSpace.SeparationQuotient

namespace SeparationQuotient

instance : UniformSpace (SeparationQuotient α) :=
  separationSetoid.uniformSpace

instance : SeparatedSpace (SeparationQuotient α) :=
  UniformSpace.separated_separation

instance [Inhabited α] : Inhabited (SeparationQuotient α) :=
  inferInstanceAs (Inhabited (Quotient (separationSetoid α)))

lemma mk_eq_mk {x y : α} : (⟦x⟧ : SeparationQuotient α) = ⟦y⟧ ↔ Inseparable x y :=
  Quotient.eq'.trans separationRel_iff_inseparable
#align uniform_space.separation_quotient.mk_eq_mk UniformSpace.SeparationQuotient.mk_eq_mk

/-- Factoring functions to a separated space through the separation quotient. -/
def lift [SeparatedSpace β] (f : α → β) : SeparationQuotient α → β :=
  if h : UniformContinuous f then Quotient.lift f fun _ _ => eq_of_separated_of_uniformContinuous h
  else fun x => f (Nonempty.some ⟨x.out⟩)
#align uniform_space.separation_quotient.lift UniformSpace.SeparationQuotient.lift

theorem lift_mk [SeparatedSpace β] {f : α → β} (h : UniformContinuous f) (a : α) :
    lift f ⟦a⟧ = f a := by rw [lift, dif_pos h]; rfl
#align uniform_space.separation_quotient.lift_mk UniformSpace.SeparationQuotient.lift_mk

theorem uniformContinuous_lift [SeparatedSpace β] (f : α → β) : UniformContinuous (lift f) := by
  by_cases hf : UniformContinuous f
  · rw [lift, dif_pos hf]
    exact uniformContinuous_quotient_lift hf
  · rw [lift, dif_neg hf]
    exact uniformContinuous_of_const fun a _ => rfl
#align uniform_space.separation_quotient.uniform_continuous_lift UniformSpace.SeparationQuotient.uniformContinuous_lift

/-- The separation quotient functor acting on functions. -/
def map (f : α → β) : SeparationQuotient α → SeparationQuotient β :=
  lift (Quotient.mk' ∘ f)
#align uniform_space.separation_quotient.map UniformSpace.SeparationQuotient.map

theorem map_mk {f : α → β} (h : UniformContinuous f) (a : α) : map f ⟦a⟧ = ⟦f a⟧ := by
  rw [map, lift_mk (uniformContinuous_quotient_mk'.comp h)]; rfl
#align uniform_space.separation_quotient.map_mk UniformSpace.SeparationQuotient.map_mk

theorem uniformContinuous_map (f : α → β) : UniformContinuous (map f) :=
  uniformContinuous_lift (Quotient.mk' ∘ f)
#align uniform_space.separation_quotient.uniform_continuous_map UniformSpace.SeparationQuotient.uniformContinuous_map

theorem map_unique {f : α → β} (hf : UniformContinuous f)
    {g : SeparationQuotient α → SeparationQuotient β}
    (comm : Quotient.mk _ ∘ f = g ∘ Quotient.mk _) : map f = g := by
  ext ⟨a⟩
  calc
    map f ⟦a⟧ = ⟦f a⟧ := map_mk hf a
    _ = g ⟦a⟧ := congr_fun comm a
#align uniform_space.separation_quotient.map_unique UniformSpace.SeparationQuotient.map_unique

theorem map_id : map (@id α) = id :=
  map_unique uniformContinuous_id rfl
#align uniform_space.separation_quotient.map_id UniformSpace.SeparationQuotient.map_id

theorem map_comp {f : α → β} {g : β → γ} (hf : UniformContinuous f) (hg : UniformContinuous g) :
    map g ∘ map f = map (g ∘ f) :=
  (map_unique (hg.comp hf) <| by simp only [Function.comp, map_mk, hf, hg]).symm
#align uniform_space.separation_quotient.map_comp UniformSpace.SeparationQuotient.map_comp

end SeparationQuotient

#align uniform_space.separation_prod inseparable_prod
#align uniform_space.separated.prod Prod.instT0Space
