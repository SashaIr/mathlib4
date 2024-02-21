/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Yury Kudryashov
-/
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

#align_import topology.uniform_space.compact_convergence from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Compact convergence (uniform convergence on compact sets)

Given a topological space `α` and a uniform space `β` (e.g., a metric space or a topological group),
the space of continuous maps `C(α, β)` carries a natural uniform space structure. We define this
uniform space structure in this file and also prove the following properties of the topology it
induces on `C(α, β)`:

 1. Given a sequence of continuous functions `Fₙ : α → β` together with some continuous `f : α → β`,
    then `Fₙ` converges to `f` as a sequence in `C(α, β)` iff `Fₙ` converges to `f` uniformly on
    each compact subset `K` of `α`.
 2. Given `Fₙ` and `f` as above and suppose `α` is locally compact, then `Fₙ` converges to `f` iff
    `Fₙ` converges to `f` locally uniformly.
 3. The topology coincides with the compact-open topology.

Property 1 is essentially true by definition, 2 follows from basic results about uniform
convergence, but 3 requires a little work and uses the Lebesgue number lemma.

## The uniform space structure

Given subsets `K ⊆ α` and `V ⊆ β × β`, let `E(K, V) ⊆ C(α, β) × C(α, β)` be the set of pairs of
continuous functions `α → β` which are `V`-close on `K`:
$$
  E(K, V) = \{ (f, g) | ∀ (x ∈ K), (f x, g x) ∈ V \}.
$$
Fixing some `f ∈ C(α, β)`, let `N(K, V, f) ⊆ C(α, β)` be the set of continuous functions `α → β`
which are `V`-close to `f` on `K`:
$$
  N(K, V, f) = \{ g | ∀ (x ∈ K), (f x, g x) ∈ V \}.
$$
Using this notation we can describe the uniform space structure and the topology it induces.
Specifically:
  * A subset `X ⊆ C(α, β) × C(α, β)` is an entourage for the uniform space structure on `C(α, β)`
    iff there exists a compact `K` and entourage `V` such that `E(K, V) ⊆ X`.
  * A subset `Y ⊆ C(α, β)` is a neighbourhood of `f` iff there exists a compact `K` and entourage
    `V` such that `N(K, V, f) ⊆ Y`.

The topology on `C(α, β)` thus has a natural subbasis (the compact-open subbasis) and a natural
neighbourhood basis (the compact-convergence neighbourhood basis).

## Main definitions / results

 * `ContinuousMap.compactOpen_eq_compactConvergence`: the compact-open topology is equal to the
   compact-convergence topology.
 * `ContinuousMap.compactConvergenceUniformSpace`: the uniform space structure on `C(α, β)`.
 * `ContinuousMap.mem_compactConvergence_entourage_iff`: a characterisation of the entourages
    of `C(α, β)`.
 * `ContinuousMap.tendsto_iff_forall_compact_tendstoUniformlyOn`: a sequence of functions `Fₙ` in
    `C(α, β)` converges to some `f` iff `Fₙ` converges to `f` uniformly on each compact subset
    `K` of `α`.
 * `ContinuousMap.tendsto_iff_tendstoLocallyUniformly`: on a locally compact space, a sequence of
    functions `Fₙ` in `C(α, β)` converges to some `f` iff `Fₙ` converges to `f` locally uniformly.
 * `ContinuousMap.tendsto_iff_tendstoUniformly`: on a compact space, a sequence of functions `Fₙ` in
    `C(α, β)` converges to some `f` iff `Fₙ` converges to `f` uniformly.

## Implementation details

We use the forgetful inheritance pattern (see Note [forgetful inheritance]) to make the topology
of the uniform space structure on `C(α, β)` definitionally equal to the compact-open topology.

## TODO

 * When `β` is a metric space, there is natural basis for the compact-convergence topology
   parameterised by triples `(K, ε, f)` for a real number `ε > 0`.
 * When `α` is compact and `β` is a metric space, the compact-convergence topology (and thus also
   the compact-open topology) is metrisable.
 * Results about uniformly continuous functions `γ → C(α, β)` and uniform limits of sequences
   `ι → γ → C(α, β)`.
-/


universe u₁ u₂ u₃

open scoped Uniformity Topology UniformConvergence

open UniformSpace Set Filter

variable {α : Type u₁} {β : Type u₂} [TopologicalSpace α] [UniformSpace β]

variable (K : Set α) (V : Set (β × β)) (f : C(α, β))

namespace ContinuousMap

/-- Compact-open topology on `C(α, β)` agrees with the topology of uniform convergence on compacts:
a family of continuous functions `F i` tends to `f` in the compact-open topology
if and only if the `F i` tends to `f` uniformly on all compact sets. -/
theorem tendsto_iff_forall_compact_tendstoUniformlyOn
    {ι : Type u₃} {p : Filter ι} {F : ι → C(α, β)} {f} :
    Tendsto F p (𝓝 f) ↔ ∀ K, IsCompact K → TendstoUniformlyOn (fun i a => F i a) f p K := by
  rw [tendsto_nhds_compactOpen]
  constructor
  · -- Let us prove that convergence in the compact-open topology
    -- implies uniform convergence on compacts.
    -- Consider a compact set `K`
    intro h K hK
    -- Since `K` is compact, it suffices to prove locally uniform convergence
    rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK]
    -- Now choose an entourage `U` in the codomain and a point `x ∈ K`.
    intro U hU x _
    -- Choose an open symmetric entourage `V` such that `V ○ V ⊆ U`.
    rcases comp_open_symm_mem_uniformity_sets hU with ⟨V, hV, hVo, hVsymm, hVU⟩
    -- Then choose a closed entourage `W ⊆ V`
    rcases mem_uniformity_isClosed hV with ⟨W, hW, hWc, hWU⟩
    -- Consider `s = {y ∈ K | (f x, f y) ∈ W}`
    set s := K ∩ f ⁻¹' ball (f x) W
    -- This is a neighbourhood of `x` within `K`, because `W` is an entourage.
    have hnhds : s ∈ 𝓝[K] x := inter_mem_nhdsWithin _ <| f.continuousAt _ (ball_mem_nhds _ hW)
    -- This set is compact because it is an intersection of `K`
    -- with a closed set `{y | (f x, f y) ∈ W} = f ⁻¹' UniformSpace.ball (f x) W`
    have hcomp : IsCompact s := hK.inter_right <| (isClosed_ball _ hWc).preimage f.continuous
    -- `f` maps `s` to the open set `ball (f x) V = {z | (f x, z) ∈ V}`
    have hmaps : MapsTo f s (ball (f x) V) := fun x hx ↦ hWU hx.2
    use s, hnhds
    -- Continuous maps `F i` in a neighbourhood of `f` map `s` to `ball (f x) V` as well.
    refine (h s hcomp _ (isOpen_ball _ hVo) hmaps).mono fun g hg y hy ↦ ?_
    -- Then for `y ∈ s` we have `(f y, f x) ∈ V` and `(f x, F i y) ∈ V`, thus `(f y, F i y) ∈ U`
    exact hVU ⟨f x, hVsymm.mk_mem_comm.2 <| hmaps hy, hg hy⟩
  · -- Now we prove that uniform convergence on compacts
    -- implies convergence in the compact-open topology
    -- Consider a compact set `K`, an open set `U`, and a continuous map `f` that maps `K` to `U`
    intro h K hK U hU hf
    -- Due to Lebesgue number lemma, there exists an entourage `V`
    -- such that `U` includes the `V`-thickening of `f '' K`.
    rcases lebesgue_number_of_compact_open (hK.image (map_continuous f)) hU hf.image_subset
        with ⟨V, hV, -, hVf⟩
    -- Then any continuous map that is uniformly `V`-close to `f` on `K`
    -- maps `K` to `U` as well
    filter_upwards [h K hK V hV] with g hg x hx using hVf _ (mem_image_of_mem f hx) (hg x hx)
#align continuous_map.tendsto_iff_forall_compact_tendsto_uniformly_on ContinuousMap.tendsto_iff_forall_compact_tendstoUniformlyOn

/-- Interpret a bundled continuous map as an element of `α →ᵤ[{K | IsCompact K}] β`.

We use this map to induce the `UniformSpace` structure on `C(α, β)`. -/
def toUniformOnFun (f : C(α, β)) : α →ᵤ[{K | IsCompact K}] β :=
  UniformOnFun.ofFun {K | IsCompact K} f

@[simp]
theorem toUniformOnFun_toFun (f : C(α, β)) : UniformOnFun.toFun _ f.toUniformOnFun = f := rfl

open UniformSpace in
/-- Uniform space structure on `C(α, β)`.

The uniformity comes from `α →ᵤ[{K | IsCompact K}] β`
which defines topology of uniform convergence on compact sets.
We use `tendsto_iff_forall_compact_tendstoUniformlyOn`
to show that the induced topology agrees with the compact-open topology
and replace the topology with `compactOpen` to avoid non-defeq diamonds.  -/
instance compactConvergenceUniformSpace : UniformSpace (C(α, β)) :=
  .replaceTopology (.comap toUniformOnFun inferInstance) <| by
    refine eq_of_nhds_eq_nhds fun f ↦ eq_of_forall_le_iff fun l ↦ ?_
    simp_rw [← tendsto_id', tendsto_iff_forall_compact_tendstoUniformlyOn,
      nhds_induced, tendsto_comap_iff, UniformOnFun.tendsto_iff_tendstoUniformlyOn]
    rfl
#align continuous_map.compact_convergence_uniform_space ContinuousMap.compactConvergenceUniformSpace

theorem uniformEmbedding_toUniformOnFun :
    UniformEmbedding (toUniformOnFun : C(α, β) → α →ᵤ[{K | IsCompact K}] β) where
  comap_uniformity := rfl
  inj := DFunLike.coe_injective

-- The following definitions and theorems
-- used to be a part of the construction of the `UniformSpace (C(α, β))` structure
-- before it was migrated to `UniformOnFun`
#noalign continuous_map.compact_conv_nhd
#noalign continuous_map.self_mem_compact_conv_nhd
#noalign continuous_map.compact_conv_nhd_mono
#noalign continuous_map.compact_conv_nhd_mem_comp
#noalign continuous_map.compact_conv_nhd_nhd_basis
#noalign continuous_map.compact_conv_nhd_subset_inter
#noalign continuous_map.compact_conv_nhd_compact_entourage_nonempty
#noalign continuous_map.compact_conv_nhd_filter_is_basis
#noalign continuous_map.compact_convergence_filter_basis
#noalign continuous_map.mem_compact_convergence_nhd_filter
#noalign continuous_map.compact_convergence_topology
#noalign continuous_map.nhds_compact_convergence
#noalign continuous_map.has_basis_nhds_compact_convergence
#noalign continuous_map.tendsto_iff_forall_compact_tendsto_uniformly_on'
#noalign continuous_map.compact_conv_nhd_subset_compact_open
#noalign continuous_map.Inter_compact_open_gen_subset_compact_conv_nhd
#noalign continuous_map.compact_open_eq_compact_convergence
#noalign continuous_map.compact_convergence_uniformity
#noalign continuous_map.has_basis_compact_convergence_uniformity_aux
#noalign continuous_map.mem_compact_convergence_uniformity

theorem _root_.Filter.HasBasis.compactConvergenceUniformity {ι : Type*} {pi : ι → Prop}
    {s : ι → Set (β × β)} (h : (𝓤 β).HasBasis pi s) :
    HasBasis (𝓤 C(α, β)) (fun p : Set α × ι => IsCompact p.1 ∧ pi p.2) fun p =>
      { fg : C(α, β) × C(α, β) | ∀ x ∈ p.1, (fg.1 x, fg.2 x) ∈ s p.2 } := by
  rw [← uniformEmbedding_toUniformOnFun.comap_uniformity]
  exact .comap _ <| UniformOnFun.hasBasis_uniformity_of_basis _ _ {K | IsCompact K}
    ⟨∅, isCompact_empty⟩ (directedOn_of_sup_mem fun _ _ ↦ IsCompact.union) h
#align filter.has_basis.compact_convergence_uniformity Filter.HasBasis.compactConvergenceUniformity

theorem hasBasis_compactConvergenceUniformity :
    HasBasis (𝓤 C(α, β)) (fun p : Set α × Set (β × β) => IsCompact p.1 ∧ p.2 ∈ 𝓤 β) fun p =>
      { fg : C(α, β) × C(α, β) | ∀ x ∈ p.1, (fg.1 x, fg.2 x) ∈ p.2 } :=
  (basis_sets _).compactConvergenceUniformity
#align continuous_map.has_basis_compact_convergence_uniformity ContinuousMap.hasBasis_compactConvergenceUniformity

theorem mem_compactConvergence_entourage_iff (X : Set (C(α, β) × C(α, β))) :
    X ∈ 𝓤 C(α, β) ↔
      ∃ (K : Set α) (V : Set (β × β)), IsCompact K ∧ V ∈ 𝓤 β ∧
        { fg : C(α, β) × C(α, β) | ∀ x ∈ K, (fg.1 x, fg.2 x) ∈ V } ⊆ X := by
  simp [hasBasis_compactConvergenceUniformity.mem_iff, and_assoc]
#align continuous_map.mem_compact_convergence_entourage_iff ContinuousMap.mem_compactConvergence_entourage_iff

variable {ι : Type u₃} {p : Filter ι} {F : ι → C(α, β)} {f}


/-- Locally uniform convergence implies convergence in the compact-open topology. -/
theorem tendsto_of_tendstoLocallyUniformly (h : TendstoLocallyUniformly (fun i a => F i a) f p) :
    Tendsto F p (𝓝 f) := by
  rw [tendsto_iff_forall_compact_tendstoUniformlyOn]
  intro K hK
  rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK]
  exact h.tendstoLocallyUniformlyOn
#align continuous_map.tendsto_of_tendsto_locally_uniformly ContinuousMap.tendsto_of_tendstoLocallyUniformly

/-- In a weakly locally compact space,
convergence in the compact-open topology is the same as locally uniform convergence.

The right-to-left implication holds in any topological space,
see `ContinuousMap.tendsto_of_tendstoLocallyUniformly`. -/
theorem tendsto_iff_tendstoLocallyUniformly [WeaklyLocallyCompactSpace α] :
    Tendsto F p (𝓝 f) ↔ TendstoLocallyUniformly (fun i a => F i a) f p := by
  refine ⟨fun h V hV x ↦ ?_, tendsto_of_tendstoLocallyUniformly⟩
  rw [tendsto_iff_forall_compact_tendstoUniformlyOn] at h
  obtain ⟨n, hn₁, hn₂⟩ := exists_compact_mem_nhds x
  exact ⟨n, hn₂, h n hn₁ V hV⟩
#align continuous_map.tendsto_iff_tendsto_locally_uniformly ContinuousMap.tendsto_iff_tendstoLocallyUniformly

@[deprecated tendsto_iff_tendstoLocallyUniformly]
theorem tendstoLocallyUniformly_of_tendsto [WeaklyLocallyCompactSpace α] (h : Tendsto F p (𝓝 f)) :
    TendstoLocallyUniformly (fun i a => F i a) f p :=
  tendsto_iff_tendstoLocallyUniformly.1 h
#align continuous_map.tendsto_locally_uniformly_of_tendsto ContinuousMap.tendstoLocallyUniformly_of_tendsto

section CompactDomain

variable [CompactSpace α]

theorem hasBasis_compactConvergenceUniformity_of_compact :
    HasBasis (𝓤 C(α, β)) (fun V : Set (β × β) => V ∈ 𝓤 β) fun V =>
      { fg : C(α, β) × C(α, β) | ∀ x, (fg.1 x, fg.2 x) ∈ V } :=
  hasBasis_compactConvergenceUniformity.to_hasBasis
    (fun p hp => ⟨p.2, hp.2, fun _fg hfg x _hx => hfg x⟩) fun V hV =>
    ⟨⟨univ, V⟩, ⟨isCompact_univ, hV⟩, fun _fg hfg x => hfg x (mem_univ x)⟩
#align continuous_map.has_basis_compact_convergence_uniformity_of_compact ContinuousMap.hasBasis_compactConvergenceUniformity_of_compact

/-- Convergence in the compact-open topology is the same as uniform convergence for sequences of
continuous functions on a compact space. -/
theorem tendsto_iff_tendstoUniformly :
    Tendsto F p (𝓝 f) ↔ TendstoUniformly (fun i a => F i a) f p := by
  rw [tendsto_iff_forall_compact_tendstoUniformlyOn, ← tendstoUniformlyOn_univ]
  exact ⟨fun h => h univ isCompact_univ, fun h K _hK => h.mono (subset_univ K)⟩
#align continuous_map.tendsto_iff_tendsto_uniformly ContinuousMap.tendsto_iff_tendstoUniformly

end CompactDomain

end ContinuousMap
