import Mathlib.Algebra.Algebra.Spectrum
-- these are only needed for the last three declarations, and I think maybe we only need the last
-- one?
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.ContinuousFunction.Algebra
/-!
## Restriction of the spectrum

Suppose that `A` is an `S`-algebra and `S` is an `R`-algebra. For `a : A`, what is the relationship
between `spectrum R a` and `spectrum S a`? Of course, these live in different places, and in general
the relationship is `spectrum R a = algebraMap R S ⁻¹' spectrum S a`. One might wonder under what
conditions one has `algebraMap R S '' spectrum R a = spectrum S a`. We provide a predicate here
called `SpectrumRestricts` which takes an `a : A` and a function `f : S → R` and says that
`f ∘ algebraMap R S = id` and the restriction of `algebraMap R S ∘ f` to `spectrum S a` is the
identity. Of course, this forces `algebraMap R S` to be a ring embedding, and also this is
sufficient to guarantee `algebraMap R S '' spectrum R a = spectrum S a`.
This predicate is useful for restricting a continuous functional calculus over the ring `S` to one
over the ring `R`.
-/


/-- Given an element `a : A` of an `S`-algebra, where `S` is itself an `R`-algebra, we say that
the spectrum of `a` restricts via a function `f : S → R` if `f` is a left inverse of
`algebraMap R S`, and `f` is a right inverse of `algebraMap R S` on `spectrum S a`.

This is property allows us to restrict a continuous functional calculus over `S` to a
continuous functional calculus over `R`. -/
structure SpectrumRestricts {R S A : Type*} [CommSemiring R] [CommSemiring S] [Ring A]
    [Algebra R S] [Algebra R A] [Algebra S A] (a : A) (f : S → R) : Prop where
  /-- `f` is a right inverse of `algebraMap R S` when restricted to `spectrum S a`. -/
  rightInvOn : (spectrum S a).RightInvOn f (algebraMap R S)
  /-- `f` is a left inverse of `algebraMap R S`. -/
  left_inv : Function.LeftInverse f (algebraMap R S)

variable {R S A : Type*} [CommSemiring R] [CommSemiring S] [Ring A]
    [Algebra R S] [Algebra R A] [Algebra S A]

theorem spectrumRestricts_of_subset_range_algebraMap (a : A) (f : S → R)
    (hf : Function.LeftInverse f (algebraMap R S)) (h : spectrum S a ⊆ Set.range (algebraMap R S)) :
    SpectrumRestricts a f where
  rightInvOn := fun s hs => by obtain ⟨r, rfl⟩ := h hs; rw [hf r]
  left_inv := hf

variable [IsScalarTower R S A] {a : A} {f : S → R} (h : SpectrumRestricts a f)

theorem SpectrumRestricts.algebraMap_image : algebraMap R S '' spectrum R a = spectrum S a := by
  refine' Set.eq_of_subset_of_subset _ fun s hs => ⟨f s, _⟩
  simpa only [spectrum.preimage_algebraMap] using
    (spectrum S a).image_preimage_subset (algebraMap R S)
  exact ⟨spectrum.of_algebraMap_mem S ((h.rightInvOn hs).symm ▸ hs), h.rightInvOn hs⟩

theorem SpectrumRestricts.image : f '' spectrum S a = spectrum R a := by
  simp only [← h.algebraMap_image, Set.image_image, h.left_inv _, Set.image_id']

theorem SpectrumRestricts.apply_mem {s : S} (hs : s ∈ spectrum S a) : f s ∈ spectrum R a :=
  h.image ▸ ⟨s, hs, rfl⟩

theorem SpectrumRestricts.subset_preimage : spectrum S a ⊆ f ⁻¹' spectrum R a :=
  h.image ▸ (spectrum S a).subset_preimage_image f

lemma SpectrumRestricts.compactSpace [TopologicalSpace R] [TopologicalSpace S] (f : C(S, R))
    (h : SpectrumRestricts a f) [h_cpct : CompactSpace (spectrum S a)] :
    CompactSpace (spectrum R a) := by
  rw [← isCompact_iff_compactSpace] at h_cpct ⊢
  exact h.image ▸ h_cpct.image (map_continuous f)

universe u v w

/-- If the spectrum of an element restricts to a smaller scalar ring, then a continuous functional
calculus over the larger scalar ring descends to the smaller one. -/
@[simps!]
def SpectrumRestricts.starAlgHom {R : Type u} {S : Type v} {A : Type w} [CommSemiring R]
    [StarRing R] [TopologicalSpace R] [TopologicalSemiring R] [ContinuousStar R] [CommSemiring S]
    [StarRing S] [TopologicalSpace S] [TopologicalSemiring S] [ContinuousStar S] [Ring A]
    [StarRing A] [Algebra R S] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S] {a : A}
    (φ : C(spectrum S a, S) →⋆ₐ[S] A) (f : C(S, R)) (h : SpectrumRestricts a f) :
    C(spectrum R a, R) →⋆ₐ[R] A :=
  (φ.restrictScalars R).comp <|
    (ContinuousMap.compStarAlgHom (spectrum S a) (.ofId R S) (algebraMapCLM R S).continuous).comp <|
      ContinuousMap.compStarAlgHom' R R
        ⟨Subtype.map f h.subset_preimage, (map_continuous f).subtype_map
          fun x (hx : x ∈ spectrum S a) => h.subset_preimage hx⟩
