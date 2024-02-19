--import Mathlib.Analysis.NormedSpace.Star.Spectrum
import Mathlib.Analysis.NormedSpace.Star.CFC.CFCRestricts
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousFunction.Compact
import Mathlib.Topology.MetricSpace.Isometry

/-!
# The continuous functional calculus

This file defines a generic API for the *continuous functional calculus* which is suitable in a wide
range of settings.

A continuous functional calculus for an element `a : A` in a topological `R`-algebra is a continuous
extension of the polynomial functional calculus (i.e., `Polynomial.aeval`) to continuous `R`-valued
functions on `spectrum R a`. More precisely, it is a continuous star algebra homomorphism
`cfcSpec : C(spectrum R a, R) →⋆ₐ[R] A` that sends `(ContinuousMap.id R).restrict (spectrum R a)` to
`a`. This is the data contained in `CFCCoreClass` and in many cases (e.g., when `spectrum R a` is
compact and `R` is `ℝ≥0`, `ℝ`, or `ℂ`), this is sufficient to uniquely determine the continuous
functional calculus.

Although these properties suffice to uniquely determine the continuous functional calculus, we
choose to bundle more information into the class itself. Namely, we include that `cfcSpec` is a
closed embedding, and also that the spectrum of the image of `f : C(spectrum R a, R)` under
`cfcSpec` is the range of `f`. In addition, the class specifies a collection of continuous
functional calculi for elements satisfying a given predicate `p : A → Prop`, and we require that
this predicate is preserved by the functional calculus.

Although `cfcSpec : p a → C(spectrum R a, R) →*ₐ[R] A` is a necessity for getting the full power out of
the continuous functional calculus, this declaration will generally not be accessed directly by the
user. One reason for this is that `cfcSpec` requires a proof of `p a` (indeed, if the spectrum is
empty, there cannot exist a star algebra homomorphism like this). Instead, we provide the completely
unbundled `cfc : A → (R → R) → A` which operates on bare functions and provides junk values when either
`a` does not satisfy the property `p`, or else when the function which is the argument to `cfc` is
not continuous on the spectrum of `a`.

This completely unbundled approach may give up some conveniences, but it allows for tremendous
freedom. In particular, `cfc a f` makes sense for *any* `a : A` and `f : R → R`. This is quite
useful in a variety of settings, but perhaps the most important is the following.
Besides being a star algebra homomorphism sending the identity to `a`, the key property enjoyed
by the continuous functional calculus is the *composition property*, which guarantees that
`cfc a (g ∘ f) = cfc (cfc a f) g` under suitable hypotheses on `a`, `f` and `g`. Note that this
theorem is nearly impossible to state nicely in terms of `cfcSpec` (see `cfcSpec_comp`). An
additional advantage of the unbundled approach is that expressions like `fun x : R ↦ x⁻¹` are valid
arguments to `cfc a`, and a bundled continuous counterpart can only make sense when the spectrum of
`a` does not contain zero.

## Main statements

+ `ContinuousFunctionalCalculus R (p : A → Prop)`: a class stating that every `a : A` satisfying
  `p a` has a star algebra homomorphism from the continuous `R`-valued functions on the
  `R`-spectrum of `A`. This map is a closed embedding, and satisfies the
  **spectral mappping theorem**.
+ `cfcSpec : p a → C(spectrum R a, R) →⋆ₐ[R] A`: the underlying star algebra homomorphism for an
  element satisfying property `p`.
+ `cfc : A → (R → R) → A`: an unbundled version of `cfcSpec` which takes the junk value `0` when
  `cfcSpec` is not defined.
+ `cfc_units`: builds a unit from `cfc a f` when `f` is nonzero and continuous on the
  specturm of `a`.
+ `cfc_of_spectrumRestricts`: builds a continuous functional calculus over a scalar subring and a
  predicate `q` whenever `q` is a predicate equivalent to `p` along with the condition that the
  spectrum of an element satisfying `q` restricts to the scalar subring.

## Main theorems

+ `cfc_comp : cfc a (x ↦ g (f x)) = cfc (cfc a f) g`
+ `cfc_polynomial`: the continuous functional calculus extends the polynomial functional calculus.

## Implementation details

Instead of defining a class depending on a term `a : A`, we register it for an `outParam` predicate
`p : A → Prop`, and then any element of `A` satisfying this predicate has the associated star
algebra homomorphism with the specified properties. In so doing we avoid a common pitfall:
dependence of the class on a term. This avoids annoying situations where `a b : A` are
propositionally equal, but not definitionally so, and hence Lean would not be able to automatically
identify the continuous functional calculi associated to these elements. In order to guarantee
the necessary properties, we require that the continuous functional calculus preserves this
predicate. That is, `p a → p (cfc a f)` for any function `f` continuous on the spectrum of `a`.

As stated above, the unbundled approach to `cfc` has its advantages. For instance, given an
expression `cfc a f`, the user is free to rewrite either `a` or `f` as desired with no possibility
of the expression ceasing to be defined. However, this unbundling also has some potential downsides.
In particular, by unbundling, proof requirements are deferred until the user calls the lemmas, most
of which have hypotheses both of `p a` and of `ContinuousOn f (spectrum R a)`.

In order to minimize burden to the user, we provide `autoParams` in terms of two tactics. Goals
related to continuity are dispatched by (a small wrapper around) `fun_prop`. As for goals involving
the predicate `p`, it should be noted that these will only ever be of the form `IsStarNormal a`,
`IsSelfAdjoint a` or `0 ≤ a`. For the moment we provide a rudimentary tactic to deal with these
goals, but it can be modified to become more sophisticated as the need arises.
-/

#exit

section Basic

/-- A star `R`-algebra `A` has *continuous functional calculus* for elements satisfying the
property `p : A → Prop` if

+ for every such element `a : A` there is a star algebra homomorphism
  `cfcSpec : C(spectrum R a, R) →⋆ₐ[R] A` sending the (restriction of) the identity map to `a`.
+ `cfcSpec` is a closed embedding for which the spectrum of the image of function `f` is its range.
+ `cfcSpec` preserves the property `p`.

The property `p` is marked as an `outParam` so that the user need not specify it. In practice,

+ for `R := ℂ`, we choose `p := IsStarNormal`,
+ for `R := ℝ`, we choose `p := IsSelfAdjoint`,
+ for `R := ℝ≥0`, we choose `p := (0 ≤ ·)`.
-/
class ContinuousFunctionalCalculus (R : Type*) {A : Type*} (p : outParam (A → Prop))
    [CommSemiring R] [StarRing R] [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R]
    [Ring A] [StarRing A] [TopologicalSpace A] [Algebra R A] where
  /-- The star algebra homomorphisms. -/
  toStarAlgHom {a} (ha : p a) : C(spectrum R a, R) →⋆ₐ[R] A
  /-- A continuous functional calculus is a closed embedding. -/
  hom_closedEmbedding {a} (ha : p a) : ClosedEmbedding <| toStarAlgHom ha
  /-- A continuous functional calculus extends the polynomial functional calculus. -/
  hom_id {a} (ha : p a) : toStarAlgHom ha ((ContinuousMap.id R).restrict <| spectrum R a) = a
  /-- A continuous functional calculus satisfies the spectral mapping property. -/
  hom_map_spectrum {a} (ha : p a) : ∀ f, spectrum R (toStarAlgHom ha f) = Set.range f
  /-- Predicate preserving -/
  predicate_hom {a} (ha : p a) : ∀ f, p (toStarAlgHom ha f)

structure CFCCore {R A : Type*} [CommSemiring R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] (s : Set R) (a : A) extends C(s, R) →⋆ₐ[R] A where
  map_id' : toStarAlgHom ((ContinuousMap.id R).restrict s) = a
  map_continuous' : Continuous toStarAlgHom

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
variable [TopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
variable [Algebra R A] [ContinuousFunctionalCalculus R p]

section cfcSpec

variable {a : A} (ha : p a)

/- Note: since `spectrum R a` is closed, we may always extend `f : C(spectrum R a, R)` to a function
of type `C(R, R)` by the Tietze extension theorem (assuming `R` is either `ℝ`, `ℂ` or `ℝ≥0`). -/

/-- The star algebra homomorphism underlying a instance of the continuous functional calculus.
Version for continuous functions on the spectrum.

In this case, the user must supply the fact that `a` satisfies the predicate `p`, for otherwise it
may be the case that no star algebra homomorphism exists. For instance if `R := ℝ` and `a` is an
element whose spectrum (in `ℂ`) is disjoint from `ℝ`, then `spectrum ℝ a = ∅` and so there can be
no star algebra homomorphism between these spaces. -/
def cfcSpec : C(spectrum R a, R) →⋆ₐ[R] A :=
  ContinuousFunctionalCalculus.toStarAlgHom ha

lemma cfcSpec_closedEmbedding :
    ClosedEmbedding <| (cfcSpec ha : C(spectrum R a, R) →⋆ₐ[R] A) :=
  ContinuousFunctionalCalculus.hom_closedEmbedding ha

lemma cfcSpec_map_id :
    cfcSpec ha ((ContinuousMap.id R).restrict <| spectrum R a) = a :=
  ContinuousFunctionalCalculus.hom_id ha

/-- The **spectral mapping theorem** for the continuous functional calculus. -/
lemma cfcSpec_map_spectrum (f : C(spectrum R a, R)) :
    spectrum R (cfcSpec ha f) = Set.range f :=
  ContinuousFunctionalCalculus.hom_map_spectrum ha f

lemma cfcSpec_predicate (f : C(spectrum R a, R)) :
    p (cfcSpec ha f) :=
  ContinuousFunctionalCalculus.predicate_hom ha f

theorem cfcSpec_comp (f : C(spectrum R a, R))
    [Subsingleton (CFCCore (spectrum R (cfcSpec ha f)) (cfcSpec ha f))]
    (f' : C(spectrum R a, spectrum R (cfcSpec ha f)))
    (hff' : ∀ x, f x = f' x) (g : C(spectrum R (cfcSpec ha f), R)) :
    cfcSpec ha (g.comp f') = cfcSpec (cfcSpec_predicate ha f) g := by
  let cfc₂ : CFCCore (spectrum R (cfcSpec ha f)) (cfcSpec ha f) :=
    { toStarAlgHom := cfcSpec (cfcSpec_predicate ha f)
      map_id' := cfcSpec_map_id (cfcSpec_predicate ha f)
      map_continuous' := (cfcSpec_closedEmbedding (cfcSpec_predicate ha f)).continuous }
  let cfc₁ : CFCCore (spectrum R (cfcSpec ha f)) (cfcSpec ha f) :=
    { toStarAlgHom := (cfcSpec ha).comp <| ContinuousMap.compStarAlgHom' R R f'
      map_id' := by
        simp only [StarAlgHom.comp_apply, ContinuousMap.compStarAlgHom'_apply]
        congr
        ext x
        simp [hff']
      map_continuous' := (cfcSpec_closedEmbedding ha).continuous.comp f'.continuous_comp_left }
  have := congr_arg CFCCore.toStarAlgHom <| Subsingleton.elim cfc₁ cfc₂
  exact DFunLike.congr_fun this g

end cfcSpec

/-- Evaluation of continuous maps at a point, bundled as a star algebra homomorphism. -/
@[simps]
def ContinuousMap.evalStarAlgHom (r : R) : C(R, R) →⋆ₐ[R] R where
  toFun f := f r
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

section Bare

syntax (name := cfcTac) "cfc_tac" : tactic
macro_rules
  | `(tactic| cfc_tac) => `(tactic| (try (first | assumption | infer_instance | aesop)))

syntax (name := cfcContTac) "cfc_cont_tac" : tactic
macro_rules
  | `(tactic| cfc_cont_tac) => `(tactic| try (first | fun_prop (disch := aesop) | assumption))

/- This is a version of the continuous functional calculus for bare functions. It is most useful
when one prefers unbundled objects. For instance, the most general version of the composition
theorem is easily statable for `cfc`. -/
noncomputable irreducible_def cfc (a : A) (f : R → R) : A := by
  classical
  exact if h : p a ∧ ContinuousOn f (spectrum R a)
    then cfcSpec h.1 ⟨_, h.2.restrict⟩
    else 0 -- algebraMap R A (f 0) -- chosen to agree with `cfc`

variable (a : A)

lemma cfc_apply (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc a f = cfcSpec (a := a) ha ⟨_, hf.restrict⟩ := by
  rw [cfc_def, dif_pos ⟨ha, hf⟩]

lemma cfc_apply_of_not_and {f : R → R} (ha : ¬ (p a ∧ ContinuousOn f (spectrum R a))) :
    cfc a f = 0 := by
  rw [cfc_def, dif_neg ha]

lemma cfc_apply_of_not {f : R → R} (ha : ¬ p a) :
    cfc a f = 0 := by
  rw [cfc_def, dif_neg (not_and_of_not_left _ ha)]

lemma cfc_apply_of_not' {f : R → R} (hf : ¬ ContinuousOn f (spectrum R a)) :
    cfc a f = 0 := by
  rw [cfc_def, dif_neg (not_and_of_not_right _ hf)]

variable (R) in
lemma cfc_id (ha : p a := by cfc_tac) : cfc a (id : R → R) = a :=
  cfc_apply a (id : R → R) ▸ cfcSpec_map_id (p := p) ha

variable (R) in
lemma cfc_id' (ha : p a := by cfc_tac) : cfc a (fun x : R ↦ x) = a :=
  cfc_id R a

/-- The **spectral mapping theorem** for the continuous functional calculus. -/
lemma cfc_map_spectrum (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    spectrum R (cfc a f) = f '' spectrum R a := by
  simp [cfc_apply a f, cfcSpec_map_spectrum (p := p)]

lemma cfc_predicate (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    p (cfc a f) :=
  cfc_apply a f ▸ cfcSpec_predicate (A := A) ha _

lemma cfc_congr {f g : R → R} (hfg : (spectrum R a).EqOn f g) :
    cfc a f = cfc a g := by
  by_cases h : p a ∧ ContinuousOn g (spectrum R a)
  · rw [cfc_apply (ha := h.1) (hf := h.2.congr hfg), cfc_apply (ha := h.1) (hf := h.2)]
    congr
    exact Set.restrict_eq_iff.mpr hfg
  · classical
    obtain (ha | hg) := Decidable.not_and_iff_or_not _ _ |>.mp h
    · simp [cfc_apply_of_not a ha]
    · rw [cfc_apply_of_not' a hg, cfc_apply_of_not']
      exact fun hf ↦ hg (hf.congr hfg.symm)

lemma cfc_eqOn_of_eq {f g : R → R} (h : cfc a f = cfc a g) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) :
    (spectrum R a).EqOn f g := by
  rw [cfc_apply a f, cfc_apply a g] at h
  have := (cfcSpec_closedEmbedding (show p a from ha) (R := R)).inj h
  intro x hx
  congrm($(this) ⟨x, hx⟩)

attribute [fun_prop] continuous_one continuous_zero

lemma cfc_map_const (r : R) (ha : p a := by cfc_tac) :
    cfc a (fun _ ↦ r) = algebraMap R A r := by
  have h₁ := cfc_apply a (fun _ : R ↦ r)
  have h₂ := AlgHomClass.commutes (cfcSpec ha (p := p)) r
  exact h₁.trans <| Eq.trans (by congr) h₂

variable (R)

lemma cfc_map_one (ha : p a := by cfc_tac) : cfc a (1 : R → R) = 1 :=
  cfc_apply a (1 : R → R) ▸ map_one (cfcSpec (show p a from ha))

lemma cfc_map_one' (ha : p a := by cfc_tac) : cfc a (fun _ : R ↦ 1) = 1 :=
  cfc_map_one R a

lemma cfc_map_zero : cfc a (0 : R → R) = 0 := by
  by_cases ha : p a
  · exact cfc_apply a (0 : R → R) ▸ map_zero (cfcSpec ha)
  · rw [cfc_apply_of_not a ha]

lemma cfc_map_zero' : cfc a (0 : R → R) = 0 :=
  cfc_map_zero R a

variable {R}

lemma cfc_map_mul (f g : R → R)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) :
    cfc a (fun x ↦ f x * g x) = cfc a f * cfc a g := by
  have : ContinuousOn f (spectrum R a) := hf -- hack
  have : ContinuousOn g (spectrum R a) := hg -- hack
  by_cases ha : p a
  · rw [cfc_apply a f, cfc_apply a g, ← map_mul, cfc_apply a _]
    congr
  · simp [cfc_apply_of_not a ha]

lemma cfc_map_pow (f : R → R) (n : ℕ) (hn : n ≠ 0)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)  :
    cfc a (fun x ↦ (f x) ^ n) = cfc a f ^ n := by
  have : ContinuousOn f (spectrum R a) := hf
  by_cases ha : p a
  · rw [cfc_apply a f, ← map_pow, cfc_apply a _]
    congr
  · simp [cfc_apply_of_not a ha, zero_pow hn]

lemma cfc_map_add (f g : R → R)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) :
    cfc a (fun x ↦ f x + g x) = cfc a f + cfc a g := by
  have : ContinuousOn f (spectrum R a) := hf -- hack
  have : ContinuousOn g (spectrum R a) := hg -- hack
  by_cases ha : p a
  · rw [cfc_apply a f, cfc_apply a g, ← map_add, cfc_apply a _]
    congr
  · simp [cfc_apply_of_not a ha]

-- when `R := ℂ`, this should work for `S` being any of `ℕ`, `ℤ`, `ℝ≥0`, `ℝ`, `ℂ`.
lemma cfc_map_smul {S : Type*} [SMul S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R → R)]
    (s : S) (f : R → R) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc a (fun x ↦ s • f x) = s • cfc a f := by
  have : ContinuousOn f (spectrum R a) := hf -- hack
  by_cases ha : p a
  · rw [cfc_apply a f, cfc_apply a _]
    simp_rw [← Pi.smul_def, ← smul_one_smul R s _]
    rw [← map_smul]
    congr
  · simp [cfc_apply_of_not a ha]

lemma cfc_map_const_mul (r : R) (f : R → R)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc a (fun x ↦ r * f x) = r • cfc a f :=
  cfc_map_smul a r f

lemma cfc_map_star (f : R → R) : cfc a (fun x ↦ star (f x)) = star (cfc a f) := by
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · obtain ⟨ha, hf⟩ := h
    rw [cfc_apply a f, ← map_star, cfc_apply a _]
    congr
  · classical
    obtain (ha | hf) := Decidable.not_and_iff_or_not _ _ |>.mp h
    · simp [cfc_apply_of_not a ha]
    · rw [cfc_apply_of_not' a hf, cfc_apply_of_not', star_zero]
      exact fun hf_star ↦ hf <| by simpa using hf_star.star

lemma cfc_pow (n : ℕ) (ha : p a := by cfc_tac) : cfc a (· ^ n : R → R) = a ^ n := by
  nth_rw 2 [← cfcSpec_map_id (show p a from ha) (R := R)]
  rw [cfc_apply a (· ^ n), ← map_pow]
  congr

lemma cfc_smul {S : Type*} [SMul S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R → R)]
    (s : S) (ha : p a := by cfc_tac) : cfc a (s • · : R → R) = s • a := by
  have := cfc_id R a ▸ cfc_map_smul a s id
  exact this

lemma cfc_const_mul (r : R) (ha : p a := by cfc_tac) : cfc a (r * ·) = r • a :=
  cfc_smul a r

lemma cfc_star (ha : p a := by cfc_tac) : cfc a (star · : R → R) = star a := by
  nth_rw 2 [← cfcSpec_map_id (show p a from ha) (R := R)]
  rw [← map_star, cfc_apply a (star : R → R)]
  congr

section Polynomial
open Polynomial

lemma cfc_eval_X (ha : p a := by cfc_tac) :
    cfc a (X : R[X]).eval = a := by
  simpa using cfc_id R a

lemma cfc_eval_C (r : R) (ha : p a := by cfc_tac) :
    cfc a (C r).eval = algebraMap R A r := by
  simp [cfc_map_const a r]

attribute [fun_prop]
  Polynomial.continuous
  Polynomial.continuousOn
  Polynomial.continuousAt

@[fun_prop]
theorem Continuous.comp_continuousOn'
    {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] {g : β → γ}
    {f : α → β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) :
    ContinuousOn (fun x ↦ g (f x)) s :=
  hg.comp_continuousOn hf

-- can we get a better proof of this by using the underlying `StarAlgHom`?
lemma cfc_map_polynomial (q : R[X]) (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc a (fun x ↦ q.eval (f x)) = aeval (cfc a f) q := by
  have : ContinuousOn f (spectrum R a) := hf -- hack
  induction q using Polynomial.induction_on with
  | h_C r => simp [cfc_map_const a r]
  | h_add q₁ q₂ hq₁ hq₂ =>
    simp only [eval_add, map_add, ← hq₁, ← hq₂, cfc_map_add a (q₁.eval <| f ·) (q₂.eval <| f ·)]
  | h_monomial n r _ =>
    simp only [eval_mul, eval_C, eval_pow, eval_X, map_mul, aeval_C, map_pow, aeval_X]
    rw [cfc_map_const_mul .., cfc_map_pow _ _ _ n.succ_ne_zero,
      ← smul_eq_mul, algebraMap_smul]

lemma cfc_polynomial (q : R[X]) (ha : p a := by cfc_tac) :
    cfc a q.eval = aeval a q := by
  rw [cfc_map_polynomial a q (fun x : R ↦ x)]
  congr
  exact cfc_id R a

end Polynomial

variable [∀ a : A, Subsingleton (CFCCore (spectrum R a) a)]

lemma cfc_comp' (g f : R → R) (ha : p a := by cfc_tac)
    (hg : ContinuousOn g (f '' spectrum R a) := by cfc_cont_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc a (g ∘ f) = cfc (cfc a f) g := by
  have := hg.comp hf <| (spectrum R a).mapsTo_image f
  have sp_eq : spectrum R (cfcSpec (show p a from ha) (ContinuousMap.mk _ hf.restrict)) =
      f '' (spectrum R a) := by
    rw [cfcSpec_map_spectrum (by exact ha) _]
    ext
    simp
  rw [cfc_apply .., cfc_apply a f]
  rw [cfc_apply _ _ (cfcSpec_predicate (show p a from ha) _) (by convert hg)]
  rw [← cfcSpec_comp _ _]
  swap
  · exact ContinuousMap.mk _ <| hf.restrict.codRestrict fun x ↦ by rw [sp_eq]; use x.1; simp
  · congr
  · exact fun _ ↦ rfl

lemma cfc_comp (g f : R → R) (ha : p a := by cfc_tac)
    (hg : ContinuousOn g (f '' spectrum R a) := by cfc_cont_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc a (g <| f ·) = cfc (cfc a f) g :=
  cfc_comp' a g f

lemma cfc_comp_pow (n : ℕ) (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f ((· ^ n) '' (spectrum R a)) := by cfc_cont_tac) :
    cfc a (f <| · ^ n) = cfc (a ^ n) f := by
  rw [cfc_comp a f (· ^ n), cfc_pow a n]

lemma cfc_comp_smul {S : Type*} [SMul S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R → R)]
    (s : S) (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f ((s • ·) '' (spectrum R a)) := by cfc_cont_tac) :
    cfc a (f <| s • ·) = cfc (s • a) f := by
  rw [cfc_comp a f (s • ·), cfc_smul a s]

lemma cfc_comp_const_mul (r : R) (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f ((r * ·) '' (spectrum R a)) := by cfc_cont_tac) :
    cfc a (f <| r * ·) = cfc (r • a) f := by
  rw [cfc_comp a f (r * ·), cfc_const_mul a r]

lemma cfc_comp_star (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (star '' (spectrum R a)) := by cfc_cont_tac) :
    cfc a (f <| star ·) = cfc (star a) f := by
  rw [cfc_comp a f star, cfc_star a]

open Polynomial in
lemma cfc_comp_polynomial (q : R[X]) (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (q.eval '' (spectrum R a)) := by cfc_cont_tac) :
    cfc a (f <| q.eval ·) = cfc (aeval a q) f := by
  rw [cfc_comp a f q.eval, cfc_polynomial a]

lemma eq_algebraMap_of_spectrum_singleton (r : R) (h_spec : spectrum R a = {r})
    (ha : p a := by cfc_tac) : a = algebraMap R A r := by
  simpa [cfc_id R a, cfc_map_const a r] using
    cfc_congr a (f := id) (g := fun _ : R ↦ r) <| by rw [h_spec]; simp

lemma eq_zero_of_spectrum_eq_zero (h_spec : spectrum R a = {0}) (ha : p a := by cfc_tac) :
    a = 0 := by
  simpa using eq_algebraMap_of_spectrum_singleton a 0 h_spec

lemma eq_one_of_spectrum_eq_one (h_spec : spectrum R a = {1}) (ha : p a := by cfc_tac) :
    a = 1 := by
  simpa using eq_algebraMap_of_spectrum_singleton a 1 h_spec

end Bare


end Basic

section Inv

variable {R A : Type*} {p : A → Prop} [Semifield R] [StarRing R] [MetricSpace R]
variable [TopologicalSemiring R] [ContinuousStar R] [HasContinuousInv₀ R] [TopologicalSpace A]
variable [Ring A] [StarRing A] [Algebra R A] [ContinuousFunctionalCalculus R p]

lemma cfc_isUnit_iff (a : A) (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    IsUnit (cfc a f) ↔ ∀ x ∈ spectrum R a, f x ≠ 0 := by
  rw [← spectrum.zero_not_mem_iff R, cfc_map_spectrum ..]
  aesop

alias ⟨_, cfc_isUnit⟩ := cfc_isUnit_iff

@[simps]
noncomputable def cfc_units (a : A) (f : R → R) (hf' : ∀ x ∈ spectrum R a, f x ≠ 0)
    (ha : p a := by cfc_tac) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) : Aˣ where
  val := cfc a f
  inv := cfc a (fun x ↦ (f x)⁻¹)
  val_inv := by
    have : ContinuousOn f (spectrum R a) := hf -- hack
    rw [← cfc_map_mul .., ← cfc_map_one R a]
    exact cfc_congr a fun _ _ ↦ by aesop
  inv_val := by
    have : ContinuousOn f (spectrum R a) := hf -- hack
    rw [← cfc_map_mul .., ← cfc_map_one R a]
    exact cfc_congr a fun _ _ ↦ by aesop

lemma cfc_units_pow (a : A) (f : R → R) (hf' : ∀ x ∈ spectrum R a, f x ≠ 0) (n : ℕ)
    (ha : p a := by cfc_tac) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    (cfc_units a f hf') ^ n =
      cfc_units (forall₂_imp (fun _ _ ↦ pow_ne_zero n) hf') (hf := hf.pow n) := by
  ext
  cases n with
  | zero => simp [cfc_map_one' R a]
  | succ n => simp [cfc_map_pow a f _ n.succ_ne_zero]

lemma cfc_map_inv (a : A) (f : R → R) (hf' : ∀ x ∈ spectrum R a, f x ≠ 0)
    (ha : p a := by cfc_tac) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc a (fun x ↦ (f x) ⁻¹) = Ring.inverse (cfc a f) := by
  rw [← val_inv_cfc_units a f hf', ← val_cfc_units a f hf', Ring.inverse_unit]

lemma cfc_inv (a : Aˣ) (ha : p a := by cfc_tac) :
    cfc (a : A) (fun x ↦ x⁻¹ : R → R) = a⁻¹ := by
  rw [← Ring.inverse_unit]
  convert cfc_map_inv (a : A) (id : R → R) ?_
  · exact (cfc_id R (a : A)).symm
  · rintro x hx rfl
    exact spectrum.zero_not_mem R a.isUnit hx

lemma cfc_map_div (a : A) (f g : R → R) (hg' : ∀ x ∈ spectrum R a, g x ≠ 0)
    (ha : p a := by cfc_tac) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) :
    cfc a (fun x ↦ f x / g x) = cfc a f * Ring.inverse (cfc a g) := by
  simp only [div_eq_mul_inv]
  have : ContinuousOn g (spectrum R a) := hg -- hack
  rw [cfc_map_mul .., cfc_map_inv a g hg']

variable [∀ a : A, Subsingleton (CFCCore (spectrum R a) a)]

@[fun_prop]
lemma Units.continuousOn_inv₀_spectrum (a : Aˣ) : ContinuousOn (· ⁻¹) (spectrum R (a : A)) :=
  continuousOn_inv₀.mono <| by
    simpa only [Set.subset_compl_singleton_iff] using spectrum.zero_not_mem R a.isUnit

@[fun_prop]
lemma Units.continuousOn_zpow₀_spectrum (a : Aˣ) (n : ℤ) :
    ContinuousOn (· ^ n) (spectrum R (a : A)) :=
  (continuousOn_zpow₀ n).mono <| by
    simpa only [Set.subset_compl_singleton_iff] using spectrum.zero_not_mem R a.isUnit

lemma cfc_comp_inv (a : Aˣ) (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f ((· ⁻¹) '' (spectrum R (a : A))) := by cfc_cont_tac) :
    cfc (a : A) (fun x ↦ f x⁻¹) = cfc (↑a⁻¹ : A) f := by
  rw [cfc_comp .., cfc_inv _]  -- cool!
  -- more info: `rw [cfc_comp (a : A) f (· ⁻¹), cfc_inv a]`

lemma cfc_units_zpow (a : A) (f : R → R) (hf' : ∀ x ∈ spectrum R a, f x ≠ 0) (n : ℤ)
    (ha : p a := by cfc_tac) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    (cfc_units a f hf') ^ n =
      cfc_units a (f ^ n) (forall₂_imp (fun _ _ ↦ zpow_ne_zero n) hf')
        (by cfc_tac) (hf.zpow₀ n (forall₂_imp (fun _ _ ↦ Or.inl) hf')) := by
  cases n with
  | ofNat _ => simpa using cfc_units_pow a f hf' _
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow]
    ext
    exact cfc_map_pow (hf := hf.inv₀ hf') _ n.succ_ne_zero |>.symm

lemma cfc_zpow (a : Aˣ) (n : ℤ) (ha : p a := by cfc_tac) :
    cfc (a : A) (fun x : R ↦ x ^ n) = ↑(a ^ n) := by
  cases n with
  | ofNat n => simpa using cfc_pow (a : A) n
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    have := cfc_map_pow (a : A) (fun x ↦ x⁻¹ : R → R) (n + 1) n.succ_ne_zero
    exact this.trans <| congr($(cfc_inv a) ^ (n + 1))

lemma cfc_comp_zpow (a : Aˣ) (f : R → R) (n : ℤ) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f ((· ^ n) '' (spectrum R (a : A))) := by cfc_cont_tac) :
    cfc (a : A) (fun x ↦ f (x ^ n)) = cfc (↑(a ^ n) : A) f := by
  rw [cfc_comp .., cfc_zpow a]
  -- more info: `rw [cfc_comp (a : A) f (· ^ n), cfc_inv a]`

end Inv

section Neg

variable {R A : Type*} {p : A → Prop} [CommRing R] [StarRing R] [MetricSpace R]
variable [TopologicalRing R] [ContinuousStar R] [TopologicalSpace A]
variable [Ring A] [StarRing A] [Algebra R A] [ContinuousFunctionalCalculus R p]

lemma cfc_map_sub (a : A) (f g : R → R)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) :
    cfc a (fun x ↦ f x - g x) = cfc a f - cfc a g := by
  have : ContinuousOn f (spectrum R a) := hf -- hack
  have : ContinuousOn g (spectrum R a) := hg -- hack
  by_cases ha : p a
  · rw [cfc_apply a f, cfc_apply a g, ← map_sub, cfc_apply ..]
    congr
  · simp [cfc_apply_of_not a ha]

lemma cfc_map_neg (a : A) (f : R → R) : cfc a (fun x ↦ - (f x)) = - (cfc a f) := by
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · obtain ⟨ha, hf⟩ := h
    rw [cfc_apply a f, ← map_neg, cfc_apply ..]
    congr
  · classical
    obtain (ha | hf) := Decidable.not_and_iff_or_not _ _ |>.mp h
    · simp [cfc_apply_of_not a ha]
    · rw [cfc_apply_of_not' a hf, cfc_apply_of_not', neg_zero]
      exact fun hf_neg ↦ hf <| by simpa using hf_neg.neg

lemma cfc_neg (a : A) (ha : p a := by cfc_tac) :
    cfc (a : A) (- · : R → R) = -a := by
  have := cfc_id R a ▸ cfc_map_neg a (id : R → R)
  exact this

variable [∀ a : A, Subsingleton (CFCCore (spectrum R a) a)]

lemma cfc_comp_neg (a : A) (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f ((- ·) '' (spectrum R (a : A))) := by cfc_cont_tac) :
    cfc (a : A) (f <| - ·) = cfc (-a) f := by
  rw [cfc_comp .., cfc_neg _]

end Neg

/- maybe we actually don't need this?
section cfc

section Basic

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
variable [TopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
variable [Algebra R A] [CFC R p] [StarModule R A] (a : A)

/- In practice, we expec this to be the most useful version of the continuous functional calculus.
It is also uniquely determined (by appealing to the Stone-Weierstrass and the Tietze extension
theorems), although I haven't proven that here. -/

/-- The star algebra homomorphism underlying a instance of the continuous functional calculus.
Version for continuous functions on the full space. -/
noncomputable irreducible_def cfc : C(R, R) →⋆ₐ[R] A := by
  classical
  exact if ha : p a
    then (cfcSpec ha).comp <| (ContinuousMap.id R |>.restrict <| spectrum R a).compStarAlgHom' R R
    else (StarAlgHom.ofId R A).comp (ContinuousMap.evalStarAlgHom 0)

lemma cfc_dif_pos (ha : p a := by cfc_tac) :
    cfc a = (cfcSpec (show p a from ha)).comp
      ((ContinuousMap.id R |>.restrict <| spectrum R a).compStarAlgHom' R R) := by
  rw [cfc_def, dif_pos ha]

lemma cfc_dif_neg (ha : ¬ p a) :
    cfc a = (StarAlgHom.ofId R A).comp (ContinuousMap.evalStarAlgHom 0) := by
  rw [cfc_def, dif_neg ha]

lemma cfc_apply (f : C(R, R)) (ha : p a := by cfc_tac) :
    cfc a f = cfcSpec (show p a from ha) (f.restrict <| spectrum R a) := by
  rw [cfc_dif_pos a, StarAlgHom.comp_apply, ContinuousMap.compStarAlgHom'_apply]
  congr

lemma cfc_eq_cfc (a : A) (f : C(R, R)) (ha : p a := by cfc_tac)  :
    cfc a f = cfc a f := by
  rw [cfc_apply _, cfc_apply ..]
  congr

lemma cfc_id (ha : p a := by cfc_tac) : cfc a (.id R) = a := by
  rw [cfc_apply a, cfcSpec_map_id (show p a from ha)]

/-- The **spectral mapping theorem** for the continuous functional calculus. -/
lemma cfc_map_spectrum (f : C(R, R)) (ha : p a := by cfc_tac) :
    spectrum R (cfc a f) = f '' spectrum R a := by
  rw [cfc_apply a, cfcSpec_map_spectrum]
  simp [Set.range_comp]

@[aesop safe apply]
lemma cfc_predicate (f : C(R, R)) (ha : p a := by cfc_tac) : p (cfc a f) := by
  rw [cfc_apply a]
  exact cfcSpec_predicate (p := p) ha _

lemma cfc_continuous [TopologicalSemiring A] [ContinuousSMul R A] :
    Continuous (cfc a (R := R)) := by
  by_cases ha : p a
  · rw [cfc_dif_pos a]
    exact cfcSpec_closedEmbedding ha |>.continuous |>.comp <| ContinuousMap.continuous_comp_left _
  · rw [cfc_dif_neg a ha]
    exact continuous_algebraMap R A |>.comp <| ContinuousMap.continuous_eval_const _

-- MOVE ME
attribute [fun_prop] map_continuous

lemma cfc_congr {f g : C(R, R)} (hfg : (spectrum R a).EqOn f g) (ha : p a := by cfc_tac) :
    cfc a f = cfc a g := by
  simpa [cfc_eq_cfc a] using cfc_congr a hfg

lemma cfc_eqOn_of_eq {f g : C(R, R)} (hfg : cfc a f = cfc a g) (ha : p a := by cfc_tac) :
    (spectrum R a).EqOn f g :=
  cfc_eqOn_of_eq a <| by simpa [cfc_eq_cfc a] using hfg

lemma cfc_pow (n : ℕ) (ha : p a := by cfc_tac) : cfc a (.id R ^ n) = a ^ n := by
  rw [map_pow, cfc_id a]

lemma cfc_star (ha : p a := by cfc_tac)  : cfc a (star (.id R)) = star a := by
  rw [map_star, cfc_id a]

lemma cfc_smul {S : Type*} [SMul S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R C(R, R)]
    (s : S) (a : A) (ha : p a := by cfc_tac) : cfc a (s • .id R) = s • a := by
  rw [← smul_one_smul R s (ContinuousMap.id R), map_smul, cfc_id a, ← smul_one_smul R s a]

-- inv, zpow, neg

variable [∀ a : A, Subsingleton (CFCCore (spectrum R a) a)]

lemma cfc_comp (f g : C(R, R)) (ha : p a := by cfc_tac) : cfc a (g.comp f) = cfc (cfc a f) g := by
  have := cfc_predicate a f
  simp_rw [cfc_eq_cfc .., cfc_eq_cfc a, ContinuousMap.coe_comp]
  exact cfc_comp a g f

lemma cfc_comp_pow (n : ℕ) (f : C(R, R)) (ha : p a := by cfc_tac)  :
    cfc a (f.comp (.id R ^ n)) = cfc (a ^ n) f := by
  rw [cfc_comp _, cfc_pow _]

lemma cfc_comp_star (f : C(R, R)) (ha : p a := by cfc_tac) :
    cfc a (f.comp (star (.id R))) = cfc (star a) f := by
  rw [cfc_comp _, cfc_star _]

lemma cfc_comp_smul (r : R) (a : A) (f : C(R, R)) (ha : p a := by cfc_tac) :
    cfc a (f.comp (r • .id R)) = cfc (r • a) f := by
  rw [cfc_comp _, cfc_smul ..]

end Basic

section Neg

variable {R A : Type*} {p : A → Prop} [CommRing R] [StarRing R] [MetricSpace R]
variable [TopologicalRing R] [ContinuousStar R] [TopologicalSpace A]
variable [Ring A] [StarRing A] [Algebra R A] [CFC R p] [StarModule R A]

lemma cfc_neg (a : A) (ha : p a := by cfc_tac) : cfc a (- (.id R)) = -a := by
  rw [map_neg, cfc_id a]

variable [∀ a : A, Subsingleton (CFCCore (spectrum R a) a)]

lemma cfc_comp_neg (a : A) (f : C(R, R)) (ha : p a := by cfc_tac) :
    cfc a (f.comp (- (.id R))) = cfc (-a) f := by
  rw [cfc_comp a, cfc_neg a]

end Neg
-- spectrum subset circle → unitary

end cfc
-/

section Restrict

variable {R S A : Type*} {p q : A → Prop}
variable [CommSemiring R] [StarRing R] [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R]
variable [CommSemiring S] [StarRing S] [MetricSpace S] [TopologicalSemiring S] [ContinuousStar S]
variable [TopologicalSpace A] [Ring A] [StarRing A] [Algebra S A] [ContinuousFunctionalCalculus S q]
variable [Algebra R S] [Algebra R A] [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S]

-- we should be able to get rid of the compactness and isometry conditions below in favor of
-- something weaker, but they hold in the situations we care about, so we leave them for now.
@[reducible]
def cfc_of_spectrumRestricts [CompleteSpace R]
    (f : C(S, R)) (h_isom : Isometry (algebraMap R S)) (h : ∀ a, p a ↔ q a ∧ SpectrumRestricts a f)
    (h_cpct : ∀ a, q a → CompactSpace (spectrum S a)) :
    ContinuousFunctionalCalculus R p where
  toStarAlgHom {a} ha := ((h a).mp ha).2.starAlgHom (cfcSpec ((h a).mp ha).1 (R := S)) f
  hom_closedEmbedding {a} ha := by
    apply ClosedEmbedding.comp (cfcSpec_closedEmbedding ((h a).mp ha).1)
    simp only [RingHom.coe_coe, StarAlgHom.coe_toAlgHom, StarAlgHom.comp_apply,
      ContinuousMap.compStarAlgHom'_apply, ContinuousMap.compStarAlgHom_apply]
    have : CompactSpace (spectrum S a) := h_cpct a ((h a).mp ha).1
    have : CompactSpace (spectrum R a) := ((h a).mp ha).2.compactSpace
    refine Isometry.closedEmbedding ?_
    simp only [isometry_iff_dist_eq]
    refine fun g₁ g₂ ↦ le_antisymm ?_ ?_
    all_goals refine (ContinuousMap.dist_le dist_nonneg).mpr fun x ↦ ?_
    · simpa [h_isom.dist_eq] using ContinuousMap.dist_apply_le_dist _
    · obtain ⟨y, y_mem, hy⟩ : (x : R) ∈ f '' spectrum S a := ((h a).mp ha).2.image.symm ▸ x.2
      lift y to spectrum S a using y_mem
      refine le_of_eq_of_le ?_ <| ContinuousMap.dist_apply_le_dist y
      simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, StarAlgHom.ofId_apply]
      rw [h_isom.dist_eq]
      congr <;> exact Subtype.ext hy.symm
  hom_id {a} ha := by
    simp only [SpectrumRestricts.starAlgHom_apply]
    convert cfcSpec_map_id ((h a).mp ha).1
    ext x
    exact ((h a).mp ha).2.rightInvOn x.2
  hom_map_spectrum {a} ha g := by
    rw [SpectrumRestricts.starAlgHom_apply]
    simp only [← @spectrum.preimage_algebraMap (R := R) S, cfcSpec_map_spectrum]
    ext x
    constructor
    · rintro ⟨y, hy⟩
      have := congr_arg f hy
      simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, StarAlgHom.ofId_apply] at this
      rw [((h a).mp ha).2.left_inv _, ((h a).mp ha).2.left_inv _] at this
      exact ⟨_, this⟩
    · rintro ⟨y, rfl⟩
      rw [Set.mem_preimage]
      refine' ⟨⟨algebraMap R S y, spectrum.algebraMap_mem S y.prop⟩, _⟩
      simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, StarAlgHom.ofId_apply]
      congr
      exact Subtype.ext (((h a).mp ha).2.left_inv y)
  predicate_hom {a} ha g := by
    rw [h]
    refine ⟨cfcSpec_predicate _ _, ?_⟩
    refine { rightInvOn := fun s hs ↦ ?_, left_inv := ((h a).mp ha).2.left_inv }
    rw [SpectrumRestricts.starAlgHom_apply, cfcSpec_map_spectrum] at hs
    obtain ⟨r, rfl⟩ := hs
    simp [((h a).mp ha).2.left_inv _]


end Restrict
