/-
Copyright (c) 2023 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
import Mathlib.RingTheory.Noetherian
import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Module.GradeZeroModule
import Mathlib.GroupTheory.Subgroup.Pointwise
import Mathlib.GroupTheory.Finiteness
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Finsupp.Pointwise

/-!
# The properties of a graded Noetherian ring.

This file proves some properties of a graded Noetherian ring:
1. The 0-th grade of a Noetherian ring is also a Noetherian ring.
2. For a Noetherian ring `A` which is internally graded by `𝒜`,
   `⨁_{i>0} 𝒜ᵢ` is finitely generated as an ideal of `A`.
-/


namespace GradedRing

section Ring

variable {ι A σ : Type*}
variable [Ring A] [IsNoetherianRing A]
variable [DecidableEq ι] [CanonicallyOrderedAddCommMonoid ι]
variable [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜]


/--
If the internally graded ring `A` is Noetherian, then `𝒜 0` is a Noetherian ring.
-/
instance GradeZero.subring_isNoetherianRing_of_isNoetherianRing : IsNoetherianRing (𝒜 0) :=
  isNoetherianRing_of_surjective A (𝒜 0) (GradedRing.projZeroRingHom' 𝒜)
  (GradedRing.projZeroRingHom'_surjective 𝒜)

end Ring

section CommRing

variable {A M : Type*}
variable [CommRing A] [AddCommGroup M] [Module A M]
variable [finite_module : Module.Finite A M] [noetherian_ring : IsNoetherianRing A]
variable (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
variable (ℳ : ℕ → AddSubgroup M) [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]

instance : Algebra (𝒜 0) A := Algebra.ofSubring (SetLike.GradeZero.subring 𝒜)

open BigOperators Pointwise SetLike

namespace finite_algebra_over_degree_zero_subring

noncomputable def generating_set : Finset A :=
  (Ideal.fg_iff_homogeneously_fg _  |>.mp <|
    isNoetherianRing_iff_ideal_fg A |>.mp inferInstance
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal).choose

lemma homogeneous_of_mem_generating_set (a : A) (ha : a ∈ generating_set 𝒜) : Homogeneous 𝒜 a :=
  (Ideal.fg_iff_homogeneously_fg _  |>.mp <|
    isNoetherianRing_iff_ideal_fg A |>.mp inferInstance
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal).choose_spec.1 a ha

lemma irrelevant_eq_span_generating_set :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal = Ideal.span (generating_set 𝒜) :=
  (Ideal.fg_iff_homogeneously_fg _  |>.mp <|
    isNoetherianRing_iff_ideal_fg A |>.mp inferInstance
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal).choose_spec.2

lemma algebra_eq_join : (⊤ : Subalgebra (𝒜 0) A) = Algebra.adjoin (𝒜 0) (generating_set 𝒜) := by
  classical
  let S : Finset A := generating_set 𝒜
  let hS1 := homogeneous_of_mem_generating_set 𝒜
  let hS2 := irrelevant_eq_span_generating_set 𝒜
  choose deg h_deg1 using hS1
  have h_deg0 (a : A) (h1 : a ∈ S) (h2 : a ≠ 0) : 0 < deg a h1
  · by_contra! rid
    simp only [nonpos_iff_eq_zero] at rid
    have m : a ∈ Ideal.span S := Ideal.subset_span h1
    specialize h_deg1 a h1
    rw [rid] at h_deg1
    erw [← hS2, HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      DirectSum.decompose_of_mem_same (hx := h_deg1)] at m
    exact h2 m

  suffices subset (m : ℕ) : (𝒜 m : Set A) ⊆ (Algebra.adjoin (𝒜 0) (S : Set A))
  · refine le_antisymm (fun a _ ↦ ?_) le_top
    rw [← DirectSum.sum_support_decompose 𝒜 a]
    exact Subalgebra.sum_mem _ fun j _ ↦ subset j <| Subtype.mem _

  suffices (n : ℕ) :
    𝒜 n.succ = ⨆ (s : {s : S | deg s.1 s.2 ≤ n + 1 }), (s : A) • 𝒜 (n.succ - deg _ s.1.2)
  · cases m with | zero => ?_ | succ m => ?_
    · simp only [Nat.zero_eq]
      intro x hx
      show _ ∈ Subsemiring.closure (_ ∪ _)
      rw [Subsemiring.closure_union (Set.range <| algebraMap (𝒜 0) A) S]
      exact @le_sup_left (Subsemiring A) _ (Subsemiring.closure _) (Subsemiring.closure _) _ <|
        Subsemiring.subset_closure ⟨⟨_, hx⟩, rfl⟩
    induction' m using Nat.strong_induction_on with m ih
    rw [this]
    intro x hx
    simp only [SetLike.mem_coe] at hx ⊢
    refine AddSubgroup.iSup_induction (C := fun y ↦ y ∈ Algebra.adjoin (𝒜 0) (S : Set A))
      (fun (s : {s : S | deg s.1 s.2 ≤ m + 1 }) ↦ (s : A) • 𝒜 (m.succ - deg _ s.1.2)) hx ?_ ?_ ?_
    · rintro ⟨⟨x, hx1⟩, (hx2 : deg _ _ ≤ _)⟩ y hy1
      simp only at hy1
      rw [AddSubgroup.mem_smul_pointwise_iff_exists] at hy1
      obtain ⟨y, hy1, rfl⟩ := hy1
      by_cases ineq1 : x = 0
      · rw [ineq1, zero_smul]; exact Subalgebra.zero_mem _

      by_cases ineq0 : m < deg x hx1
      · have eq0 : m.succ - deg x hx1 = 0
        · simp only [tsub_eq_zero_iff_le]
          exact ineq0
        rw [eq0] at hy1
        refine Subalgebra.mul_mem _ (show _ ∈ Subsemiring.closure (_ ∪ _) from ?_)
          (show _ ∈ Subsemiring.closure (_ ∪ _) from ?_) <;>
        rw [Subsemiring.closure_union (Set.range <| algebraMap (𝒜 0) A) S]
        · exact @le_sup_right (Subsemiring A) _ (Subsemiring.closure _) (Subsemiring.closure _) _ <|
            Subsemiring.subset_closure hx1
        · exact @le_sup_left (Subsemiring A) _ (Subsemiring.closure _) (Subsemiring.closure _) _ <|
            Subsemiring.subset_closure ⟨⟨_, hy1⟩, rfl⟩
      simp only [not_lt] at ineq0
      specialize ih (m - deg _ hx1) (Nat.sub_lt_self (h_deg0 _ hx1 ineq1) ineq0) <|
        show y ∈ _ by
          simp only [SetLike.mem_coe]
          convert hy1 using 2
          rw [Nat.succ_sub]
          exact ineq0
      refine Subalgebra.mul_mem _ (show _ ∈ Subsemiring.closure (_ ∪ _) from ?_) ih
      rw [Subsemiring.closure_union (Set.range <| algebraMap (𝒜 0) A) S]
      exact @le_sup_right (Subsemiring A) _ (Subsemiring.closure _) (Subsemiring.closure _) _ <|
        Subsemiring.subset_closure hx1

    · exact Subalgebra.zero_mem _
    · intros _ _ h1 h2
      exact Subalgebra.add_mem _ h1 h2

  ext x; constructor
  · intro hx
    have m : x ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal
    · erw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne (hx := hx)]
      norm_num
    erw [hS2, mem_span_set] at m
    obtain ⟨f, hf, (eq0 : ∑ i in f.support, f i * i = x)⟩ := m
    replace eq0 :=
      calc x
        = (DirectSum.decompose 𝒜 x (n + 1) : A) :=
          by simp only [DirectSum.of_eq_same, DirectSum.decompose_of_mem 𝒜 hx]
      _ = DirectSum.decompose 𝒜 (∑ a in f.support, f a * a) (n + 1) := by rw [eq0]
      _ = ∑ a in f.support, (DirectSum.decompose 𝒜 (f a * a) (n + 1) : A) :=
          by change GradedRing.proj 𝒜 (n + 1) (∑ a in f.support, f a * a : A) = _
             rw [map_sum]
             rfl
      _ = ∑ a in f.support.attach, (DirectSum.decompose 𝒜 (f a * a) (n + 1) : A) :=
          Finset.sum_attach _ _ |>.symm
      _ = ∑ a in f.support.attach,
            if deg a (hf a.2) ≤ n + 1
            then (DirectSum.decompose 𝒜 (f a) ((n + 1) - deg a (hf a.2)) * a : A)
            else 0 := Finset.sum_congr rfl fun a _ ↦
          DirectSum.coe_decompose_mul_of_right_mem 𝒜 (n + 1) (h_deg1 a (hf a.2)) (a := f a)

    rw [eq0]
    refine AddSubgroup.sum_mem _ fun a _ ↦ ?_

    split_ifs with h
    · refine AddSubgroup.mem_iSup_of_mem ⟨⟨a, hf a.2⟩, h⟩ ?_
      rw [AddSubgroup.mem_smul_pointwise_iff_exists]
      exact ⟨DirectSum.decompose 𝒜 (f a) ((n + 1) - deg a (hf a.2)), SetLike.coe_mem _,
        by rw [mul_comm]; rfl⟩
    · exact AddSubgroup.zero_mem _
  · intro hx
    refine AddSubgroup.iSup_induction (C := fun y ↦ y ∈ 𝒜 n.succ)
      (fun (s : {s : S | deg s.1 s.2 ≤ n + 1 }) ↦ (s : A) • 𝒜 (n.succ - deg _ s.1.2)) hx ?_ ?_ ?_
    · rintro ⟨⟨x, hx1⟩, (hx2 : deg _ _ ≤ _)⟩ z hz1
      simp only at hz1
      rw [AddSubgroup.mem_smul_pointwise_iff_exists] at hz1
      obtain ⟨z, hz1, rfl⟩ := hz1
      specialize h_deg1 _ hx1
      convert SetLike.mul_mem_graded h_deg1 hz1 using 2
      rw [← Nat.add_sub_assoc, add_comm, Nat.add_sub_cancel]
      exact hx2
    · exact AddSubgroup.zero_mem _
    · intros _ _ h1 h2
      exact AddSubgroup.add_mem _ h1 h2

def eval_monomial (f : A →₀ ℕ) : A :=
  ∏ a in f.support, a ^ (f a)

def degree_monomial
  (f : A →₀ ℕ)
  (deg : ⦃a : A⦄ → (ha : a ∈ f.support) → ℕ) : ℕ :=
∑ i in f.support.attach, deg i.2 * f i

lemma eval_monomial_mem_aux {ι : Type*} (s : Finset ι)
    (deg : s → ℕ)
    (pow : s → ℕ)
    (f : s → A)
    (h_deg : ∀ i, f i ∈ 𝒜 (deg i)):
    ∏ i in s.attach, f i ^ (pow i) ∈ 𝒜 (∑ i in s.attach, deg i * pow i) := by
  classical
  induction' s using Finset.induction_on with a s h ih
  · simp only [Finset.attach_empty, Finset.prod_empty, Finset.sum_empty]
    exact (SetLike.GradeZero.subring 𝒜).one_mem
  · simp only [Finset.attach_insert]
    rw [Finset.prod_insert (by simpa), Finset.sum_insert (by simpa)]
    refine SetLike.mul_mem_graded ?_ ?_
    · rw [mul_comm, ← smul_eq_mul]
      refine SetLike.pow_mem_graded _ ?_
      exact h_deg ⟨a, by aesop⟩
    · simp only [Finset.mem_attach, Subtype.mk.injEq, forall_true_left, Subtype.forall, imp_self,
      implies_true, Finset.prod_image, Finset.sum_image]
      apply ih
      rintro ⟨i, hi⟩
      exact h_deg ⟨i, by aesop⟩

lemma eval_monomial_mem
    (f : A →₀ ℕ)
    (deg : ⦃a : A⦄ → (ha : a ∈ f.support) → ℕ)
    (h_deg :  ⦃a : A⦄ → (ha : a ∈ f.support) → a ∈ 𝒜 (deg ha)) :
    eval_monomial f ∈ 𝒜 (degree_monomial f deg) := by
  classical
  delta eval_monomial degree_monomial
  convert eval_monomial_mem_aux 𝒜 f.support
    (fun i ↦ deg i.2) (fun i ↦ f i) Subtype.val (fun ⟨i, hi⟩ ↦ h_deg hi)
  exact Finset.prod_attach _ _ |>.symm

lemma eval_monomial_homogeneous (f : A →₀ ℕ) (hf : f.support ⊆ generating_set 𝒜) :
    Homogeneous 𝒜 (eval_monomial f) := by
  let deg ⦃a : A⦄ (ha : a ∈ f.support) : ℕ :=
    (homogeneous_of_mem_generating_set 𝒜 _ <| hf ha).choose
  have h_deg1 ⦃a : A⦄ (ha : a ∈ f.support) : a ∈ 𝒜 (deg ha) :=
    (homogeneous_of_mem_generating_set 𝒜 _ <| hf ha).choose_spec
  exact ⟨degree_monomial _ deg, eval_monomial_mem (deg := deg) (h_deg := h_deg1)⟩

lemma top_eq_span_monomial :
    (⊤ : Submodule (𝒜 0) A) =
    Submodule.span (𝒜 0)
      {a | ∃ (f : A →₀ ℕ), f.support ⊆ generating_set 𝒜 ∧ a = eval_monomial f } := by
  classical
  refine le_antisymm ?_ le_top
  rintro x -
  have hx : x ∈ (⊤ : Subalgebra (𝒜 0) A) := ⟨⟩
  rw [algebra_eq_join] at hx
  refine Algebra.adjoin_induction hx ?_ ?_ ?_ ?_
  · intro x hx
    refine Submodule.subset_span ⟨Finsupp.single x 1,
      Finsupp.support_single_subset.trans (by simpa), ?_⟩
    · delta eval_monomial
      have eq1 : (Finsupp.single x 1).support = {x} :=
        le_antisymm Finsupp.support_single_subset (by simp)
      simp [eq1]
  · intro r
    change (r : A) ∈ Submodule.span (𝒜 0) _
    rw [show (r : A) = (r : A) • (1 : A) by rw [smul_eq_mul, mul_one]]
    exact Submodule.smul_mem _ _ <| Submodule.subset_span ⟨0, by simp, by simp [eval_monomial]⟩
  · intro a b ha hb
    exact Submodule.add_mem _ ha hb
  · intro a b ha hb
    apply Submodule.span_induction₂ ha hb
    · rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
      refine Submodule.subset_span ⟨(f + g : A →₀ ℕ), ?_, ?_⟩
      · exact Finsupp.support_add (g₁ := f) (g₂ := g) |>.trans <|
          sup_le (α := Finset A) hf hg
      · simp only [eval_monomial, Finsupp.coe_add, Pi.add_apply]
        rw [Finset.prod_subset (h := hf), Finset.prod_subset (h := hg),
          Finset.prod_subset (h := (_ : (f + g).support ⊆ generating_set 𝒜))]
        rotate_left
        · intro x _ hx2
          simp only [Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply, ne_eq, add_eq_zero,
            not_and, not_forall, not_not, exists_prop] at hx2
          rw [pow_add, hx2.1, hx2.2, pow_zero, one_mul]
        · exact Finsupp.support_add (g₁ := f) (g₂ := g) |>.trans <|
            sup_le (α := Finset A) hf hg
        · intro x _ hx2
          simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hx2
          rw [hx2, pow_zero]
        · intro x _ hx2
          simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hx2
          rw [hx2, pow_zero]

        simp_rw [pow_add]
        rw [Finset.prod_mul_distrib]
    · intro y
      rw [zero_mul]
      exact Submodule.zero_mem _
    · intro x
      rw [mul_zero]
      exact Submodule.zero_mem _
    · intro x₁ x₂ y hx₁ hx₂
      rw [add_mul]
      exact Submodule.add_mem _ hx₁ hx₂
    · intro x y₁ y₂ hy₁ hy₂
      rw [mul_add]
      exact Submodule.add_mem _ hy₁ hy₂
    · intro r x y h
      change ((r : A) * x) * y ∈ _
      rw [mul_assoc, ← smul_eq_mul]
      exact Submodule.smul_mem _ _ h
    · intro r x y h
      change x * ((r : A) * y) ∈ _
      rw [show x * (r * y) = r * (x * y) by ring, ← smul_eq_mul]
      exact Submodule.smul_mem _ _ h

end finite_algebra_over_degree_zero_subring

/--
If `A ≅ ⨁ᵢ, Aᵢ` is a noetherian graded ring, then `A` is a finite `A₀`-algebra.
-/
instance finite_algebra_over_degree_zero_subring : Algebra.FiniteType (𝒜 0) A := by
  constructor
  exact ⟨finite_algebra_over_degree_zero_subring.generating_set 𝒜,
    finite_algebra_over_degree_zero_subring.algebra_eq_join 𝒜 |>.symm⟩

lemma top_eq_adjoin_finitely_many_homogeneous_elements_over_degree_zero_subring  :
  ∃ (S : Finset A) (_ : ∀ s ∈ S, SetLike.Homogeneous 𝒜 s),
    (Algebra.adjoin (𝒜 0) (S : Set A) = ⊤) := by
  exact ⟨finite_algebra_over_degree_zero_subring.generating_set 𝒜,
    finite_algebra_over_degree_zero_subring.homogeneous_of_mem_generating_set 𝒜,
    finite_algebra_over_degree_zero_subring.algebra_eq_join 𝒜 |>.symm⟩

namespace finite_module_over_degree_zero_subring

variable (A) in
noncomputable def generatingSetModule : Finset M :=
  Submodule.fg_iff_homogeneously_fg (A := A) (ℳ := ℳ) (p := ⊤) |>.mp finite_module.out |>.choose

lemma homogeneous_of_mem_generatingSetModule (m : M) (hm : m ∈ generatingSetModule A ℳ) :
    Homogeneous ℳ m :=
  Submodule.fg_iff_homogeneously_fg (A := A) (ℳ := ℳ) (p := ⊤) |>.mp finite_module.out
  |>.choose_spec.1 m hm

lemma generatingSetModule_span :
    (⊤ : Submodule A M) = Submodule.span A (generatingSetModule A ℳ) :=
  Submodule.fg_iff_homogeneously_fg (A := A) (ℳ := ℳ) (p := ⊤) |>.mp finite_module.out
  |>.choose_spec.2


open finite_algebra_over_degree_zero_subring

variable {𝒜} in
noncomputable def degA : ⦃a : A⦄ → (ha : a ∈ generating_set 𝒜) → ℕ :=
  fun _ ha ↦ (homogeneous_of_mem_generating_set 𝒜 _ ha).choose

variable {𝒜} in
lemma h_degA : ⦃a : A⦄ → (ha : a ∈ generating_set 𝒜) → a ∈ 𝒜 (degA ha) :=
  fun _ ha ↦ (homogeneous_of_mem_generating_set 𝒜 _ ha).choose_spec

variable {ℳ} in
noncomputable def degM : (m : M) → m ∈ generatingSetModule A ℳ → ℕ :=
  fun m hm ↦ homogeneous_of_mem_generatingSetModule (A := A) ℳ m hm |>.choose

variable {ℳ} in
lemma h_degM : ∀ (m : M) (hm : m ∈ generatingSetModule A ℳ), m ∈ ℳ (degM m hm) :=
  fun m hm ↦ homogeneous_of_mem_generatingSetModule (A := A) ℳ m hm |>.choose_spec

lemma finite1 (k : ℕ) :
    {x : ℳ k |
      ∃ (ω : M) (_ : ω ∈ generatingSetModule A ℳ )
        (p : A →₀ ℕ) (hp1 : p.support ⊆ generating_set 𝒜),
      degree_monomial p (fun a ha ↦ degA (hp1 ha)) ≤ k ∧
      (x : M) = eval_monomial p • ω }.Finite := by
  sorry

set_option maxHeartbeats 400000 in
lemma kth_degree_eq_span (k : ℕ) :
    (⊤ : Submodule (𝒜 0) (ℳ k)) =
    Submodule.span (𝒜 0)
      {x : ℳ k |
        ∃ (ω : M) (_ : ω ∈ generatingSetModule A ℳ )
          (p : A →₀ ℕ) (hp1 : p.support ⊆ generating_set 𝒜),
        degree_monomial p (fun a ha ↦ degA (hp1 ha)) ≤ k ∧
        (x : M) = eval_monomial p • ω } := by
  refine le_antisymm ?_ le_top
  rintro ⟨x, hx⟩ -

  have mem1 : x ∈ (⊤ : Submodule A M) := ⟨⟩
  rw [generatingSetModule_span (A := A) ℳ, mem_span_set] at mem1

  obtain ⟨f, f_support_le, (eq0 : ∑ i in f.support, (f i) • i = x)⟩ := mem1

  have mem1 (a : A) : a ∈ (⊤ : Submodule (𝒜 0) A) := ⟨⟩
  simp_rw [top_eq_span_monomial 𝒜, mem_span_set] at mem1
  choose r hr1 hr2 using mem1
  change ∀ a, ∑ j in (r a).support, (r a) j • j = a at hr2
  replace hr1 (a : A) : ∀ j ∈ (r a).support, ∃ f, f.support ⊆ generating_set 𝒜 ∧ j = eval_monomial f
  · specialize hr1 a
    exact hr1
  choose p hp1 hp2 using hr1
  replace eq0 := calc
      x = ∑ i in f.support, (f i) • i := eq0.symm
      _ = ∑ i in f.support, (∑ j in (r (f i)).support, r (f i) j • j) • i :=
          Finset.sum_congr rfl fun x _ ↦ by
            congr 1
            rw [hr2 (f x)]
      _ = ∑ i in f.support, ∑ j in (r (f i)).support, (r (f i) j • j) • i :=
          Finset.sum_congr rfl fun x _ ↦ Finset.sum_smul
      _ = ∑ i in f.support, ∑ j in (r (f i)).support, (r (f i) j : A) • (j : A) • (i : M) :=
          Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ by
            change ((r (f x) y : A) * y) • _ = _
            rw [mul_smul]
      _ = ∑ i in f.support, ∑ j in (r (f i)).support.attach,
            (r (f i) j : A) • (j : A) • (i : M) :=
          Finset.sum_congr rfl fun _ _ ↦ Finset.sum_attach _ _ |>.symm
      _ = ∑ i in f.support, ∑ j in (r (f i)).support.attach,
            (r (f i) j : A) • (eval_monomial (p _ _ j.2) : A) • (i : M) :=
          Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
            congr 2
            exact hp2 _ _ j.2
  apply_fun GradedModule.proj ℳ k at eq0
  conv_lhs at eq0 => rw [GradedModule.proj_apply, DirectSum.decompose_of_mem_same _ hx]
  simp_rw [map_sum] at eq0
  replace eq0 := calc
    x = ∑ i in f.support, ∑ j in (r (f i)).support.attach,
          GradedModule.proj ℳ k ((r (f i) j : A) • (eval_monomial (p _ _ j.2) : A) • (i : M)) := eq0
    _ = ∑ i in f.support, ∑ j in (r (f i)).support.attach,
          GradedModule.proj ℳ k (((r (f i) j : A) * (eval_monomial (p _ _ j.2) : A)) • (i : M)) :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [mul_smul]
    _ = ∑ i in f.support.attach, ∑ j in (r (f i)).support.attach,
          GradedModule.proj ℳ k (((r (f i) j : A) * (eval_monomial (p _ _ j.2) : A)) • (i : M)) :=
        Finset.sum_attach _ _ |>.symm
    _ = ∑ i in f.support.attach, ∑ j in (r (f i)).support.attach,
          if degM (i : M) (f_support_le i.2) ≤ k
          then
            GradedRing.proj 𝒜 (k - degM (i : M) (f_support_le i.2))
              ((r (f i) j : A) * (eval_monomial (p _ _ j.2) : A)) • (i : M)
          else 0 :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
          rw [GradedModule.proj_smul_mem_right 𝒜 ℳ _ _ (h_degM (i : M) (f_support_le i.2))]
    _ = ∑ i in f.support.attach.filter fun i : f.support ↦ degM _ (f_support_le i.2) ≤ k,
        ∑ j in (r (f i)).support.attach,
          GradedRing.proj 𝒜 (k - degM _ (f_support_le i.2))
            ((r (f i) j : A) * (eval_monomial (p _ _ j.2) : A)) • (i : M) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        rintro ⟨i, hi⟩ -
        split_ifs with ineq1
        · rfl
        · rw [Finset.sum_const, smul_zero]
    _ = ∑ i in f.support.attach.filter fun i : f.support ↦ degM _ (f_support_le i.2) ≤ k,
        (∑ j in (r (f i)).support.attach,
          GradedRing.proj 𝒜 (k - degM _ (f_support_le i.2))
            ((r (f i) j : A) * (eval_monomial (p _ _ j.2) : A))) • (i : M) :=
        Finset.sum_congr rfl fun _ _ ↦ by rw [Finset.sum_smul]
    _ = ∑ i in f.support.attach.filter fun i : f.support ↦ degM _ (f_support_le i.2) ≤ k,
        (∑ j in (r (f i)).support.attach,
          if degree_monomial (p _ _ j.2) (fun a ha ↦ degA (hp1 _ _ j.2 ha)) ≤
              k - degM _ (f_support_le i.2)
          then
            GradedRing.proj 𝒜
              ((k - degM _ (f_support_le i.2)) -
                degree_monomial (p _ _ j.2) fun a ha ↦ degA (hp1 _ _ j.2 ha))
              (r (f i) j : A) * (eval_monomial (p _ _ j.2) : A)
          else 0) • (i : M) := by
        refine Finset.sum_congr rfl ?_
        rintro ⟨i, hi1⟩ _
        congr 1
        refine Finset.sum_congr rfl ?_
        rintro ⟨j, hj⟩ -
        rw [proj_apply, DirectSum.coe_decompose_mul_of_right_mem 𝒜]
        pick_goal 2
        · apply eval_monomial_mem 𝒜 (p _ _ hj) (fun a ha ↦ degA (hp1 _ _ hj ha))
          rintro a ha
          apply h_degA (hp1 _ _ hj ha)
        rfl
    _ = ∑ i in f.support.attach.filter fun i : f.support ↦ degM _ (f_support_le i.2) ≤ k,
        (∑ j in (r (f i)).support.attach.filter
          fun j : (r (f i)).support ↦
            degree_monomial (p _ _ j.2) (fun a ha ↦ degA (hp1 _ _ j.2 ha)) ≤
            k - degM _ (f_support_le i.2),
          GradedRing.proj 𝒜
              ((k - degM _ (f_support_le i.2)) -
                degree_monomial (p _ _ j.2) fun a ha ↦ degA (hp1 _ _ j.2 ha))
              (r (f i) j : A) * (eval_monomial (p _ _ j.2) : A)) • (i : M) :=
        Finset.sum_congr rfl fun _ _ ↦ by rw [Finset.sum_filter]
    _ = ∑ i in f.support.attach.filter fun i : f.support ↦ degM _ (f_support_le i.2) ≤ k,
        ∑ j in (r (f i)).support.attach.filter
          fun j : (r (f i)).support ↦
            degree_monomial (p _ _ j.2) (fun a ha ↦ degA (hp1 _ _ j.2 ha)) ≤
            k - degM _ (f_support_le i.2),
          (GradedRing.proj 𝒜
              ((k - degM _ (f_support_le i.2)) -
                degree_monomial (p _ _ j.2) fun a ha ↦ degA (hp1 _ _ j.2 ha))
              (r (f i) j : A) * (eval_monomial (p _ _ j.2) : A)) • (i : M) :=
        Finset.sum_congr rfl fun _ _ ↦ by rw [Finset.sum_smul]
    _ = ∑ i in f.support.attach.filter fun i : f.support ↦ degM _ (f_support_le i.2) ≤ k,
        ∑ j in (r (f i)).support.attach.filter
          fun j : (r (f i)).support ↦
            degree_monomial (p _ _ j.2) (fun a ha ↦ degA (hp1 _ _ j.2 ha)) ≤
            k - degM _ (f_support_le i.2),
          (GradedRing.proj 𝒜
              ((k - degM _ (f_support_le i.2)) -
                degree_monomial (p _ _ j.2) fun a ha ↦ degA (hp1 _ _ j.2 ha))
              (r (f i) j : A)) • (eval_monomial (p _ _ j.2) : A) • (i : M) :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by rw [mul_smul]
    _ = ∑ i in f.support.attach.filter fun i : f.support ↦ degM _ (f_support_le i.2) ≤ k,
        ∑ j in (r (f i)).support.attach.filter
          fun j : (r (f i)).support ↦
            degree_monomial (p _ _ j.2) (fun a ha ↦ degA (hp1 _ _ j.2 ha)) ≤
            k - degM _ (f_support_le i.2),
          (if degree_monomial (p _ _ j.2) (fun a ha ↦ degA (hp1 _ _ j.2 ha)) =
              k - degM _ (f_support_le i.2)
            then (r (f i) j : A)
            else 0) • (eval_monomial (p _ _ j.2) : A) • (i : M) :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j hj ↦ by
          congr 1
          split_ifs with ineq1
          · rw [ineq1, Nat.sub_self, proj_apply, DirectSum.decompose_of_mem_same]
            exact SetLike.coe_mem _
          · rw [proj_apply, DirectSum.decompose_of_mem_ne (hx := SetLike.coe_mem _)]
            intro rid
            rw [eq_comm, Nat.sub_eq_zero_iff_le] at rid
            rw [Finset.mem_filter] at hj
            exact ineq1 <| le_antisymm hj.2 rid
    _ = ∑ i in f.support.attach.filter fun i : f.support ↦ degM _ (f_support_le i.2) ≤ k,
        ∑ j in (r (f i)).support.attach.filter
          fun j : (r (f i)).support ↦
            degree_monomial (p _ _ j.2) (fun a ha ↦ degA (hp1 _ _ j.2 ha)) =
            k - degM _ (f_support_le i.2),
          (r (f i) j : A) • (eval_monomial (p _ _ j.2) : A) • (i : M) := by
        refine Finset.sum_congr rfl ?_
        rintro ⟨i, hi1⟩ _
        rw [Finset.sum_filter, Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        rintro ⟨h, hj1⟩ -
        simp only [ite_smul, zero_smul, ite_eq_left_iff, not_le]
        intro rid
        rw [if_neg (Ne.symm (ne_of_lt rid))]
    _ = ∑ i in (f.support.attach.filter fun i : f.support ↦ degM _ (f_support_le i.2) ≤ k).attach,
        ∑ j in (r (f i)).support.attach.filter
          fun j : (r (f i)).support ↦
            degree_monomial (p _ _ j.2) (fun a ha ↦ degA (hp1 _ _ j.2 ha)) =
            k - degM _ (f_support_le i.1.2),
          (r (f i) j : A) • (eval_monomial (p _ _ j.2) : A) • (i : M) :=
        Finset.sum_attach _ _ |>.symm
    _ = ∑ i in (f.support.attach.filter fun i : f.support ↦ degM _ (f_support_le i.2) ≤ k).attach,
        ∑ j in ((r (f i)).support.attach.filter
          fun j : (r (f i)).support ↦
            degree_monomial (p _ _ j.2) (fun a ha ↦ degA (hp1 _ _ j.2 ha)) =
            k - degM _ (f_support_le i.1.2)).attach,
          (r (f i) j : A) • (eval_monomial (p _ _ j.1.2) : A) • (i : M) :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_attach _ _ |>.symm

  replace eq0 :
    (⟨x, hx⟩ : ℳ k) =
    ∑ i in (f.support.attach.filter fun i : f.support ↦ degM _ (f_support_le i.2) ≤ k).attach,
        ∑ j in ((r (f i)).support.attach.filter
          fun j : (r (f i)).support ↦
            degree_monomial (p _ _ j.2) (fun a ha ↦ degA (hp1 _ _ j.2 ha)) =
            k - degM _ (f_support_le i.1.2)).attach,
          r (f i) j • (⟨(eval_monomial (p _ _ j.1.2) : A) • (i : M), by
            have mem1 := eval_monomial_mem 𝒜 (p _ _ j.1.2) (fun a ha ↦ degA (hp1 _ _ j.1.2 ha))
              (fun a ha ↦ h_degA (hp1 _ _ j.1.2 ha))
            have mem2 := h_degM _ (f_support_le i.1.2)
            convert (inferInstance : SetLike.GradedSMul 𝒜 ℳ).smul_mem mem1 mem2
            have mem3 := j.2
            simp only [Finset.filter_congr_decidable, Finset.mem_filter, Finset.mem_attach,
              true_and] at mem3
            rw [mem3, vadd_eq_add, Nat.sub_add_cancel]
            simpa using i.2⟩ : ℳ k)
  · ext
    refine eq0.trans ?_
    rw [AddSubgroup.val_finset_sum]
    refine Finset.sum_congr rfl ?_
    rintro ⟨j, hj1⟩ -
    rw [AddSubgroup.val_finset_sum]
    rfl

  rw [eq0]
  refine Submodule.sum_mem _ ?_
  rintro ⟨⟨i, hi1⟩, hi2⟩ -
  simp only [Finset.mem_filter, Finset.mem_attach, true_and] at hi2
  refine Submodule.sum_mem _ ?_
  rintro ⟨⟨j, hj1⟩, hj2⟩ -
  simp only [Finset.filter_congr_decidable, Finset.mem_filter, Finset.mem_attach, true_and] at hj2
  refine Submodule.smul_mem _ _ <| Submodule.subset_span
    ⟨i, f_support_le hi1, p _ _ hj1, hp1 _ _ hj1, ?_, rfl⟩

  rw [hj2]
  exact Nat.sub_le _ _

end finite_module_over_degree_zero_subring

open finite_module_over_degree_zero_subring finite_algebra_over_degree_zero_subring in
instance (k : ℕ) : Module.Finite (𝒜 0) (ℳ k) :=
  ⟨Set.Finite.toFinset (finite1 𝒜 ℳ k),
    by simpa only [Set.Finite.coe_toFinset] using (kth_degree_eq_span 𝒜 ℳ k).symm⟩

end CommRing

end GradedRing
