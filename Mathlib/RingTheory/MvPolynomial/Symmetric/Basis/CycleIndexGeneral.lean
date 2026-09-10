/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.CycleIndex

/-!
# The cycle index sum of an arbitrary family

The cycle index formula `h_n = ∑_{η ⊢ n} p_η / z_η` of
`Mathlib/RingTheory/MvPolynomial/Symmetric/Basis/CycleIndex.lean` only uses the recursion
`n · h_n = ∑_{r=1}^n p_r · h_{n-r}`.  Here we isolate that argument: given any family
`P : ℕ → A` in a commutative ring containing the rationals, the sums
`∑_{η ⊢ n} P_η / z_η` satisfy the same recursion, and they are the unique family
doing so with value `1` in degree `0`.

This is used to identify the Cauchy kernel with its power sum expansion in
`Mathlib/RingTheory/MvPolynomial/Symmetric/Cauchy/PowerSum.lean`.

## Main results

* `MvPolynomial.genCycleIndexSum` : the sum `∑_{η ⊢ n} P_η / z_η`.
* `MvPolynomial.sum_mul_genCycleIndexSum` : it satisfies the recursion
  `n · F n = ∑_{r=1}^n P_r · F (n-r)`.
* `MvPolynomial.eq_genCycleIndexSum_of_rec` : that recursion, together with `F 0 = 1`,
  characterises it.
-/

@[expose] public section

open Young

namespace MvPolynomial

open List

variable {A : Type*} [CommRing A]

/-- The product `P_η = P_{η_1} ⋯ P_{η_k}` attached to a list of parts. -/
noncomputable def genProd (P : ℕ → A) (η : List ℕ) : A := (η.map P).prod

@[simp] lemma genProd_nil (P : ℕ → A) : genProd P [] = 1 := rfl

lemma genProd_cons (P : ℕ → A) (r : ℕ) (η : List ℕ) :
    genProd P (r :: η) = P r * genProd P η := by
  simp [genProd]

lemma genProd_of_perm (P : ℕ → A) {l l' : List ℕ} (h : l.Perm l') :
    genProd P l = genProd P l' := (h.map P).prod_eq

lemma genProd_insPart (P : ℕ → A) (η : List ℕ) (r : ℕ) :
    genProd P (insPart η r) = P r * genProd P η := by
  rw [genProd_of_perm P (insPart_perm η r), genProd_cons]

/-- The sum `∑_{η ⊢ n} P_η / z_η` attached to a family `P`. -/
noncomputable def genCycleIndexSum [Algebra ℚ A] (P : ℕ → A) (n : ℕ) : A :=
  ∑ η ∈ partFinset n, ((zcard η : ℚ))⁻¹ • genProd P η

@[simp] lemma genCycleIndexSum_zero [Algebra ℚ A] (P : ℕ → A) :
    genCycleIndexSum P 0 = 1 := by
  rw [genCycleIndexSum, partFinset_zero, Finset.sum_singleton, genProd_nil]
  norm_num [zcard]

/-- **The recursion satisfied by the cycle index sums**: `n · F n = ∑_{r=1}^n P_r F (n-r)`. -/
lemma sum_mul_genCycleIndexSum [Algebra ℚ A] (P : ℕ → A) (n : ℕ) :
    ∑ r ∈ Finset.Icc 1 n, P r * genCycleIndexSum P (n - r)
      = (n : ℚ) • genCycleIndexSum P n := by
  classical
  have hL : ∑ r ∈ Finset.Icc 1 n, P r * genCycleIndexSum P (n - r)
      = ∑ x ∈ (Finset.Icc 1 n).sigma (fun r => partFinset (n - r)),
          ((zcard x.2 : ℚ))⁻¹ • genProd P (insPart x.2 x.1) := by
    rw [← Finset.sum_sigma' (Finset.Icc 1 n) (fun r => partFinset (n - r))
      (fun r μ => ((zcard μ : ℚ))⁻¹ • genProd P (insPart μ r))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [genCycleIndexSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => by rw [genProd_insPart, mul_smul_comm]
  have hR : (n : ℚ) • genCycleIndexSum P n
      = ∑ y ∈ (partFinset n).sigma (fun η => η.toFinset),
          ((zcard (dropPart y.1 y.2) : ℚ))⁻¹ • genProd P y.1 := by
    rw [← Finset.sum_sigma' (partFinset n) (fun η => η.toFinset)
      (fun η r => ((zcard (dropPart η r) : ℚ))⁻¹ • genProd P η),
      genCycleIndexSum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun η hη => ?_
    obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hη
    rw [← Finset.sum_smul, sum_inv_zcard_dropPart hpart, hsum, smul_smul]
  rw [hL, hR]
  refine Finset.sum_nbij' (i := fun x => (⟨insPart x.2 x.1, x.1⟩ : (_ : List ℕ) × ℕ))
    (j := fun y => (⟨y.2, dropPart y.1 y.2⟩ : (_ : ℕ) × List ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨r, μ⟩ hx
    simp only [Finset.mem_sigma] at hx ⊢
    obtain ⟨hr, hμ⟩ := hx
    obtain ⟨hμpart, hμsum⟩ := mem_partFinset.1 hμ
    rw [Finset.mem_Icc] at hr
    refine ⟨mem_partFinset.2 ⟨isPart_insPart hμpart hr.1, ?_⟩, ?_⟩
    · rw [sum_insPart, hμsum]; omega
    · exact List.mem_toFinset.2 (mem_insPart_self μ r)
  · rintro ⟨η, r⟩ hy
    simp only [Finset.mem_sigma] at hy ⊢
    obtain ⟨hη, hr⟩ := hy
    obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hη
    have hrm : r ∈ η := List.mem_toFinset.1 hr
    have hpos : 0 < r := hpart.pos_of_mem hrm
    have hsd := sum_dropPart hrm
    refine ⟨Finset.mem_Icc.2 ⟨hpos, by omega⟩, mem_partFinset.2 ⟨isPart_dropPart hpart r, ?_⟩⟩
    omega
  · rintro ⟨r, μ⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hμpart, -⟩ := mem_partFinset.1 hx.2
    simp only [dropPart_insPart hμpart]
  · rintro ⟨η, r⟩ hy
    rw [Finset.mem_sigma] at hy
    obtain ⟨hpart, -⟩ := mem_partFinset.1 hy.1
    have hrm : r ∈ η := List.mem_toFinset.1 hy.2
    simp only [insPart_dropPart hpart hrm]
  · rintro ⟨r, μ⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hμpart, -⟩ := mem_partFinset.1 hx.2
    rw [dropPart_insPart hμpart]

/-- **The recursion characterises the cycle index sums**: a family `F` with `F 0 = 1` and
`n · F n = ∑_{r=1}^n P_r · F (n-r)` is the family of the sums `∑_{η ⊢ n} P_η / z_η`. -/
theorem eq_genCycleIndexSum_of_rec [Algebra ℚ A] (P F : ℕ → A) (h0 : F 0 = 1)
    (hrec : ∀ n : ℕ, (n : ℚ) • F n = ∑ r ∈ Finset.Icc 1 n, P r * F (n - r)) (n : ℕ) :
    F n = genCycleIndexSum P n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [h0, genCycleIndexSum_zero]
    · have hterm : ∀ r ∈ Finset.Icc 1 n, P r * F (n - r) = P r * genCycleIndexSum P (n - r) := by
        intro r hr
        rw [Finset.mem_Icc] at hr
        rw [ih (n - r) (by omega)]
      have hq : (n : ℚ) • F n = (n : ℚ) • genCycleIndexSum P n := by
        rw [hrec n, Finset.sum_congr rfl hterm, sum_mul_genCycleIndexSum]
      exact smul_right_injective _ (Nat.cast_ne_zero.2 hn.ne' : (n : ℚ) ≠ 0) hq

end MvPolynomial
