/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Alternant.Vandermonde
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.DualPieri

/-!
# The dual Pieri rule for Schur polynomials

Following `theories/MPoly/Schur_altdef.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we deduce from the dual Pieri rule
for alternants (`MvPolynomial.altPart_mul_esymm`) and from Jacobi's bialternant formula
(`MvPolynomial.altPart_eq_schurPoly_mul`) the dual Pieri rule for Schur polynomials:

`s_μ * e_r = ∑_{η / μ a vertical strip of size r} s_η`.

Over `ℤ` the Vandermonde alternant is a nonzero element of an integral domain, so it can
be cancelled; the statement over an arbitrary commutative semiring follows by base change.

## Main results

* `MvPolynomial.map_schurPoly` : Schur polynomials are compatible with base change.
* `MvPolynomial.altPart_nil_ne_zero` : the Vandermonde alternant is nonzero over `ℤ`.
* `MvPolynomial.schurPoly_mul_esymm` : **the dual Pieri rule**.
-/

@[expose] public section

open Young

open List

namespace MvPolynomial

open MvPolynomial Finset

variable {m : ℕ}

/-! ### Base change -/

/-- Schur polynomials are compatible with base change. -/
lemma map_schurPoly {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (μ : List ℕ) :
    MvPolynomial.map f (schurPoly (Fin m) R μ) = schurPoly (Fin m) S μ := by
  classical
  rw [schurPoly, schurPoly, map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [map_list_prod, List.map_map]
  simp [Function.comp_def]

/-! ### The Vandermonde alternant is a nonzero divisor -/

/-- Over `ℤ`, the Vandermonde alternant of the staircase is nonzero. -/
lemma altPart_nil_ne_zero (m : ℕ) : altPart m ℤ [] ≠ 0 := by
  rw [altPart_of_le (by simp), alt_staircase]
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
  have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.1 hj)
  exact sub_ne_zero.2 fun h => hij (X_injective h)

/-! ### The dual Pieri rule -/

/-- The dual Pieri rule over `ℤ`, obtained by cancelling the Vandermonde alternant. -/
theorem schurPoly_mul_esymm_int {μ : List ℕ} (hμ : IsPart μ) (r : ℕ) :
    schurPoly (Fin m) ℤ μ * esymm (Fin m) ℤ r
      = ∑ η ∈ partFinset (μ.sum + r),
          if VertStrip η μ then schurPoly (Fin m) ℤ η else 0 := by
  classical
  refine mul_right_cancel₀ (altPart_nil_ne_zero m) ?_
  have hlhs : schurPoly (Fin m) ℤ μ * esymm (Fin m) ℤ r * altPart m ℤ []
      = altPart m ℤ μ * esymm (Fin m) ℤ r := by
    rw [altPart_eq_schurPoly_mul hμ]; ring
  have hrhs : (∑ η ∈ partFinset (μ.sum + r),
        if VertStrip η μ then schurPoly (Fin m) ℤ η else 0) * altPart m ℤ []
      = ∑ η ∈ partFinset (μ.sum + r), if VertStrip η μ then altPart m ℤ η else 0 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun η hη => ?_
    obtain ⟨hηpart, -⟩ := mem_partFinset.1 hη
    by_cases hstrip : VertStrip η μ
    · rw [ite_eq_left hstrip, ite_eq_left hstrip, altPart_eq_schurPoly_mul hηpart]
    · rw [ite_eq_right hstrip, ite_eq_right hstrip, zero_mul]
  rw [hlhs, hrhs]
  exact altPart_mul_esymm hμ r

/-- The dual Pieri rule over `ℕ`, obtained from the one over `ℤ` by injectivity. -/
theorem schurPoly_mul_esymm_nat {μ : List ℕ} (hμ : IsPart μ) (r : ℕ) :
    schurPoly (Fin m) ℕ μ * esymm (Fin m) ℕ r
      = ∑ η ∈ partFinset (μ.sum + r),
          if VertStrip η μ then schurPoly (Fin m) ℕ η else 0 := by
  classical
  refine MvPolynomial.map_injective (Nat.castRingHom ℤ) Nat.cast_injective ?_
  rw [map_mul, map_schurPoly, MvPolynomial.map_esymm, map_sum]
  rw [schurPoly_mul_esymm_int hμ r]
  refine Finset.sum_congr rfl fun η _ => ?_
  by_cases hstrip : VertStrip η μ
  · rw [ite_eq_left hstrip, ite_eq_left hstrip, map_schurPoly]
  · rw [ite_eq_right hstrip, ite_eq_right hstrip, map_zero]

/-- **The dual Pieri rule**: the product of the Schur polynomial of shape `μ` by the
elementary symmetric polynomial of degree `r` is the sum of the Schur polynomials of the
shapes obtained from `μ` by adding a vertical strip with `r` boxes. -/
theorem schurPoly_mul_esymm {R : Type*} [CommSemiring R] {μ : List ℕ} (hμ : IsPart μ)
    (r : ℕ) :
    schurPoly (Fin m) R μ * esymm (Fin m) R r
      = ∑ η ∈ partFinset (μ.sum + r),
          if VertStrip η μ then schurPoly (Fin m) R η else 0 := by
  classical
  have h := congrArg (MvPolynomial.map (Nat.castRingHom R)) (schurPoly_mul_esymm_nat (m := m) hμ r)
  rw [map_mul, map_schurPoly, MvPolynomial.map_esymm, map_sum] at h
  rw [h]
  refine Finset.sum_congr rfl fun η _ => ?_
  by_cases hstrip : VertStrip η μ
  · rw [ite_eq_left hstrip, ite_eq_left hstrip, map_schurPoly]
  · rw [ite_eq_right hstrip, ite_eq_right hstrip, map_zero]

end MvPolynomial
