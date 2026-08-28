/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.DualPieriSchur

/-!
# The Jacobi-Trudi formula

Following `theories/MPoly/Schur_altdef.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove the Jacobi-Trudi formula
expressing a Schur polynomial as a determinant of complete homogeneous symmetric
polynomials:

`s_lam = det (h_{lam_i - i + j})_{0 ≤ i, j < m}`,

for a partition `lam` with at most `m` parts, in `m` variables.

The proof is the classical one.  Write `e^{(j)}_r` for the elementary symmetric polynomial
in the variables other than `X j`.  Since
`(∑_r h_r t^r) · (∑_r (-1)^r e^{(j)}_r t^r) = ∑_r (X j)^r t^r`, one gets

`∑_r (-1)^r e^{(j)}_r h_{a - r} = (X j) ^ a`,

which says exactly that the product of the Jacobi-Trudi matrix of `lam` with the matrix
`B_{k j} = (-1)^{m-1-k} e^{(j)}_{m-1-k}` is the matrix `(X j ^ (lam + delta)_i)` whose
determinant is the alternant `a_{lam + delta}`.  Taking `lam = 0`, the Jacobi-Trudi matrix
is upper triangular with `1` on the diagonal, so `det B` is the Vandermonde alternant
`a_delta`; comparing with Jacobi's bialternant formula `a_{lam + delta} = s_lam · a_delta`
and cancelling `a_delta` gives the result.

## Main definitions and results

* `MvPolynomial.esymmErase m R j r` : the elementary symmetric polynomial of degree `r` in the
  variables other than `X j`.
* `MvPolynomial.hsymmInt m R n` : the complete homogeneous symmetric polynomial indexed by an
  integer, zero for negative indices.
* `MvPolynomial.sum_esymmErase_mul_hsymmInt` : `∑_{r < m} (-1)^r e^{(j)}_r h_{a-r} = (X j)^a`.
* `MvPolynomial.jtMatrix m R lam` : the Jacobi-Trudi matrix `(h_{lam_i - i + j})`.
* `MvPolynomial.det_jtMatrix_mul_alt` : `det (jtMatrix lam) · a_delta = a_{lam + delta}`.
* `MvPolynomial.schurPoly_eq_det_jtMatrix` : **the Jacobi-Trudi formula**.
-/

open List

namespace MvPolynomial

open MvPolynomial Finset

variable {m : ℕ} {R : Type*} [CommRing R]

/-! ### The elementary symmetric polynomials in all but one variable -/

/-- The elementary symmetric polynomial of degree `r` in the variables other than `X j`. -/
noncomputable def esymmErase (m : ℕ) (R : Type*) [CommRing R] (j : Fin m) (r : ℕ) :
    MvPolynomial (Fin m) R :=
  ∑ S ∈ Finset.powersetCard r ((Finset.univ : Finset (Fin m)).erase j), ∏ i ∈ S, X i

@[simp]
lemma esymmErase_zero (j : Fin m) : esymmErase m R j 0 = 1 := by
  simp [esymmErase]

/-- There is no elementary symmetric polynomial of degree `≥ m` in `m - 1` variables. -/
lemma esymmErase_eq_zero_of_le (j : Fin m) {r : ℕ} (hr : m ≤ r) :
    esymmErase m R j r = 0 := by
  have hm : 0 < m := j.pos
  have hcard : ((Finset.univ : Finset (Fin m)).erase j).card < r := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  rw [esymmErase, Finset.powersetCard_eq_empty.2 hcard, Finset.sum_empty]

/-- Splitting the subsets of size `r + 1` according to whether they contain `j` or not. -/
lemma esymm_succ_eq_esymmErase (j : Fin m) (r : ℕ) :
    esymm (Fin m) R (r + 1) = esymmErase m R j (r + 1) + X j * esymmErase m R j r := by
  classical
  have hj : j ∉ (Finset.univ : Finset (Fin m)).erase j := Finset.notMem_erase _ _
  have huniv : (Finset.univ : Finset (Fin m)) = insert j (Finset.univ.erase j) :=
    (Finset.insert_erase (Finset.mem_univ j)).symm
  rw [esymm, huniv, Finset.powersetCard_succ_insert hj, Finset.sum_union, esymmErase,
    esymmErase, Finset.mul_sum, Finset.sum_image]
  · refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun S hS => ?_)
    have hjS : j ∉ S := fun h => hj ((Finset.mem_powersetCard.1 hS).1 h)
    rw [Finset.prod_insert hjS]
  · intro S hS T hT hST
    have hjS : j ∉ S := fun h => hj ((Finset.mem_powersetCard.1 (Finset.mem_coe.1 hS)).1 h)
    have hjT : j ∉ T := fun h => hj ((Finset.mem_powersetCard.1 (Finset.mem_coe.1 hT)).1 h)
    have := congrArg (fun U : Finset (Fin m) => U.erase j) hST
    simpa only [Finset.erase_insert hjS, Finset.erase_insert hjT] using this
  · refine Finset.disjoint_left.2 fun S hS hS' => ?_
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hS'
    exact hj ((Finset.mem_powersetCard.1 hS).1 (Finset.mem_insert_self _ _))

/-! ### Complete homogeneous symmetric polynomials with an integer index -/

/-- The complete homogeneous symmetric polynomial indexed by an integer: it is zero for a
negative index. -/
noncomputable def hsymmInt (m : ℕ) (R : Type*) [CommRing R] (n : ℤ) :
    MvPolynomial (Fin m) R :=
  if 0 ≤ n then hsymm (Fin m) R n.toNat else 0

@[simp]
lemma hsymmInt_natCast (n : ℕ) : hsymmInt m R (n : ℤ) = hsymm (Fin m) R n := by
  simp [hsymmInt]

lemma hsymmInt_of_neg {n : ℤ} (hn : n < 0) : hsymmInt m R n = 0 := by
  simp [hsymmInt, not_le.2 hn]

@[simp]
lemma hsymmInt_zero : hsymmInt m R 0 = 1 := by
  simpa using hsymmInt_natCast (m := m) (R := R) 0

/-! ### The key identity -/

/-- `∑_{r ≤ n} (-1)^r e^{(j)}_r h_{n-r} = (X j)^n`, the coefficientwise form of
`H(t) · E^{(j)}(-t) = (1 - X j · t)⁻¹`. -/
theorem sum_esymmErase_mul_hsymm (j : Fin m) (n : ℕ) :
    ∑ r ∈ Finset.range (n + 1),
        (-1 : MvPolynomial (Fin m) R) ^ r * esymmErase m R j r * hsymm (Fin m) R (n - r)
      = X j ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hzero : ∑ r ∈ Finset.range (n + 2),
        (-1 : MvPolynomial (Fin m) R) ^ r * (esymm (Fin m) R r * hsymm (Fin m) R (n + 1 - r))
          = 0 := sum_neg_one_pow_esymm_mul_hsymm m R (Nat.succ_pos n)
    have hstep : ∀ r ∈ Finset.range (n + 1),
        (-1 : MvPolynomial (Fin m) R) ^ (r + 1) * esymmErase m R j (r + 1)
            * hsymm (Fin m) R (n + 1 - (r + 1))
          = (-1 : MvPolynomial (Fin m) R) ^ (r + 1)
              * (esymm (Fin m) R (r + 1) * hsymm (Fin m) R (n + 1 - (r + 1)))
            + X j * ((-1 : MvPolynomial (Fin m) R) ^ r * esymmErase m R j r
              * hsymm (Fin m) R (n - r)) := by
      intro r _
      have he : esymmErase m R j (r + 1)
          = esymm (Fin m) R (r + 1) - X j * esymmErase m R j r := by
        rw [esymm_succ_eq_esymmErase (R := R) j r]; ring
      have hn : n + 1 - (r + 1) = n - r := by omega
      rw [he, hn]
      ring
    rw [Finset.sum_range_succ'] at hzero ⊢
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum, ih]
    simp only [pow_zero, one_mul, esymmErase_zero, Nat.sub_zero, esymm_zero] at hzero ⊢
    rw [pow_succ, mul_comm (X j ^ n)]
    linear_combination hzero

/-- The identity `∑_r (-1)^r e^{(j)}_r h_{a-r} = (X j)^a`, with the sum ranging over
`r < m` and with the complete homogeneous polynomials indexed by integers. -/
theorem sum_esymmErase_mul_hsymmInt (j : Fin m) (a : ℕ) :
    ∑ r ∈ Finset.range m,
        (-1 : MvPolynomial (Fin m) R) ^ r * esymmErase m R j r * hsymmInt m R ((a : ℤ) - r)
      = X j ^ a := by
  classical
  set T : ℕ → MvPolynomial (Fin m) R := fun r =>
    (-1 : MvPolynomial (Fin m) R) ^ r * esymmErase m R j r * hsymmInt m R ((a : ℤ) - r) with hT
  have h1 : ∑ r ∈ Finset.range m, T r = ∑ r ∈ Finset.range (max m (a + 1)), T r := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (le_max_left m (a + 1))) fun r _ hr => ?_
    have hmr : m ≤ r := by simpa using hr
    simp [hT, esymmErase_eq_zero_of_le j hmr]
  have h2 : ∑ r ∈ Finset.range (a + 1), T r = ∑ r ∈ Finset.range (max m (a + 1)), T r := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (le_max_right m (a + 1))) fun r _ hr => ?_
    have har : a + 1 ≤ r := by simpa using hr
    have : ((a : ℤ) - r) < 0 := by
      have : (a : ℤ) < r := by exact_mod_cast Nat.lt_of_succ_le har
      omega
    simp [hT, hsymmInt_of_neg this]
  have h3 : ∑ r ∈ Finset.range (a + 1), T r = X j ^ a := by
    rw [← sum_esymmErase_mul_hsymm (R := R) j a]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hra : r ≤ a := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
    have hcast : ((a : ℤ) - r) = ((a - r : ℕ) : ℤ) := by
      have : (r : ℤ) ≤ a := by exact_mod_cast hra
      push_cast [Nat.cast_sub hra]
      ring
    simp [hT, hcast]
  rw [h1, ← h2, h3]

/-! ### The Jacobi-Trudi matrix -/

/-- The Jacobi-Trudi matrix of a shape `lam`: its `(i, j)` entry is `h_{lam_i - i + j}`. -/
noncomputable def jtMatrix (m : ℕ) (R : Type*) [CommRing R] (lam : List ℕ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin m) R) :=
  Matrix.of fun i k => hsymmInt m R ((lam.getD i 0 : ℤ) + (k : ℕ) - (i : ℕ))

/-- The auxiliary matrix `B_{k j} = (-1)^{m-1-k} e^{(j)}_{m-1-k}`. -/
noncomputable def jtAuxMatrix (m : ℕ) (R : Type*) [CommRing R] :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin m) R) :=
  Matrix.of fun k j => (-1 : MvPolynomial (Fin m) R) ^ (m - 1 - (k : ℕ))
    * esymmErase m R j (m - 1 - (k : ℕ))

/-- The product of the Jacobi-Trudi matrix of `lam` with the auxiliary matrix is the
matrix `(X j ^ (lam + delta)_i)` of the alternant. -/
theorem jtMatrix_mul_jtAuxMatrix (lam : List ℕ) :
    jtMatrix m R lam * jtAuxMatrix m R
      = Matrix.of fun i j : Fin m => (X j : MvPolynomial (Fin m) R) ^ partVec m lam i := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply]
  have hL : ∑ k : Fin m, jtMatrix m R lam i k * jtAuxMatrix m R k j
      = ∑ k ∈ Finset.range m, hsymmInt m R ((lam.getD i 0 : ℤ) + (k : ℕ) - (i : ℕ))
          * ((-1 : MvPolynomial (Fin m) R) ^ (m - 1 - k) * esymmErase m R j (m - 1 - k)) :=
    Fin.sum_univ_eq_sum_range (fun k : ℕ => hsymmInt m R ((lam.getD i 0 : ℤ) + (k : ℕ) - (i : ℕ))
      * ((-1 : MvPolynomial (Fin m) R) ^ (m - 1 - k) * esymmErase m R j (m - 1 - k))) m
  rw [hL, Matrix.of_apply, ← sum_esymmErase_mul_hsymmInt (R := R) j (partVec m lam i),
    ← Finset.sum_range_reflect (fun r => (-1 : MvPolynomial (Fin m) R) ^ r * esymmErase m R j r
      * hsymmInt m R ((partVec m lam i : ℤ) - r)) m]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < m := Finset.mem_range.1 hk
  have hi : (i : ℕ) < m := i.isLt
  have hcast : ((lam.getD i 0 : ℤ) + (k : ℕ) - (i : ℕ))
      = ((partVec m lam i : ℕ) : ℤ) - ((m - 1 - k : ℕ) : ℤ) := by
    simp only [partVec]
    omega
  rw [hcast]
  ring

/-- The determinant of the matrix `(X j ^ a i)` is the alternant of `a`. -/
lemma det_of_pow_eq_alt (a : Fin m → ℕ) :
    (Matrix.of fun i j : Fin m => (X j : MvPolynomial (Fin m) R) ^ a i).det = alt m R a := by
  rw [alt_eq_det, ← Matrix.det_transpose]
  rfl

/-- The Jacobi-Trudi matrix of the empty shape is upper triangular with `1` on the
diagonal, hence has determinant `1`. -/
lemma det_jtMatrix_nil : (jtMatrix m R []).det = 1 := by
  have htri : (jtMatrix m R ([] : List ℕ)).BlockTriangular id := by
    intro i k hik
    have hneg : ((([] : List ℕ).getD i 0 : ℤ) + (k : ℕ) - (i : ℕ)) < 0 := by
      have : (k : ℕ) < (i : ℕ) := hik
      simp only [List.getD_nil, Nat.cast_zero, zero_add]
      omega
    exact hsymmInt_of_neg hneg
  rw [Matrix.det_of_upperTriangular htri]
  refine Finset.prod_eq_one fun i _ => ?_
  have hz : ((([] : List ℕ).getD i 0 : ℤ) + (i : ℕ) - (i : ℕ)) = 0 := by
    simp
  change hsymmInt m R ((([] : List ℕ).getD i 0 : ℤ) + (i : ℕ) - (i : ℕ)) = 1
  rw [hz, hsymmInt_zero]

/-- The determinant of the auxiliary matrix is the Vandermonde alternant. -/
lemma det_jtAuxMatrix : (jtAuxMatrix m R).det = alt m R (partVec m []) := by
  have h := congrArg Matrix.det (jtMatrix_mul_jtAuxMatrix (m := m) (R := R) [])
  rw [Matrix.det_mul, det_jtMatrix_nil, one_mul, det_of_pow_eq_alt] at h
  exact h

/-- The determinant of the Jacobi-Trudi matrix times the Vandermonde alternant is the
alternant of `lam + delta`. -/
theorem det_jtMatrix_mul_alt (lam : List ℕ) :
    (jtMatrix m R lam).det * alt m R (partVec m []) = alt m R (partVec m lam) := by
  have h := congrArg Matrix.det (jtMatrix_mul_jtAuxMatrix (m := m) (R := R) lam)
  rw [Matrix.det_mul, det_jtAuxMatrix, det_of_pow_eq_alt] at h
  exact h

/-! ### The Jacobi-Trudi formula -/

/-- **The Jacobi-Trudi formula** over `ℤ`. -/
theorem schurPoly_eq_det_jtMatrix_int {lam : List ℕ} (hlam : IsPart lam)
    (hlen : lam.length ≤ m) :
    schurPoly (Fin m) ℤ lam = (jtMatrix m ℤ lam).det := by
  have hne : alt m ℤ (partVec m []) ≠ 0 := by
    rw [← altPart_of_le (m := m) (R := ℤ) (lam := ([] : List ℕ)) (by simp)]
    exact altPart_nil_ne_zero m
  refine mul_right_cancel₀ hne ?_
  rw [det_jtMatrix_mul_alt, alt_partVec_eq_schurPoly_mul hlam hlen]

/-- The complete homogeneous symmetric polynomials with an integer index are compatible
with base change. -/
lemma map_hsymmInt {S : Type*} [CommRing S] (f : R →+* S) (n : ℤ) :
    MvPolynomial.map f (hsymmInt m R n) = hsymmInt m S n := by
  simp only [hsymmInt]
  split
  · exact MvPolynomial.map_hsymm (Fin m) R _ f
  · exact map_zero _

/-- **The Jacobi-Trudi formula**: the Schur polynomial of a partition `lam` with at most
`m` parts is the determinant of the matrix `(h_{lam_i - i + j})_{0 ≤ i, j < m}` of complete
homogeneous symmetric polynomials in `m` variables. -/
theorem schurPoly_eq_det_jtMatrix {lam : List ℕ} (hlam : IsPart lam) (hlen : lam.length ≤ m) :
    schurPoly (Fin m) R lam = (jtMatrix m R lam).det := by
  have h := congrArg (MvPolynomial.map (Int.castRingHom R))
    (schurPoly_eq_det_jtMatrix_int (m := m) hlam hlen)
  rw [map_schurPoly, RingHom.map_det] at h
  have hmat : (MvPolynomial.map (Int.castRingHom R)).mapMatrix (jtMatrix m ℤ lam)
      = jtMatrix m R lam :=
    Matrix.ext fun i k => map_hsymmInt (m := m) (Int.castRingHom R) _
  rw [h, hmat]

end MvPolynomial
