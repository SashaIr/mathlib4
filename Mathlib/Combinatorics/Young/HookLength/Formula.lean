/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.HookLength.Basic
public import Mathlib.Combinatorics.Young.HookLength.Frobenius

/-!
# The hook length formula

This file proves the **hook length formula**: the number `f^η` of standard Young tableaux
of shape a partition `η` of `n` is

`f^η = n ! / ∏_{(i, j) ∈ η} h(i, j)`,

where `h(i, j)` is the hook length of the box `(i, j)`.  It is stated in the division free
form `Young.numStdTab_mul_hookProd`:

`f^η · ∏_{(i, j) ∈ η} h(i, j) = n !`.

The proof combines the Frobenius formula `Young.numStdTab_mul_prod_factorial`, which computes
`f^η` in terms of the first column hook lengths `x_i` of `η`, with the identity
`Young.rowHookProd_mul_prod_colHook_sub` between the hook lengths of a row and the first
column hook lengths: multiplying the latter over all the rows gives

`(∏ hook lengths) · ∏_{i < j} (x_j - x_i) = ∏_i x_i !`,

which is exactly what is needed to turn the Frobenius formula into the hook length formula.

## Main results

* `Young.prod_factorial_frobVec_eq` : `∏_i x_i ! = (∏ hook lengths) · ∏_{i < j} (x_j - x_i)`.
* `Young.numStdTab_mul_hookProd` : the hook length formula.
* `Young.numStdTab_pos` : there is at least one standard tableau of any partition shape.

## References

* [B. E. Sagan, *The symmetric group*][sagan2001]
* [C. Greene, A. Nijenhuis and H. S. Wilf, *A probabilistic proof of a formula for the
  number of Young tableaux of a given shape*][greene-nijenhuis-wilf1979]
* [F. Hivert et al., *Coq-Combi*][hivert-coqcombi]
-/

@[expose] public section

namespace Young

open List Finset

variable {μ : List ℕ}

/-! ### The first column hook lengths as a family indexed by `Fin (length μ)` -/

/-- The first column hook lengths of `Young.frobVec` are those of `Young.colHook`, read in
the reverse order. -/
lemma frobVec_eq_colHook (μ : List ℕ) (i : Fin μ.length) :
    frobVec μ.length μ i = colHook μ (i.rev : ℕ) := by
  have h1 : ((i.rev : Fin μ.length) : ℕ) = μ.length - ((i : ℕ) + 1) := Fin.val_rev i
  have h2 : (i : ℕ) < μ.length := i.isLt
  simp only [frobVec, colHook]
  omega

/-- The first column hook lengths increase with the index of `Young.frobVec`. -/
lemma frobVec_lt_frobVec (hμ : IsPart μ) {i j : Fin μ.length} (hij : j < i) :
    frobVec μ.length μ j < frobVec μ.length μ i := by
  have hlt : ((i.rev : Fin μ.length) : ℕ) < ((j.rev : Fin μ.length) : ℕ) := by
    have h1 : ((i.rev : Fin μ.length) : ℕ) = μ.length - ((i : ℕ) + 1) := Fin.val_rev i
    have h2 : ((j.rev : Fin μ.length) : ℕ) = μ.length - ((j : ℕ) + 1) := Fin.val_rev j
    have h3 : (i : ℕ) < μ.length := i.isLt
    have h4 : (j : ℕ) < (i : ℕ) := hij
    omega
  rw [frobVec_eq_colHook, frobVec_eq_colHook]
  exact colHook_strictAnti hμ hlt (Fin.is_lt _)

/-- The product of the factorials of the first column hook lengths, indexed by rows. -/
lemma prod_factorial_frobVec_eq_prod_range (μ : List ℕ) :
    ∏ i : Fin μ.length, Nat.factorial (frobVec μ.length μ i)
      = ∏ r ∈ Finset.range μ.length, Nat.factorial (colHook μ r) := by
  have h1 : ∏ i : Fin μ.length, Nat.factorial (frobVec μ.length μ i)
      = ∏ i : Fin μ.length, Nat.factorial (colHook μ (i.rev : ℕ)) :=
    Finset.prod_congr rfl fun i _ => by rw [frobVec_eq_colHook]
  have h2 : ∏ i : Fin μ.length, Nat.factorial (colHook μ (i.rev : ℕ))
      = ∏ i : Fin μ.length, Nat.factorial (colHook μ (i : ℕ)) :=
    Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin μ.length))
      fun i : Fin μ.length => Nat.factorial (colHook μ (i : ℕ))
  rw [h1, h2, Fin.prod_univ_eq_prod_range fun r => Nat.factorial (colHook μ r)]

/-! ### The product of the hook lengths of a row, indexed by `Fin (length μ)` -/

/-- The rows below the row `i.rev` are indexed by the elements of `Fin (length μ)` that are
smaller than `i`. -/
lemma prod_colHook_sub_eq_prod_Iio (i : Fin μ.length) :
    ∏ s ∈ Finset.Ico ((i.rev : ℕ) + 1) μ.length,
        (colHook μ (i.rev : ℕ) - colHook μ s)
      = ∏ j ∈ Finset.Iio i, (frobVec μ.length μ i - frobVec μ.length μ j) := by
  have hi : ((i.rev : Fin μ.length) : ℕ) = μ.length - ((i : ℕ) + 1) := Fin.val_rev i
  have hilt : (i : ℕ) < μ.length := i.isLt
  refine (Finset.prod_nbij (fun j : Fin μ.length => ((j.rev : Fin μ.length) : ℕ))
    ?_ ?_ ?_ ?_).symm
  · intro j hj
    rw [Finset.mem_Iio] at hj
    have h2 : ((j.rev : Fin μ.length) : ℕ) = μ.length - ((j : ℕ) + 1) := Fin.val_rev j
    have h4 : (j : ℕ) < (i : ℕ) := hj
    simp only [Finset.mem_Ico]
    omega
  · intro a _ b _ hab
    simp only at hab
    have h2 : ((a.rev : Fin μ.length) : ℕ) = μ.length - ((a : ℕ) + 1) := Fin.val_rev a
    have h3 : ((b.rev : Fin μ.length) : ℕ) = μ.length - ((b : ℕ) + 1) := Fin.val_rev b
    have h4 : (a : ℕ) < μ.length := a.isLt
    have h5 : (b : ℕ) < μ.length := b.isLt
    exact Fin.ext (by omega)
  · intro s hs
    rw [Finset.coe_Ico, Set.mem_Ico] at hs
    refine ⟨(⟨s, by omega⟩ : Fin μ.length).rev, ?_, ?_⟩
    · have h2 : ((⟨s, by omega⟩ : Fin μ.length).rev : ℕ) = μ.length - (s + 1) :=
        Fin.val_rev ⟨s, by omega⟩
      simp only [Finset.coe_Iio, Set.mem_Iio, Fin.lt_def]
      omega
    · have h2 : ((⟨s, by omega⟩ : Fin μ.length).rev : ℕ) = μ.length - (s + 1) :=
        Fin.val_rev ⟨s, by omega⟩
      have h3 : (((⟨s, by omega⟩ : Fin μ.length).rev.rev : Fin μ.length) : ℕ)
          = μ.length - (((⟨s, by omega⟩ : Fin μ.length).rev : ℕ) + 1) :=
        Fin.val_rev (⟨s, by omega⟩ : Fin μ.length).rev
      simp only
      omega
  · intro j _
    rw [frobVec_eq_colHook, frobVec_eq_colHook]

/-! ### The product of all the hook lengths -/

/-- The product of the factorials of the first column hook lengths of `μ` is the product of
all the hook lengths of `μ`, times the product of the differences of the first column hook
lengths. -/
theorem prod_factorial_frobVec_eq (hμ : IsPart μ) :
    ∏ i : Fin μ.length, Nat.factorial (frobVec μ.length μ i)
      = hookProd μ * ∏ i : Fin μ.length, ∏ j ∈ Finset.Iio i,
          (frobVec μ.length μ i - frobVec μ.length μ j) := by
  have hrow : ∀ i : Fin μ.length,
      rowHookProd μ (i.rev : ℕ)
          * ∏ j ∈ Finset.Iio i, (frobVec μ.length μ i - frobVec μ.length μ j)
        = Nat.factorial (frobVec μ.length μ i) := by
    intro i
    rw [← prod_colHook_sub_eq_prod_Iio i, frobVec_eq_colHook]
    exact rowHookProd_mul_prod_colHook_sub hμ (Fin.is_lt _)
  have hhook : ∏ i : Fin μ.length, rowHookProd μ (i.rev : ℕ) = hookProd μ := by
    have h2 : ∏ i : Fin μ.length, rowHookProd μ (i.rev : ℕ)
        = ∏ i : Fin μ.length, rowHookProd μ (i : ℕ) :=
      Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin μ.length))
        fun i : Fin μ.length => rowHookProd μ (i : ℕ)
    rw [h2, Fin.prod_univ_eq_prod_range fun r => rowHookProd μ r, hookProd]
  calc ∏ i : Fin μ.length, Nat.factorial (frobVec μ.length μ i)
      = ∏ i : Fin μ.length, (rowHookProd μ (i.rev : ℕ)
          * ∏ j ∈ Finset.Iio i, (frobVec μ.length μ i - frobVec μ.length μ j)) :=
        Finset.prod_congr rfl fun i _ => (hrow i).symm
    _ = hookProd μ * ∏ i : Fin μ.length, ∏ j ∈ Finset.Iio i,
          (frobVec μ.length μ i - frobVec μ.length μ j) := by
        rw [Finset.prod_mul_distrib, hhook]

/-- The product of the differences of the first column hook lengths is the Vandermonde
product. -/
theorem cast_prod_frobVec_sub (hμ : IsPart μ) :
    ((∏ i : Fin μ.length, ∏ j ∈ Finset.Iio i,
        (frobVec μ.length μ i - frobVec μ.length μ j) : ℕ) : ℤ)
      = vdmProd fun i => ((frobVec μ.length μ i : ℕ) : ℤ) := by
  have hcast : ((∏ i : Fin μ.length, ∏ j ∈ Finset.Iio i,
      (frobVec μ.length μ i - frobVec μ.length μ j) : ℕ) : ℤ)
      = ∏ i : Fin μ.length, ∏ j ∈ Finset.Iio i,
          (((frobVec μ.length μ i : ℕ) : ℤ) - ((frobVec μ.length μ j : ℕ) : ℤ)) := by
    push_cast
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_Iio] at hj
    have := frobVec_lt_frobVec hμ hj
    push_cast [Nat.cast_sub (le_of_lt this)]
    ring
  rw [hcast, vdmProd]
  exact Finset.prod_comm' (by simp)

/-- The differences of the first column hook lengths have a positive product. -/
lemma prod_frobVec_sub_pos (hμ : IsPart μ) :
    0 < ∏ i : Fin μ.length, ∏ j ∈ Finset.Iio i,
      (frobVec μ.length μ i - frobVec μ.length μ j) := by
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
  rw [Finset.mem_Iio] at hj
  have := frobVec_lt_frobVec hμ hj
  omega

/-! ### The hook length formula -/

/-- **The hook length formula**: the number of standard Young tableaux of shape a partition
`η` of `n`, multiplied by the product of the hook lengths of the boxes of `η`, is `n !`.
-/
theorem numStdTab_mul_hookProd (hμ : IsPart μ) :
    numStdTab μ * hookProd μ = Nat.factorial μ.sum := by
  set D : ℕ := ∏ i : Fin μ.length, ∏ j ∈ Finset.Iio i,
    (frobVec μ.length μ i - frobVec μ.length μ j) with hD
  have hDpos : 0 < D := prod_frobVec_sub_pos hμ
  have hDcast : (D : ℤ) = vdmProd fun i => ((frobVec μ.length μ i : ℕ) : ℤ) :=
    cast_prod_frobVec_sub hμ
  have hfrob := numStdTab_mul_prod_factorial μ.length μ.sum μ hμ le_rfl rfl
  rw [← hDcast, ← Nat.cast_prod, prod_factorial_frobVec_eq hμ, ← hD] at hfrob
  have hcast : ((numStdTab μ * hookProd μ * D : ℕ) : ℤ)
      = ((Nat.factorial μ.sum * D : ℕ) : ℤ) := by
    push_cast at hfrob ⊢
    linarith
  exact Nat.eq_of_mul_eq_mul_right hDpos (by exact_mod_cast hcast)

/-- The number of standard Young tableaux of a shape which is a partition is positive. -/
lemma numStdTab_pos (hμ : IsPart μ) : 0 < numStdTab μ :=
  Nat.pos_of_ne_zero fun h => Nat.factorial_ne_zero μ.sum <| by
    rw [← numStdTab_mul_hookProd hμ, h, zero_mul]

/-- The product of the hook lengths of a partition is positive. -/
lemma hookProd_pos (hμ : IsPart μ) : 0 < hookProd μ := by
  refine Finset.prod_pos fun r _ => Finset.prod_pos fun c hc => ?_
  rw [Finset.mem_range] at hc
  exact one_le_hookLength hμ hc

/-- The product of the hook lengths of a partition of `n` divides `n !`. -/
lemma hookProd_dvd_factorial (hμ : IsPart μ) : hookProd μ ∣ Nat.factorial μ.sum :=
  ⟨numStdTab μ, by rw [← numStdTab_mul_hookProd hμ, Nat.mul_comm]⟩

/-- **The hook length formula**, in division form: the number of standard Young tableaux of
shape a partition `η` of `n` is `n !` divided by the product of the hook lengths of the
boxes of `η`. -/
theorem numStdTab_eq_factorial_div_hookProd (hμ : IsPart μ) :
    numStdTab μ = Nat.factorial μ.sum / hookProd μ := by
  rw [← numStdTab_mul_hookProd hμ, Nat.mul_div_cancel _ (hookProd_pos hμ)]

end Young
