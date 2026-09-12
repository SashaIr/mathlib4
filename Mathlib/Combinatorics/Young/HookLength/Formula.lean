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

This file proves the **hook length formula**: the number `f^μ` of standard Young tableaux
of shape a partition `μ` of `n` is

`f^μ = n ! / ∏_{(i, j) ∈ μ} h(i, j)`,

where `h(i, j)` is the hook length of the box `(i, j)`.  It is stated in the division free
form `Young.numStdTab_mul_hookProd`:

`f^μ · ∏_{(i, j) ∈ μ} h(i, j) = n !`.

The proof combines the Frobenius formula `Young.numStdTab_mul_prod_factorial`, which computes
`f^μ` in terms of the first column hook lengths `x_i` of `μ`, with the identity
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

variable {ν : List ℕ}

/-! ### The first column hook lengths as a family indexed by `Fin (length ν)` -/

/-- The first column hook lengths of `Young.frobVec` are those of `Young.colHook`, read in
the reverse order. -/
lemma frobVec_eq_colHook (ν : List ℕ) (i : Fin ν.length) :
    frobVec ν.length ν i = colHook ν (i.rev : ℕ) := by
  have h1 : ((i.rev : Fin ν.length) : ℕ) = ν.length - ((i : ℕ) + 1) := Fin.val_rev i
  have h2 : (i : ℕ) < ν.length := i.isLt
  simp only [frobVec, colHook]
  omega

/-- The first column hook lengths increase with the index of `Young.frobVec`. -/
lemma frobVec_lt_frobVec (hν : IsPart ν) {i j : Fin ν.length} (hij : j < i) :
    frobVec ν.length ν j < frobVec ν.length ν i := by
  have hlt : ((i.rev : Fin ν.length) : ℕ) < ((j.rev : Fin ν.length) : ℕ) := by
    have h1 : ((i.rev : Fin ν.length) : ℕ) = ν.length - ((i : ℕ) + 1) := Fin.val_rev i
    have h2 : ((j.rev : Fin ν.length) : ℕ) = ν.length - ((j : ℕ) + 1) := Fin.val_rev j
    have h3 : (i : ℕ) < ν.length := i.isLt
    have h4 : (j : ℕ) < (i : ℕ) := hij
    omega
  rw [frobVec_eq_colHook, frobVec_eq_colHook]
  exact colHook_strictAnti hν hlt (Fin.is_lt _)

/-- The product of the factorials of the first column hook lengths, indexed by rows. -/
lemma prod_factorial_frobVec_eq_prod_range (ν : List ℕ) :
    ∏ i : Fin ν.length, Nat.factorial (frobVec ν.length ν i)
      = ∏ r ∈ Finset.range ν.length, Nat.factorial (colHook ν r) := by
  have h1 : ∏ i : Fin ν.length, Nat.factorial (frobVec ν.length ν i)
      = ∏ i : Fin ν.length, Nat.factorial (colHook ν (i.rev : ℕ)) :=
    Finset.prod_congr rfl fun i _ => by rw [frobVec_eq_colHook]
  have h2 : ∏ i : Fin ν.length, Nat.factorial (colHook ν (i.rev : ℕ))
      = ∏ i : Fin ν.length, Nat.factorial (colHook ν (i : ℕ)) :=
    Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin ν.length))
      fun i : Fin ν.length => Nat.factorial (colHook ν (i : ℕ))
  rw [h1, h2, Fin.prod_univ_eq_prod_range fun r => Nat.factorial (colHook ν r)]

/-! ### The product of the hook lengths of a row, indexed by `Fin (length ν)` -/

/-- The rows below the row `i.rev` are indexed by the elements of `Fin (length ν)` that are
smaller than `i`. -/
lemma prod_colHook_sub_eq_prod_Iio (i : Fin ν.length) :
    ∏ s ∈ Finset.Ico ((i.rev : ℕ) + 1) ν.length,
        (colHook ν (i.rev : ℕ) - colHook ν s)
      = ∏ j ∈ Finset.Iio i, (frobVec ν.length ν i - frobVec ν.length ν j) := by
  have hi : ((i.rev : Fin ν.length) : ℕ) = ν.length - ((i : ℕ) + 1) := Fin.val_rev i
  have hilt : (i : ℕ) < ν.length := i.isLt
  refine (Finset.prod_nbij (fun j : Fin ν.length => ((j.rev : Fin ν.length) : ℕ))
    ?_ ?_ ?_ ?_).symm
  · intro j hj
    rw [Finset.mem_Iio] at hj
    have h2 : ((j.rev : Fin ν.length) : ℕ) = ν.length - ((j : ℕ) + 1) := Fin.val_rev j
    have h4 : (j : ℕ) < (i : ℕ) := hj
    simp only [Finset.mem_Ico]
    omega
  · intro a _ b _ hab
    simp only at hab
    have h2 : ((a.rev : Fin ν.length) : ℕ) = ν.length - ((a : ℕ) + 1) := Fin.val_rev a
    have h3 : ((b.rev : Fin ν.length) : ℕ) = ν.length - ((b : ℕ) + 1) := Fin.val_rev b
    have h4 : (a : ℕ) < ν.length := a.isLt
    have h5 : (b : ℕ) < ν.length := b.isLt
    exact Fin.ext (by omega)
  · intro s hs
    rw [Finset.coe_Ico, Set.mem_Ico] at hs
    refine ⟨(⟨s, by omega⟩ : Fin ν.length).rev, ?_, ?_⟩
    · have h2 : ((⟨s, by omega⟩ : Fin ν.length).rev : ℕ) = ν.length - (s + 1) :=
        Fin.val_rev ⟨s, by omega⟩
      simp only [Finset.coe_Iio, Set.mem_Iio, Fin.lt_def]
      omega
    · have h2 : ((⟨s, by omega⟩ : Fin ν.length).rev : ℕ) = ν.length - (s + 1) :=
        Fin.val_rev ⟨s, by omega⟩
      have h3 : (((⟨s, by omega⟩ : Fin ν.length).rev.rev : Fin ν.length) : ℕ)
          = ν.length - (((⟨s, by omega⟩ : Fin ν.length).rev : ℕ) + 1) :=
        Fin.val_rev (⟨s, by omega⟩ : Fin ν.length).rev
      simp only
      omega
  · intro j _
    rw [frobVec_eq_colHook, frobVec_eq_colHook]

/-! ### The product of all the hook lengths -/

/-- The product of the factorials of the first column hook lengths of `ν` is the product of
all the hook lengths of `ν`, times the product of the differences of the first column hook
lengths. -/
theorem prod_factorial_frobVec_eq (hν : IsPart ν) :
    ∏ i : Fin ν.length, Nat.factorial (frobVec ν.length ν i)
      = hookProd ν * ∏ i : Fin ν.length, ∏ j ∈ Finset.Iio i,
          (frobVec ν.length ν i - frobVec ν.length ν j) := by
  have hrow : ∀ i : Fin ν.length,
      rowHookProd ν (i.rev : ℕ)
          * ∏ j ∈ Finset.Iio i, (frobVec ν.length ν i - frobVec ν.length ν j)
        = Nat.factorial (frobVec ν.length ν i) := by
    intro i
    rw [← prod_colHook_sub_eq_prod_Iio i, frobVec_eq_colHook]
    exact rowHookProd_mul_prod_colHook_sub hν (Fin.is_lt _)
  have hhook : ∏ i : Fin ν.length, rowHookProd ν (i.rev : ℕ) = hookProd ν := by
    have h2 : ∏ i : Fin ν.length, rowHookProd ν (i.rev : ℕ)
        = ∏ i : Fin ν.length, rowHookProd ν (i : ℕ) :=
      Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin ν.length))
        fun i : Fin ν.length => rowHookProd ν (i : ℕ)
    rw [h2, Fin.prod_univ_eq_prod_range fun r => rowHookProd ν r, hookProd]
  calc ∏ i : Fin ν.length, Nat.factorial (frobVec ν.length ν i)
      = ∏ i : Fin ν.length, (rowHookProd ν (i.rev : ℕ)
          * ∏ j ∈ Finset.Iio i, (frobVec ν.length ν i - frobVec ν.length ν j)) :=
        Finset.prod_congr rfl fun i _ => (hrow i).symm
    _ = hookProd ν * ∏ i : Fin ν.length, ∏ j ∈ Finset.Iio i,
          (frobVec ν.length ν i - frobVec ν.length ν j) := by
        rw [Finset.prod_mul_distrib, hhook]

/-- The product of the differences of the first column hook lengths is the Vandermonde
product. -/
theorem cast_prod_frobVec_sub (hν : IsPart ν) :
    ((∏ i : Fin ν.length, ∏ j ∈ Finset.Iio i,
        (frobVec ν.length ν i - frobVec ν.length ν j) : ℕ) : ℤ)
      = vdmProd fun i => ((frobVec ν.length ν i : ℕ) : ℤ) := by
  have hcast : ((∏ i : Fin ν.length, ∏ j ∈ Finset.Iio i,
      (frobVec ν.length ν i - frobVec ν.length ν j) : ℕ) : ℤ)
      = ∏ i : Fin ν.length, ∏ j ∈ Finset.Iio i,
          (((frobVec ν.length ν i : ℕ) : ℤ) - ((frobVec ν.length ν j : ℕ) : ℤ)) := by
    push_cast
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_Iio] at hj
    have := frobVec_lt_frobVec hν hj
    push_cast [Nat.cast_sub (le_of_lt this)]
    ring
  rw [hcast, vdmProd]
  exact Finset.prod_comm' (by simp)

/-- The differences of the first column hook lengths have a positive product. -/
lemma prod_frobVec_sub_pos (hν : IsPart ν) :
    0 < ∏ i : Fin ν.length, ∏ j ∈ Finset.Iio i,
      (frobVec ν.length ν i - frobVec ν.length ν j) := by
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
  rw [Finset.mem_Iio] at hj
  have := frobVec_lt_frobVec hν hj
  omega

/-! ### The hook length formula -/

/-- **The hook length formula**: the number of standard Young tableaux of shape a partition
`μ` of `n`, multiplied by the product of the hook lengths of the boxes of `μ`, is `n !`.
-/
theorem numStdTab_mul_hookProd (hν : IsPart ν) :
    numStdTab ν * hookProd ν = Nat.factorial ν.sum := by
  set D : ℕ := ∏ i : Fin ν.length, ∏ j ∈ Finset.Iio i,
    (frobVec ν.length ν i - frobVec ν.length ν j) with hD
  have hDpos : 0 < D := prod_frobVec_sub_pos hν
  have hDcast : (D : ℤ) = vdmProd fun i => ((frobVec ν.length ν i : ℕ) : ℤ) :=
    cast_prod_frobVec_sub hν
  have hfrob := numStdTab_mul_prod_factorial ν.length ν.sum ν hν le_rfl rfl
  rw [← hDcast, ← Nat.cast_prod, prod_factorial_frobVec_eq hν, ← hD] at hfrob
  have hcast : ((numStdTab ν * hookProd ν * D : ℕ) : ℤ)
      = ((Nat.factorial ν.sum * D : ℕ) : ℤ) := by
    push_cast at hfrob ⊢
    linarith
  exact Nat.eq_of_mul_eq_mul_right hDpos (by exact_mod_cast hcast)

/-- The number of standard Young tableaux of a shape which is a partition is positive. -/
lemma numStdTab_pos (hν : IsPart ν) : 0 < numStdTab ν :=
  Nat.pos_of_ne_zero fun h => Nat.factorial_ne_zero ν.sum <| by
    rw [← numStdTab_mul_hookProd hν, h, zero_mul]

/-- The product of the hook lengths of a partition is positive. -/
lemma hookProd_pos (hν : IsPart ν) : 0 < hookProd ν := by
  refine Finset.prod_pos fun r _ => Finset.prod_pos fun c hc => ?_
  rw [Finset.mem_range] at hc
  exact one_le_hookLength hν hc

/-- The product of the hook lengths of a partition of `n` divides `n !`. -/
lemma hookProd_dvd_factorial (hν : IsPart ν) : hookProd ν ∣ Nat.factorial ν.sum :=
  ⟨numStdTab ν, by rw [← numStdTab_mul_hookProd hν, Nat.mul_comm]⟩

/-- **The hook length formula**, in division form: the number of standard Young tableaux of
shape a partition `μ` of `n` is `n !` divided by the product of the hook lengths of the
boxes of `μ`. -/
theorem numStdTab_eq_factorial_div_hookProd (hν : IsPart ν) :
    numStdTab ν = Nat.factorial ν.sum / hookProd ν := by
  rw [← numStdTab_mul_hookProd hν, Nat.mul_div_cancel _ (hookProd_pos hν)]

end Young
