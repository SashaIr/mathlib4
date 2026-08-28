/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.HookLength.Frobenius
import Mathlib.Combinatorics.Young.HookLength.Basic

/-!
# The hook length formula

This file proves the **hook length formula**: the number `f^lam` of standard Young tableaux
of shape a partition `lam` of `n` is

`f^lam = n ! / ∏_{(i, j) ∈ lam} h(i, j)`,

where `h(i, j)` is the hook length of the box `(i, j)`.  It is stated in the division free
form `List.numStdTab_mul_hookProd`:

`f^lam · ∏_{(i, j) ∈ lam} h(i, j) = n !`.

The proof combines the Frobenius formula `List.numStdTab_mul_prod_factorial`, which computes
`f^lam` in terms of the first column hook lengths `x_i` of `lam`, with the identity
`List.rowHookProd_mul_prod_colHook_sub` between the hook lengths of a row and the first
column hook lengths: multiplying the latter over all the rows gives

`(∏ hook lengths) · ∏_{i < j} (x_j - x_i) = ∏_i x_i !`,

which is exactly what is needed to turn the Frobenius formula into the hook length formula.

## Main results

* `List.prod_factorial_frobVec_eq` : `∏_i x_i ! = (∏ hook lengths) · ∏_{i < j} (x_j - x_i)`.
* `List.numStdTab_mul_hookProd` : the hook length formula.
-/

namespace List

open List Finset

variable {sh : List ℕ}

/-! ### The first column hook lengths as a family indexed by `Fin (length sh)` -/

/-- The first column hook lengths of `List.frobVec` are those of `List.colHook`, read in
the reverse order. -/
lemma frobVec_eq_colHook (sh : List ℕ) (i : Fin sh.length) :
    frobVec sh.length sh i = colHook sh (i.rev : ℕ) := by
  have h1 : ((i.rev : Fin sh.length) : ℕ) = sh.length - ((i : ℕ) + 1) := Fin.val_rev i
  have h2 : (i : ℕ) < sh.length := i.isLt
  simp only [frobVec, colHook]
  omega

/-- The first column hook lengths increase with the index of `List.frobVec`. -/
lemma frobVec_lt_frobVec (hsh : IsPart sh) {i j : Fin sh.length} (hij : j < i) :
    frobVec sh.length sh j < frobVec sh.length sh i := by
  have hlt : ((i.rev : Fin sh.length) : ℕ) < ((j.rev : Fin sh.length) : ℕ) := by
    have h1 : ((i.rev : Fin sh.length) : ℕ) = sh.length - ((i : ℕ) + 1) := Fin.val_rev i
    have h2 : ((j.rev : Fin sh.length) : ℕ) = sh.length - ((j : ℕ) + 1) := Fin.val_rev j
    have h3 : (i : ℕ) < sh.length := i.isLt
    have h4 : (j : ℕ) < (i : ℕ) := hij
    omega
  rw [frobVec_eq_colHook, frobVec_eq_colHook]
  exact colHook_strictAnti hsh hlt (Fin.is_lt _)

/-- The product of the factorials of the first column hook lengths, indexed by rows. -/
lemma prod_factorial_frobVec_eq_prod_range (sh : List ℕ) :
    ∏ i : Fin sh.length, Nat.factorial (frobVec sh.length sh i)
      = ∏ r ∈ Finset.range sh.length, Nat.factorial (colHook sh r) := by
  have h1 : ∏ i : Fin sh.length, Nat.factorial (frobVec sh.length sh i)
      = ∏ i : Fin sh.length, Nat.factorial (colHook sh (i.rev : ℕ)) :=
    Finset.prod_congr rfl fun i _ => by rw [frobVec_eq_colHook]
  have h2 : ∏ i : Fin sh.length, Nat.factorial (colHook sh (i.rev : ℕ))
      = ∏ i : Fin sh.length, Nat.factorial (colHook sh (i : ℕ)) :=
    Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin sh.length))
      fun i : Fin sh.length => Nat.factorial (colHook sh (i : ℕ))
  rw [h1, h2, Fin.prod_univ_eq_prod_range fun r => Nat.factorial (colHook sh r)]

/-! ### The product of the hook lengths of a row, indexed by `Fin (length sh)` -/

/-- The rows below the row `i.rev` are indexed by the elements of `Fin (length sh)` that are
smaller than `i`. -/
lemma prod_colHook_sub_eq_prod_Iio (i : Fin sh.length) :
    ∏ s ∈ Finset.Ico ((i.rev : ℕ) + 1) sh.length,
        (colHook sh (i.rev : ℕ) - colHook sh s)
      = ∏ j ∈ Finset.Iio i, (frobVec sh.length sh i - frobVec sh.length sh j) := by
  have hi : ((i.rev : Fin sh.length) : ℕ) = sh.length - ((i : ℕ) + 1) := Fin.val_rev i
  have hilt : (i : ℕ) < sh.length := i.isLt
  refine (Finset.prod_nbij (fun j : Fin sh.length => ((j.rev : Fin sh.length) : ℕ))
    ?_ ?_ ?_ ?_).symm
  · intro j hj
    rw [Finset.mem_Iio] at hj
    have h2 : ((j.rev : Fin sh.length) : ℕ) = sh.length - ((j : ℕ) + 1) := Fin.val_rev j
    have h4 : (j : ℕ) < (i : ℕ) := hj
    simp only [Finset.mem_Ico]
    omega
  · intro a _ b _ hab
    simp only at hab
    have h2 : ((a.rev : Fin sh.length) : ℕ) = sh.length - ((a : ℕ) + 1) := Fin.val_rev a
    have h3 : ((b.rev : Fin sh.length) : ℕ) = sh.length - ((b : ℕ) + 1) := Fin.val_rev b
    have h4 : (a : ℕ) < sh.length := a.isLt
    have h5 : (b : ℕ) < sh.length := b.isLt
    exact Fin.ext (by omega)
  · intro s hs
    rw [Finset.coe_Ico, Set.mem_Ico] at hs
    refine ⟨(⟨s, by omega⟩ : Fin sh.length).rev, ?_, ?_⟩
    · have h2 : ((⟨s, by omega⟩ : Fin sh.length).rev : ℕ) = sh.length - (s + 1) :=
        Fin.val_rev ⟨s, by omega⟩
      simp only [Finset.coe_Iio, Set.mem_Iio, Fin.lt_def]
      omega
    · have h2 : ((⟨s, by omega⟩ : Fin sh.length).rev : ℕ) = sh.length - (s + 1) :=
        Fin.val_rev ⟨s, by omega⟩
      have h3 : (((⟨s, by omega⟩ : Fin sh.length).rev.rev : Fin sh.length) : ℕ)
          = sh.length - (((⟨s, by omega⟩ : Fin sh.length).rev : ℕ) + 1) :=
        Fin.val_rev (⟨s, by omega⟩ : Fin sh.length).rev
      simp only
      omega
  · intro j _
    rw [frobVec_eq_colHook, frobVec_eq_colHook]

/-! ### The product of all the hook lengths -/

/-- The product of the factorials of the first column hook lengths of `sh` is the product of
all the hook lengths of `sh`, times the product of the differences of the first column hook
lengths. -/
theorem prod_factorial_frobVec_eq (hsh : IsPart sh) :
    ∏ i : Fin sh.length, Nat.factorial (frobVec sh.length sh i)
      = hookProd sh * ∏ i : Fin sh.length, ∏ j ∈ Finset.Iio i,
          (frobVec sh.length sh i - frobVec sh.length sh j) := by
  have hrow : ∀ i : Fin sh.length,
      rowHookProd sh (i.rev : ℕ)
          * ∏ j ∈ Finset.Iio i, (frobVec sh.length sh i - frobVec sh.length sh j)
        = Nat.factorial (frobVec sh.length sh i) := by
    intro i
    rw [← prod_colHook_sub_eq_prod_Iio i, frobVec_eq_colHook]
    exact rowHookProd_mul_prod_colHook_sub hsh (Fin.is_lt _)
  have hhook : ∏ i : Fin sh.length, rowHookProd sh (i.rev : ℕ) = hookProd sh := by
    have h2 : ∏ i : Fin sh.length, rowHookProd sh (i.rev : ℕ)
        = ∏ i : Fin sh.length, rowHookProd sh (i : ℕ) :=
      Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin sh.length))
        fun i : Fin sh.length => rowHookProd sh (i : ℕ)
    rw [h2, Fin.prod_univ_eq_prod_range fun r => rowHookProd sh r, hookProd]
  calc ∏ i : Fin sh.length, Nat.factorial (frobVec sh.length sh i)
      = ∏ i : Fin sh.length, (rowHookProd sh (i.rev : ℕ)
          * ∏ j ∈ Finset.Iio i, (frobVec sh.length sh i - frobVec sh.length sh j)) :=
        Finset.prod_congr rfl fun i _ => (hrow i).symm
    _ = hookProd sh * ∏ i : Fin sh.length, ∏ j ∈ Finset.Iio i,
          (frobVec sh.length sh i - frobVec sh.length sh j) := by
        rw [Finset.prod_mul_distrib, hhook]

/-- The product of the differences of the first column hook lengths is the Vandermonde
product. -/
theorem cast_prod_frobVec_sub (hsh : IsPart sh) :
    ((∏ i : Fin sh.length, ∏ j ∈ Finset.Iio i,
        (frobVec sh.length sh i - frobVec sh.length sh j) : ℕ) : ℤ)
      = vdmProd fun i => ((frobVec sh.length sh i : ℕ) : ℤ) := by
  have hcast : ((∏ i : Fin sh.length, ∏ j ∈ Finset.Iio i,
      (frobVec sh.length sh i - frobVec sh.length sh j) : ℕ) : ℤ)
      = ∏ i : Fin sh.length, ∏ j ∈ Finset.Iio i,
          (((frobVec sh.length sh i : ℕ) : ℤ) - ((frobVec sh.length sh j : ℕ) : ℤ)) := by
    push_cast
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_Iio] at hj
    have := frobVec_lt_frobVec hsh hj
    push_cast [Nat.cast_sub (le_of_lt this)]
    ring
  rw [hcast, vdmProd]
  exact Finset.prod_comm' (by simp)

/-- The differences of the first column hook lengths have a positive product. -/
lemma prod_frobVec_sub_pos (hsh : IsPart sh) :
    0 < ∏ i : Fin sh.length, ∏ j ∈ Finset.Iio i,
      (frobVec sh.length sh i - frobVec sh.length sh j) := by
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
  rw [Finset.mem_Iio] at hj
  have := frobVec_lt_frobVec hsh hj
  omega

/-! ### The hook length formula -/

/-- **The hook length formula**: the number of standard Young tableaux of shape a partition
`lam` of `n`, multiplied by the product of the hook lengths of the boxes of `lam`, is `n !`.
-/
theorem numStdTab_mul_hookProd (hsh : IsPart sh) :
    numStdTab sh * hookProd sh = Nat.factorial sh.sum := by
  set D : ℕ := ∏ i : Fin sh.length, ∏ j ∈ Finset.Iio i,
    (frobVec sh.length sh i - frobVec sh.length sh j) with hD
  have hDpos : 0 < D := prod_frobVec_sub_pos hsh
  have hDcast : (D : ℤ) = vdmProd fun i => ((frobVec sh.length sh i : ℕ) : ℤ) :=
    cast_prod_frobVec_sub hsh
  have hfrob := numStdTab_mul_prod_factorial sh.length sh.sum sh hsh le_rfl rfl
  rw [← hDcast, ← Nat.cast_prod, prod_factorial_frobVec_eq hsh, ← hD] at hfrob
  have hcast : ((numStdTab sh * hookProd sh * D : ℕ) : ℤ)
      = ((Nat.factorial sh.sum * D : ℕ) : ℤ) := by
    push_cast at hfrob ⊢
    linarith
  exact Nat.eq_of_mul_eq_mul_right hDpos (by exact_mod_cast hcast)

/-- The product of the hook lengths of a partition is positive. -/
lemma hookProd_pos (hsh : IsPart sh) : 0 < hookProd sh := by
  refine Finset.prod_pos fun r _ => Finset.prod_pos fun c hc => ?_
  rw [Finset.mem_range] at hc
  exact one_le_hookLength hsh hc

/-- The product of the hook lengths of a partition of `n` divides `n !`. -/
lemma hookProd_dvd_factorial (hsh : IsPart sh) : hookProd sh ∣ Nat.factorial sh.sum :=
  ⟨numStdTab sh, by rw [← numStdTab_mul_hookProd hsh, Nat.mul_comm]⟩

/-- **The hook length formula**, in division form: the number of standard Young tableaux of
shape a partition `lam` of `n` is `n !` divided by the product of the hook lengths of the
boxes of `lam`. -/
theorem numStdTab_eq_factorial_div_hookProd (hsh : IsPart sh) :
    numStdTab sh = Nat.factorial sh.sum / hookProd sh := by
  rw [← numStdTab_mul_hookProd hsh, Nat.mul_div_cancel _ (hookProd_pos hsh)]

end List
