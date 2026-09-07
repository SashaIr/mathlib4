/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.HookLength.Branching
import Mathlib.Combinatorics.Young.HookLength.Vandermonde

/-!
# The Frobenius formula for the number of standard Young tableaux

Let `lam` be a partition of `n` with at most `N` parts and let

`x_i = lam_{N - 1 - i} + i`,  `i = 0, …, N - 1`

be its *first column hook lengths*, read from the bottom row upwards (`List.frobVec`).  The
number `f^lam` of standard Young tableaux of shape `lam` is then given by the Frobenius
formula

`f^lam · ∏_i x_i ! = n ! · ∏_{i < j} (x_j - x_i)`.

The proof is an induction on `n` using the branching rule
`List.numStdTab_branching` and the shift identity `List.sum_mul_vdmProd_update` for the
Vandermonde product: removing a removable corner from the row `N - 1 - i` of `lam` decreases
`x_i` by one, and the shapes for which this is not allowed contribute zero because the
resulting family has a repeated entry.

## Main definitions

* `List.frobVec N lam` : the first column hook lengths of `lam`, padded to `N` rows.

## Main results

* `List.numStdTab_mul_prod_factorial` : the Frobenius formula displayed above.
-/

namespace List

open List Finset

/-! ### The Vandermonde product of a family with a repetition -/

/-- The Vandermonde product of a family with two equal entries vanishes. -/
lemma vdmProd_eq_zero_of_eq {N : ℕ} {u : Fin N → ℤ} {p q : Fin N} (hpq : p < q)
    (h : u p = u q) : vdmProd u = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ p) ?_
  exact Finset.prod_eq_zero (Finset.mem_Ioi.2 hpq) (by rw [h, sub_self])

/-- The Vandermonde product of `0, 1, …, N - 1` is the product of the factorials. -/
lemma vdmProd_id (N : ℕ) :
    vdmProd (fun i : Fin N => (i : ℤ)) = ∏ i : Fin N, ((Nat.factorial (i : ℕ) : ℕ) : ℤ) := by
  match N with
  | 0 => simp [vdmProd]
  | (n + 1) =>
    have hdet : (Matrix.vandermonde fun i : Fin (n + 1) => (i : ℤ)).det
        = (n.superFactorial : ℤ) := Matrix.det_vandermonde_id_eq_superFactorial n
    rw [Matrix.det_vandermonde] at hdet
    rw [vdmProd, hdet, ← Nat.prod_range_succ_factorial n, Nat.cast_prod,
      Fin.prod_univ_eq_prod_range (fun i => ((Nat.factorial i : ℕ) : ℤ))]

/-! ### The first column hook lengths -/

/-- The first column hook lengths of the partition `lam`, padded to `N` rows and read from
the bottom row upwards: `frobVec N lam i = lam_{N - 1 - i} + i`.  These are `N` pairwise
distinct natural numbers which determine `lam`. -/
def frobVec (N : ℕ) (lam : List ℕ) (i : Fin N) : ℕ := lam.getD (i.rev : ℕ) 0 + (i : ℕ)

/-- The first column hook lengths of the empty partition. -/
lemma frobVec_nil (N : ℕ) (i : Fin N) : frobVec N [] i = (i : ℕ) := by
  simp [frobVec]

/-- The sum of the first column hook lengths. -/
lemma sum_frobVec {N : ℕ} {lam : List ℕ} (hN : lam.length ≤ N) :
    ∑ i : Fin N, frobVec N lam i = lam.sum + N.choose 2 := by
  have h1 : ∑ i : Fin N, frobVec N lam i
      = (∑ i : Fin N, lam.getD (i.rev : ℕ) 0) + ∑ i : Fin N, (i : ℕ) := by
    rw [← Finset.sum_add_distrib]
    rfl
  have h2 : ∑ i : Fin N, lam.getD (i.rev : ℕ) 0 = lam.sum :=
    calc ∑ i : Fin N, lam.getD (i.rev : ℕ) 0 = ∑ i : Fin N, lam.getD (i : ℕ) 0 :=
          Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin N)) fun i : Fin N => lam.getD (i : ℕ) 0
      _ = lam.sum := by
          rw [sum_eq_sum_range lam hN, ← Fin.sum_univ_eq_sum_range fun i => lam.getD i 0]
  have h3 : ∑ i : Fin N, (i : ℕ) = N.choose 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i), sum_range_id_eq_choose_two]
  rw [h1, h2, h3]

/-! ### Removing a removable corner -/

variable {N : ℕ} {lam : List ℕ} {r : Fin N}

/-- Removing a removable corner from the row `r` of `lam` decreases the first column hook
length of index `r.rev` by one and leaves the others unchanged. -/
lemma frobVec_decrNth (hlam : IsPart lam) (hc : IsRemCorner lam (r : ℕ)) :
    (fun p => ((frobVec N (decrNth lam (r : ℕ)) p : ℕ) : ℤ))
      = Function.update (fun p => ((frobVec N lam p : ℕ) : ℤ)) r.rev
          (((frobVec N lam r.rev : ℕ) : ℤ) - 1) := by
  have hpos : 0 < lam.getD (r : ℕ) 0 := by
    rw [IsRemCorner] at hc; omega
  have hrr : ((r.rev.rev : Fin N) : ℕ) = (r : ℕ) := by rw [Fin.rev_rev]
  ext p
  by_cases hp : p = r.rev
  · subst hp
    rw [Function.update_self]
    simp only [frobVec, hrr, getD_decrNth_self]
    omega
  · rw [Function.update_of_ne hp]
    have hne : (r : ℕ) ≠ (p.rev : ℕ) := by
      intro h
      exact hp (by rw [← Fin.rev_rev p, show p.rev = r from Fin.ext h.symm])
    simp only [frobVec, getD_decrNth_of_ne hlam hc hne]

/-- Removing a removable corner divides the product of the factorials of the first column
hook lengths by the hook length of the row that lost a box. -/
lemma frobVec_prod_factorial_decrNth (hlam : IsPart lam) (hc : IsRemCorner lam (r : ℕ)) :
    frobVec N lam r.rev * ∏ p : Fin N, Nat.factorial (frobVec N (decrNth lam (r : ℕ)) p)
      = ∏ p : Fin N, Nat.factorial (frobVec N lam p) := by
  classical
  have hrev : ((r.rev : Fin N).rev : ℕ) = (r : ℕ) := by simp [Fin.rev_rev]
  have hpos : 0 < lam.getD (r : ℕ) 0 := by
    rw [IsRemCorner] at hc; omega
  have hval : frobVec N (decrNth lam (r : ℕ)) r.rev + 1 = frobVec N lam r.rev := by
    simp only [frobVec, hrev, getD_decrNth_self]
    omega
  have hother : ∀ p : Fin N, p ≠ r.rev →
      frobVec N (decrNth lam (r : ℕ)) p = frobVec N lam p := by
    intro p hp
    have hne : (r : ℕ) ≠ (p.rev : ℕ) := by
      intro h
      apply hp
      have : p.rev = r := Fin.ext h.symm
      rw [← Fin.rev_rev p, this]
    simp only [frobVec, getD_decrNth_of_ne hlam hc hne]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ r.rev),
    ← Finset.mul_prod_erase _ (fun p => Nat.factorial (frobVec N lam p)) (Finset.mem_univ r.rev),
    ← mul_assoc]
  congr 1
  · rw [← hval, Nat.factorial_succ]
  · exact Finset.prod_congr rfl fun p hp => by
      rw [hother p (Finset.mem_erase.1 hp).1]

/-- If the row `r` of `lam` has no removable corner, then decreasing the corresponding first
column hook length by one produces a repetition, so the corresponding term of the shift
identity vanishes. -/
lemma frobVec_term_eq_zero_of_not_remCorner (hlam : IsPart lam) (hN : lam.length ≤ N)
    (hc : ¬ IsRemCorner lam (r : ℕ)) :
    ((frobVec N lam r.rev : ℕ) : ℤ)
        * vdmProd (Function.update (fun p => ((frobVec N lam p : ℕ) : ℤ)) r.rev
          (((frobVec N lam r.rev : ℕ) : ℤ) - 1)) = 0 := by
  classical
  set i : Fin N := r.rev with hi
  have hirev : ((i.rev : Fin N) : ℕ) = (r : ℕ) := by simp [hi, Fin.rev_rev]
  have heq : lam.getD ((r : ℕ) + 1) 0 = lam.getD (r : ℕ) 0 := by
    have hle : lam.getD ((r : ℕ) + 1) 0 ≤ lam.getD (r : ℕ) 0 :=
      hlam.getD_antitone (Nat.le_succ _)
    rw [IsRemCorner] at hc
    omega
  rcases Nat.eq_zero_or_pos (frobVec N lam i) with hzero | hpos
  · rw [hzero]
    simp
  · have hi0 : 0 < (i : ℕ) := by
      by_contra h
      have hi0' : (i : ℕ) = 0 := by omega
      have hr : (r : ℕ) = N - 1 := by
        have := Fin.val_rev i
        rw [hi, Fin.rev_rev] at this
        omega
      have hlamr : lam.getD (r : ℕ) 0 = 0 := by
        have hlen : lam.length ≤ (r : ℕ) + 1 := by omega
        have : lam.getD ((r : ℕ) + 1) 0 = 0 := List.getD_eq_default _ _ hlen
        omega
      simp only [frobVec, hirev, hlamr, hi0'] at hpos
      omega
    obtain ⟨j, hjv⟩ : ∃ j : Fin N, (j : ℕ) = (i : ℕ) - 1 := ⟨⟨(i : ℕ) - 1, by omega⟩, rfl⟩
    have hjrev : ((j.rev : Fin N) : ℕ) = (r : ℕ) + 1 := by
      have h1 := Fin.val_rev i
      have h2 := Fin.val_rev j
      have h3 : (i : ℕ) < N := i.isLt
      omega
    have hjne : j ≠ i := by
      intro h
      have : (j : ℕ) = (i : ℕ) := congrArg Fin.val h
      omega
    have hjlt : j < i := by
      rw [Fin.lt_def]
      omega
    refine mul_eq_zero_of_right _ (vdmProd_eq_zero_of_eq hjlt ?_)
    rw [Function.update_of_ne hjne, Function.update_self]
    have hjval : frobVec N lam j = lam.getD ((r : ℕ) + 1) 0 + ((i : ℕ) - 1) := by
      rw [frobVec, hjrev, hjv]
    have hival : frobVec N lam i = lam.getD (r : ℕ) 0 + (i : ℕ) := by
      simp only [frobVec, hirev]
    rw [hjval, hival, heq]
    have : (1 : ℤ) ≤ (i : ℕ) := by exact_mod_cast hi0
    push_cast [Nat.cast_sub hi0]
    ring

/-! ### The number of standard tableaux of the empty shape -/

/-- There is exactly one standard tableau with no box. -/
lemma numStdTab_nil : numStdTab ([] : List ℕ) = 1 := by
  rw [numStdTab]
  have hnil : ∀ Q : {Q : List (List ℕ) // IsStdTab Q ∧ shape Q = []}, Q.1 = [] := by
    rintro ⟨Q, hQ, hsh⟩
    rcases Q with _ | ⟨q, Qs⟩
    · rfl
    · simp [shape] at hsh
  refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨[], ?_, rfl⟩⟩⟩
  · rw [hnil a, hnil b]
  · exact ⟨isTableau_nil, by simp [IsStd]⟩

/-! ### The Frobenius formula -/

/-- **The Frobenius formula**: the number of standard Young tableaux of shape `lam`,
multiplied by the product of the factorials of the first column hook lengths of `lam`
(padded to `N ≥ length lam` rows), is `|lam| !` times the Vandermonde product of the first
column hook lengths. -/
theorem numStdTab_mul_prod_factorial (N : ℕ) :
    ∀ (n : ℕ) (lam : List ℕ), IsPart lam → lam.length ≤ N → lam.sum = n →
      (numStdTab lam : ℤ) * ∏ i : Fin N, ((Nat.factorial (frobVec N lam i) : ℕ) : ℤ)
        = ((Nat.factorial n : ℕ) : ℤ) * vdmProd (fun i => ((frobVec N lam i : ℕ) : ℤ)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro lam hlam hlen hsum
    match n, hsum with
    | 0, hsum =>
      have hnil : lam = [] := by
        have := hlam.length_le_sum
        rw [hsum] at this
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      simp only [numStdTab_nil, Nat.factorial_zero, Nat.cast_one, one_mul]
      simp only [frobVec_nil]
      rw [vdmProd_id N]
    | (m + 1), hsum =>
      classical
      set x : Fin N → ℤ := fun i => ((frobVec N lam i : ℕ) : ℤ) with hx
      set T : Fin N → ℤ := fun i => x i * vdmProd (Function.update x i (x i - 1)) with hT
      have hbranch : (numStdTab lam : ℤ) * ∏ i : Fin N, ((Nat.factorial (frobVec N lam i) : ℕ) : ℤ)
          = ∑ r : Fin N, ((Nat.factorial m : ℕ) : ℤ) * T r.rev := by
        rw [numStdTab_branching hlam hsum hlen, ← Fin.sum_univ_eq_sum_range
          (fun r => if IsRemCorner lam r then numStdTab (decrNth lam r) else 0)]
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun r _ => ?_
        by_cases hc : IsRemCorner lam (r : ℕ)
        · rw [ite_eq_left hc]
          have hnu : IsPart (decrNth lam (r : ℕ)) := isPart_decrNth hlam hc
          have hnulen : (decrNth lam (r : ℕ)).length ≤ N :=
            le_trans (included_decrNth lam (r : ℕ)).length_le hlen
          have hnusum : (decrNth lam (r : ℕ)).sum = m := by
            rw [sum_decrNth hlam hc, hsum]
            omega
          have hIH := ih m (by omega) (decrNth lam (r : ℕ)) hnu hnulen hnusum
          have hfact := frobVec_prod_factorial_decrNth (r := r) hlam hc
          have hcast : ((frobVec N lam r.rev : ℕ) : ℤ)
              * ∏ p : Fin N, ((Nat.factorial (frobVec N (decrNth lam (r : ℕ)) p) : ℕ) : ℤ)
              = ∏ p : Fin N, ((Nat.factorial (frobVec N lam p) : ℕ) : ℤ) := by
            rw [← Nat.cast_prod, ← Nat.cast_prod, ← Nat.cast_mul, hfact]
          calc ((numStdTab (decrNth lam (r : ℕ)) : ℕ) : ℤ)
                * ∏ p : Fin N, ((Nat.factorial (frobVec N lam p) : ℕ) : ℤ)
              = ((frobVec N lam r.rev : ℕ) : ℤ) * (((numStdTab (decrNth lam (r : ℕ)) : ℕ) : ℤ)
                * ∏ p : Fin N, ((Nat.factorial (frobVec N (decrNth lam (r : ℕ)) p) : ℕ) : ℤ)) := by
                rw [← hcast]; ring
            _ = ((frobVec N lam r.rev : ℕ) : ℤ) * (((Nat.factorial m : ℕ) : ℤ)
                * vdmProd (fun p => ((frobVec N (decrNth lam (r : ℕ)) p : ℕ) : ℤ))) := by
                rw [hIH]
            _ = ((Nat.factorial m : ℕ) : ℤ) * T r.rev := by
                rw [frobVec_decrNth hlam hc, hT]
                simp only [hx]
                ring
        · rw [ite_eq_right hc, hT]
          simp only [zero_mul, hx]
          rw [frobVec_term_eq_zero_of_not_remCorner hlam hlen hc, mul_zero]
      have hrevsum : ∑ i : Fin N, T i.rev = ∑ i : Fin N, T i :=
        Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin N)) T
      rw [hbranch, ← Finset.mul_sum, hrevsum, hT]
      simp only
      rw [sum_mul_vdmProd_update x]
      have hsumx : ∑ i : Fin N, x i = ((m + 1 : ℕ) : ℤ) + (N.choose 2 : ℤ) := by
        simp only [hx]
        rw [← Nat.cast_sum, sum_frobVec hlen, hsum]
        push_cast
        ring
      rw [hsumx]
      have : ((Nat.factorial (m + 1) : ℕ) : ℤ) = ((Nat.factorial m : ℕ) : ℤ) * ((m : ℤ) + 1) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [this]
      push_cast
      ring

end List
