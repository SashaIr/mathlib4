/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.HookLength.Branching
public import Mathlib.Combinatorics.Young.HookLength.Vandermonde

/-!
# The Frobenius formula for the number of standard Young tableaux

Let `μ` be a partition of `n` with at most `N` parts and let

`x_i = μ_{N - 1 - i} + i`,  `i = 0, …, N - 1`

be its *first column hook lengths*, read from the bottom row upwards (`Young.frobVec`).  The
number `f^μ` of standard Young tableaux of shape `μ` is then given by the Frobenius
formula

`f^μ · ∏_i x_i ! = n ! · ∏_{i < j} (x_j - x_i)`.

The proof is an induction on `n` using the branching rule
`Young.numStdTab_branching` and the shift identity `Young.sum_mul_vdmProd_update` for the
Vandermonde product: removing a removable corner from the row `N - 1 - i` of `μ` decreases
`x_i` by one, and the shapes for which this is not allowed contribute zero because the
resulting family has a repeated entry.

## Main definitions

* `Young.frobVec N μ` : the first column hook lengths of `μ`, padded to `N` rows.

## Main results

* `Young.numStdTab_mul_prod_factorial` : the Frobenius formula displayed above.
-/

@[expose] public section

namespace Young

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

/-- The first column hook lengths of the partition `μ`, padded to `N` rows and read from
the bottom row upwards: `frobVec N μ i = μ_{N - 1 - i} + i`.  These are `N` pairwise
distinct natural numbers which determine `μ`. -/
def frobVec (N : ℕ) (μ : List ℕ) (i : Fin N) : ℕ := μ.getD (i.rev : ℕ) 0 + (i : ℕ)

/-- The first column hook lengths of the empty partition. -/
lemma frobVec_nil (N : ℕ) (i : Fin N) : frobVec N [] i = (i : ℕ) := by
  simp [frobVec]

/-- The sum of the first column hook lengths. -/
lemma sum_frobVec {N : ℕ} {μ : List ℕ} (hN : μ.length ≤ N) :
    ∑ i : Fin N, frobVec N μ i = μ.sum + N.choose 2 := by
  have h1 : ∑ i : Fin N, frobVec N μ i
      = (∑ i : Fin N, μ.getD (i.rev : ℕ) 0) + ∑ i : Fin N, (i : ℕ) := by
    rw [← Finset.sum_add_distrib]
    rfl
  have h2 : ∑ i : Fin N, μ.getD (i.rev : ℕ) 0 = μ.sum :=
    calc ∑ i : Fin N, μ.getD (i.rev : ℕ) 0 = ∑ i : Fin N, μ.getD (i : ℕ) 0 :=
          Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin N)) fun i : Fin N => μ.getD (i : ℕ) 0
      _ = μ.sum := by
          rw [sum_eq_sum_range μ hN, ← Fin.sum_univ_eq_sum_range fun i => μ.getD i 0]
  have h3 : ∑ i : Fin N, (i : ℕ) = N.choose 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i), sum_range_id_eq_choose_two]
  rw [h1, h2, h3]

/-! ### Removing a removable corner -/

variable {N : ℕ} {μ : List ℕ} {r : Fin N}

/-- Removing a removable corner from the row `r` of `μ` decreases the first column hook
length of index `r.rev` by one and leaves the others unchanged. -/
lemma frobVec_decrNth (hμ : IsPart μ) (hc : IsRemCorner μ (r : ℕ)) :
    (fun p => ((frobVec N (decrNth μ (r : ℕ)) p : ℕ) : ℤ))
      = Function.update (fun p => ((frobVec N μ p : ℕ) : ℤ)) r.rev
          (((frobVec N μ r.rev : ℕ) : ℤ) - 1) := by
  have hpos : 0 < μ.getD (r : ℕ) 0 := by
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
    simp only [frobVec, getD_decrNth_of_ne hμ hc hne]

/-- Removing a removable corner divides the product of the factorials of the first column
hook lengths by the hook length of the row that lost a box. -/
lemma frobVec_prod_factorial_decrNth (hμ : IsPart μ) (hc : IsRemCorner μ (r : ℕ)) :
    frobVec N μ r.rev * ∏ p : Fin N, Nat.factorial (frobVec N (decrNth μ (r : ℕ)) p)
      = ∏ p : Fin N, Nat.factorial (frobVec N μ p) := by
  classical
  have hrev : ((r.rev : Fin N).rev : ℕ) = (r : ℕ) := by simp [Fin.rev_rev]
  have hpos : 0 < μ.getD (r : ℕ) 0 := by
    rw [IsRemCorner] at hc; omega
  have hval : frobVec N (decrNth μ (r : ℕ)) r.rev + 1 = frobVec N μ r.rev := by
    simp only [frobVec, hrev, getD_decrNth_self]
    omega
  have hother : ∀ p : Fin N, p ≠ r.rev →
      frobVec N (decrNth μ (r : ℕ)) p = frobVec N μ p := by
    intro p hp
    have hne : (r : ℕ) ≠ (p.rev : ℕ) := by
      intro h
      apply hp
      have : p.rev = r := Fin.ext h.symm
      rw [← Fin.rev_rev p, this]
    simp only [frobVec, getD_decrNth_of_ne hμ hc hne]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ r.rev),
    ← Finset.mul_prod_erase _ (fun p => Nat.factorial (frobVec N μ p)) (Finset.mem_univ r.rev),
    ← mul_assoc]
  congr 1
  · rw [← hval, Nat.factorial_succ]
  · exact Finset.prod_congr rfl fun p hp => by
      rw [hother p (Finset.mem_erase.1 hp).1]

/-- If the row `r` of `μ` has no removable corner, then decreasing the corresponding first
column hook length by one produces a repetition, so the corresponding term of the shift
identity vanishes. -/
lemma frobVec_term_eq_zero_of_not_remCorner (hμ : IsPart μ) (hN : μ.length ≤ N)
    (hc : ¬ IsRemCorner μ (r : ℕ)) :
    ((frobVec N μ r.rev : ℕ) : ℤ)
        * vdmProd (Function.update (fun p => ((frobVec N μ p : ℕ) : ℤ)) r.rev
          (((frobVec N μ r.rev : ℕ) : ℤ) - 1)) = 0 := by
  classical
  set i : Fin N := r.rev with hi
  have hirev : ((i.rev : Fin N) : ℕ) = (r : ℕ) := by simp [hi, Fin.rev_rev]
  have heq : μ.getD ((r : ℕ) + 1) 0 = μ.getD (r : ℕ) 0 := by
    have hle : μ.getD ((r : ℕ) + 1) 0 ≤ μ.getD (r : ℕ) 0 :=
      hμ.getD_antitone (Nat.le_succ _)
    rw [IsRemCorner] at hc
    omega
  rcases Nat.eq_zero_or_pos (frobVec N μ i) with hzero | hpos
  · rw [hzero]
    simp
  · have hi0 : 0 < (i : ℕ) := by
      by_contra h
      have hi0' : (i : ℕ) = 0 := by omega
      have hr : (r : ℕ) = N - 1 := by
        have := Fin.val_rev i
        rw [hi, Fin.rev_rev] at this
        omega
      have hμr : μ.getD (r : ℕ) 0 = 0 := by
        have hlen : μ.length ≤ (r : ℕ) + 1 := by omega
        have : μ.getD ((r : ℕ) + 1) 0 = 0 := List.getD_eq_default _ _ hlen
        omega
      simp only [frobVec, hirev, hμr, hi0'] at hpos
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
    have hjval : frobVec N μ j = μ.getD ((r : ℕ) + 1) 0 + ((i : ℕ) - 1) := by
      rw [frobVec, hjrev, hjv]
    have hival : frobVec N μ i = μ.getD (r : ℕ) 0 + (i : ℕ) := by
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
    rintro ⟨Q, hQ, hν⟩
    rcases Q with _ | ⟨q, Qs⟩
    · rfl
    · simp [shape] at hν
  refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨[], ?_, rfl⟩⟩⟩
  · rw [hnil a, hnil b]
  · exact ⟨isTableau_nil, by simp [IsStd]⟩

/-! ### The Frobenius formula -/

/-- **The Frobenius formula**: the number of standard Young tableaux of shape `μ`,
multiplied by the product of the factorials of the first column hook lengths of `μ`
(padded to `N ≥ length μ` rows), is `|μ| !` times the Vandermonde product of the first
column hook lengths. -/
theorem numStdTab_mul_prod_factorial (N : ℕ) :
    ∀ (n : ℕ) (μ : List ℕ), IsPart μ → μ.length ≤ N → μ.sum = n →
      (numStdTab μ : ℤ) * ∏ i : Fin N, ((Nat.factorial (frobVec N μ i) : ℕ) : ℤ)
        = ((Nat.factorial n : ℕ) : ℤ) * vdmProd (fun i => ((frobVec N μ i : ℕ) : ℤ)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro μ hμ hlen hsum
    match n, hsum with
    | 0, hsum =>
      have hnil : μ = [] := by
        have := hμ.length_le_sum
        rw [hsum] at this
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      simp only [numStdTab_nil, Nat.factorial_zero, Nat.cast_one, one_mul]
      simp only [frobVec_nil]
      rw [vdmProd_id N]
    | (m + 1), hsum =>
      classical
      set x : Fin N → ℤ := fun i => ((frobVec N μ i : ℕ) : ℤ) with hx
      set T : Fin N → ℤ := fun i => x i * vdmProd (Function.update x i (x i - 1)) with hT
      have hbranch : (numStdTab μ : ℤ) * ∏ i : Fin N, ((Nat.factorial (frobVec N μ i) : ℕ) : ℤ)
          = ∑ r : Fin N, ((Nat.factorial m : ℕ) : ℤ) * T r.rev := by
        rw [numStdTab_branching hμ hsum hlen, ← Fin.sum_univ_eq_sum_range
          (fun r => if IsRemCorner μ r then numStdTab (decrNth μ r) else 0)]
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun r _ => ?_
        by_cases hc : IsRemCorner μ (r : ℕ)
        · rw [ite_eq_left hc]
          have hρ : IsPart (decrNth μ (r : ℕ)) := isPart_decrNth hμ hc
          have hρlen : (decrNth μ (r : ℕ)).length ≤ N :=
            le_trans (included_decrNth μ (r : ℕ)).length_le hlen
          have hρsum : (decrNth μ (r : ℕ)).sum = m := by
            rw [sum_decrNth hμ hc, hsum]
            omega
          have hIH := ih m (by omega) (decrNth μ (r : ℕ)) hρ hρlen hρsum
          have hfact := frobVec_prod_factorial_decrNth (r := r) hμ hc
          have hcast : ((frobVec N μ r.rev : ℕ) : ℤ)
              * ∏ p : Fin N, ((Nat.factorial (frobVec N (decrNth μ (r : ℕ)) p) : ℕ) : ℤ)
              = ∏ p : Fin N, ((Nat.factorial (frobVec N μ p) : ℕ) : ℤ) := by
            rw [← Nat.cast_prod, ← Nat.cast_prod, ← Nat.cast_mul, hfact]
          calc ((numStdTab (decrNth μ (r : ℕ)) : ℕ) : ℤ)
                * ∏ p : Fin N, ((Nat.factorial (frobVec N μ p) : ℕ) : ℤ)
              = ((frobVec N μ r.rev : ℕ) : ℤ) * (((numStdTab (decrNth μ (r : ℕ)) : ℕ) : ℤ)
                * ∏ p : Fin N, ((Nat.factorial (frobVec N (decrNth μ (r : ℕ)) p) : ℕ) : ℤ)) := by
                rw [← hcast]; ring
            _ = ((frobVec N μ r.rev : ℕ) : ℤ) * (((Nat.factorial m : ℕ) : ℤ)
                * vdmProd (fun p => ((frobVec N (decrNth μ (r : ℕ)) p : ℕ) : ℤ))) := by
                rw [hIH]
            _ = ((Nat.factorial m : ℕ) : ℤ) * T r.rev := by
                rw [frobVec_decrNth hμ hc, hT]
                simp only [hx]
                ring
        · rw [ite_eq_right hc, hT]
          simp only [zero_mul, hx]
          rw [frobVec_term_eq_zero_of_not_remCorner hμ hlen hc, mul_zero]
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

end Young
