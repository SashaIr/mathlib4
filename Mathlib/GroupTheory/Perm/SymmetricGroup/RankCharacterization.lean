/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.Perm.SymmetricGroup.Rank

/-!
# Characterisation of the rank functions of permutations

Following `theories/SymGroup/Bruhat.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we characterise the functions
`M : ℕ → ℕ → ℕ` which are the rank function `Equiv.Perm.permRank s` of a permutation `s` of
`Fin n`: they are the functions vanishing on the two first lines, taking the values
`min i n` and `min j n` on the two lines of index `n`, nondecreasing in each argument,
submodular, and constant beyond `n` in each argument.  This is the Coq predicate
`is_pmxsum`, and the main result `Equiv.Perm.isPermRankFun_iff` is the Coq `is_pmxsumP`.

The proof recovers the permutation matrix from `M` by the second difference
`Equiv.Perm.permRankDiff M i j` (Coq `mxdiff`): submodularity says that these differences are
nonnegative, the boundary conditions say that they sum to one along every line and every
column, hence they are the entries of a permutation matrix.

## Main definitions and results

* `Equiv.Perm.permRankDiff M i j` : the second difference of `M` at `(i, j)` (Coq `mxdiff`).
* `Equiv.Perm.IsPermRankFun n M` : the conditions above (Coq `is_pmxsum`).
* `Equiv.Perm.isPermRankFun_permRank` : the rank function of a permutation satisfies them (Coq
  `mxsum_perm_mx_is_pmxsum`).
* `Equiv.Perm.isPermRankFun_iff` : conversely, a function satisfying them is the rank function
  of a unique permutation (Coq `is_pmxsumP`).
-/

open Equiv Finset

namespace Equiv.Perm


variable {n : ℕ} {M : ℕ → ℕ → ℕ}

/-- If a family of natural numbers sums to one, exactly one of its terms is one and the
others vanish. -/
lemma exists_unique_eq_one_of_sum_eq_one {ι : Type*} {s : Finset ι}
    {g : ι → ℕ} (h : ∑ x ∈ s, g x = 1) : ∃ a ∈ s, g a = 1 ∧ ∀ b ∈ s, b ≠ a → g b = 0 := by
  classical
  obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (f := g) (s := s) (by omega)
  have hsplit : ∑ x ∈ s.erase a, g x + g a = ∑ x ∈ s, g x := Finset.sum_erase_add s g ha
  have hga : g a = 1 := by omega
  refine ⟨a, ha, hga, fun b hb hba => ?_⟩
  have hzero : ∑ x ∈ s.erase a, g x = 0 := by omega
  exact (Finset.sum_eq_zero_iff.1 hzero) b (Finset.mem_erase.2 ⟨hba, hb⟩)

/-- The second difference of a function of two natural arguments, that is the entry
`M (i + 1) (j + 1) + M i j - M i (j + 1) - M (i + 1) j` of the Coq matrix `mxdiff M`. -/
def permRankDiff (M : ℕ → ℕ → ℕ) (i j : ℕ) : ℕ :=
  M (i + 1) (j + 1) + M i j - (M i (j + 1) + M (i + 1) j)

/-- The conditions characterising the rank functions of the permutations of `Fin n`
(Coq `is_pmxsum`). -/
structure IsPermRankFun (n : ℕ) (M : ℕ → ℕ → ℕ) : Prop where
  /-- `M` vanishes on the first line. -/
  zero_left : ∀ j, M 0 j = 0
  /-- `M` vanishes on the first column. -/
  zero_right : ∀ i, M i 0 = 0
  /-- The line of index `n` of `M` is `j ↦ min j n`. -/
  top_left : ∀ j, M n j = min j n
  /-- The column of index `n` of `M` is `i ↦ min i n`. -/
  top_right : ∀ i, M i n = min i n
  /-- `M` is nondecreasing in its first argument. -/
  mono_left : ∀ i j, M i j ≤ M (i + 1) j
  /-- `M` is nondecreasing in its second argument. -/
  mono_right : ∀ i j, M i j ≤ M i (j + 1)
  /-- `M` is submodular: its second differences are nonnegative. -/
  submodular : ∀ i j, M i (j + 1) + M (i + 1) j ≤ M (i + 1) (j + 1) + M i j
  /-- `M` is constant beyond `n` in its first argument. -/
  stab_left : ∀ i j, n ≤ i → M i j = M n j
  /-- `M` is constant beyond `n` in its second argument. -/
  stab_right : ∀ i j, n ≤ j → M i j = M i n

/-- The rank function of a permutation satisfies the conditions of `IsPermRankFun` (Coq
`mxsum_perm_mx_is_pmxsum`). -/
theorem isPermRankFun_permRank (s : Perm (Fin n)) : IsPermRankFun n (permRank s) where
  zero_left j := permRank_zero_left s j
  zero_right i := permRank_zero_right s i
  top_left j := permRank_top_left s j
  top_right i := permRank_top_right s i
  mono_left i j := permRank_mono_left s (Nat.le_succ i) j
  mono_right i j := permRank_mono_right s i (Nat.le_succ j)
  submodular i j := by
    rw [permRank_succ_left s i (j + 1), permRank_succ_left s i j]
    by_cases h : i < n
    · rw [dite_eq_left h, dite_eq_left h]
      by_cases hs : (s ⟨i, h⟩).val < j
      · rw [ite_eq_left hs, ite_eq_left (by omega)]
        omega
      · rw [ite_eq_right hs]
        omega
    · rw [dite_eq_right h, dite_eq_right h]
      omega
  stab_left i j hi := permRank_of_le_left s hi j
  stab_right i j hj := permRank_of_le_right s i hj

/-- The conditions of `IsPermRankFun` are invariant under transposition. -/
theorem IsPermRankFun.transpose (hM : IsPermRankFun n M) :
    IsPermRankFun n (fun i j => M j i) where
  zero_left j := hM.zero_right j
  zero_right i := hM.zero_left i
  top_left j := hM.top_right j
  top_right i := hM.top_left i
  mono_left i j := hM.mono_right j i
  mono_right i j := hM.mono_left j i
  submodular i j := by have := hM.submodular j i; omega
  stab_left i j hi := hM.stab_right j i hi
  stab_right i j hj := hM.stab_left j i hj

/-- The second differences of `M` are the increments of its lines (Coq `sum_mxdiff`). -/
theorem IsPermRankFun.sum_permRankDiff (hM : IsPermRankFun n M) (k j : ℕ) :
    ∑ l ∈ range j, permRankDiff M k l = M (k + 1) j - M k j := by
  induction j with
  | zero => simp [hM.zero_right]
  | succ j ih =>
    rw [Finset.sum_range_succ, ih, permRankDiff]
    have h1 := hM.mono_left k j
    have h2 := hM.mono_left k (j + 1)
    have h3 := hM.mono_right k j
    have h4 := hM.mono_right (k + 1) j
    have h5 := hM.submodular k j
    omega

/-- The transposed second difference. -/
lemma permRankDiff_transpose (M : ℕ → ℕ → ℕ) (i j : ℕ) :
    permRankDiff (fun i j => M j i) i j = permRankDiff M j i := by
  simp only [permRankDiff]
  omega

/-- The second differences of `M` sum to one along every line of index `k < n`. -/
theorem IsPermRankFun.sum_row (hM : IsPermRankFun n M) {k : ℕ} (hk : k < n) :
    ∑ l ∈ range n, permRankDiff M k l = 1 := by
  rw [hM.sum_permRankDiff k n, hM.top_right, hM.top_right]
  omega

/-- The second differences of `M` sum to one along every column of index `l < n`. -/
theorem IsPermRankFun.sum_col (hM : IsPermRankFun n M) {l : ℕ} (hl : l < n) :
    ∑ k ∈ range n, permRankDiff M k l = 1 := by
  have h := hM.transpose.sum_row hl
  simp only [permRankDiff_transpose] at h
  exact h

/-- Outside the square of size `n`, the second differences of `M` vanish. -/
theorem IsPermRankFun.permRankDiff_eq_zero (hM : IsPermRankFun n M) {k l : ℕ}
    (h : n ≤ k ∨ n ≤ l) : permRankDiff M k l = 0 := by
  rcases h with h | h
  · rw [permRankDiff, hM.stab_left k (l + 1) h, hM.stab_left (k + 1) (l + 1) (by omega),
      hM.stab_left k l h, hM.stab_left (k + 1) l (by omega)]
    omega
  · rw [permRankDiff, hM.stab_right (k + 1) (l + 1) (by omega), hM.stab_right k l h,
      hM.stab_right k (l + 1) (by omega), hM.stab_right (k + 1) l h]
    omega

/-- A function satisfying the conditions of `IsPermRankFun` is the rank function of a
permutation (Coq `is_pmxsumP`). -/
theorem exists_permRank_eq_of_isPermRankFun (hM : IsPermRankFun n M) :
    ∃ s : Perm (Fin n), M = permRank s := by
  classical
  have key : ∀ k : Fin n, ∃ l : Fin n,
      permRankDiff M k.val l.val = 1 ∧ ∀ l' : ℕ, l' ≠ l.val → permRankDiff M k.val l' = 0 := by
    intro k
    obtain ⟨l, hl, hl1, hl0⟩ :=
      exists_unique_eq_one_of_sum_eq_one (hM.sum_row k.isLt)
    refine ⟨⟨l, Finset.mem_range.1 hl⟩, hl1, fun l' hl' => ?_⟩
    by_cases hlt : l' < n
    · exact hl0 l' (Finset.mem_range.2 hlt) hl'
    · exact hM.permRankDiff_eq_zero (Or.inr (by omega))
  choose f hf1 hf0 using key
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    have hsum := hM.sum_col (f a).isLt
    have hpair : ({a.val, b.val} : Finset ℕ) ⊆ range n := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_range.2 a.isLt
      · exact Finset.mem_range.2 b.isLt
    have hab' : a.val ≠ b.val := fun h => hne (Fin.ext h)
    have hle : ∑ k ∈ ({a.val, b.val} : Finset ℕ), permRankDiff M k (f a).val
        ≤ ∑ k ∈ range n, permRankDiff M k (f a).val :=
      Finset.sum_le_sum_of_subset hpair
    have h1 : permRankDiff M a.val (f a).val = 1 := hf1 a
    have h2 : permRankDiff M b.val (f a).val = 1 := by rw [hab]; exact hf1 b
    rw [Finset.sum_pair hab', h1, h2] at hle
    omega
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), ?_⟩
  set s : Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj) with hs
  have hsf : ∀ k : Fin n, s k = f k := fun k => rfl
  have hstep : ∀ (i : ℕ) (hi : i < n) (j : ℕ),
      M (i + 1) j = M i j + if (f ⟨i, hi⟩).val < j then 1 else 0 := by
    intro i hi j
    have hsum := hM.sum_permRankDiff i j
    have hmono := hM.mono_left i j
    have hval : ∑ l ∈ range j, permRankDiff M i l
        = if (f ⟨i, hi⟩).val < j then 1 else 0 := by
      by_cases hlt : (f ⟨i, hi⟩).val < j
      · rw [ite_eq_left hlt]
        rw [Finset.sum_eq_single (f ⟨i, hi⟩).val]
        · exact hf1 ⟨i, hi⟩
        · intro l _ hl
          exact hf0 ⟨i, hi⟩ l hl
        · intro hmem
          exact absurd (Finset.mem_range.2 hlt) hmem
      · rw [ite_eq_right hlt]
        refine Finset.sum_eq_zero fun l hl => ?_
        exact hf0 ⟨i, hi⟩ l (by
          intro h
          exact hlt (h ▸ Finset.mem_range.1 hl))
    omega
  have hle : ∀ i ≤ n, ∀ j, M i j = permRank s i j := by
    intro i
    induction i with
    | zero => intro _ j; rw [hM.zero_left j, permRank_zero_left]
    | succ i ih =>
      intro hi j
      have hi' : i < n := by omega
      rw [hstep i hi' j, ih (by omega) j, permRank_succ_left, dite_eq_left hi', hsf ⟨i, hi'⟩]
  funext i j
  by_cases hi : i ≤ n
  · exact hle i hi j
  · rw [hM.stab_left i j (by omega), permRank_of_le_left s (by omega) j]
    exact hle n le_rfl j

/-- A function is the rank function of a permutation of `Fin n` if and only if it
satisfies the conditions of `IsPermRankFun` (Coq `is_pmxsumP`). -/
theorem isPermRankFun_iff : IsPermRankFun n M ↔ ∃ s : Perm (Fin n), M = permRank s := by
  refine ⟨exists_permRank_eq_of_isPermRankFun, ?_⟩
  rintro ⟨s, rfl⟩
  exact isPermRankFun_permRank s

end Equiv.Perm
