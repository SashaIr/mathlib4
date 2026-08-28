/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Combinatorics.Young.Tableau.Restrict

/-!
# Symmetry of the Kostka numbers

The Kostka number `K_{λ,c}` counting the tableaux of shape `λ` and content `c` does not
depend on the order of the letters: it is invariant under permuting the content vector.
This is the combinatorial heart of the symmetry of the Schur polynomials.

The proof is the classical one, using the Bender–Knuth style commutation of two steps of
the Pieri rule (`List.card_midSet_add_comm`): peeling off the two largest letters of a
tableau expresses the Kostka number as a sum over the shapes obtained after removing both
letters, weighted by the number of intermediate shapes, and this weight is symmetric in
the multiplicities of the two letters.

## Main results

* `List.kostkaNum_swap_top` : invariance under exchanging the multiplicities of the two
  largest letters.
* `List.kostkaNum_swap` : invariance under exchanging the multiplicities of two adjacent
  letters.
* `List.kostkaNum_permContent` : invariance under an arbitrary permutation of the letters.
-/

namespace List

open List

variable {N : ℕ} {sh : List ℕ} {c d : ℕ → ℕ} {m : ℕ}

/-- The Kostka number `kostkaNum N sh c` only depends on the values `c i` for `i < N`. -/
lemma kostkaNum_congr (N : ℕ) (sh : List ℕ) {c d : ℕ → ℕ} (h : ∀ i < N, c i = d i) :
    kostkaNum N sh c = kostkaNum N sh d := by
  have : tabSet N sh c = tabSet N sh d := by
    ext P
    simp only [tabSet, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, h3, fun i hi => (h4 i hi).trans (h i hi)⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, h3, fun i hi => (h4 i hi).trans (h i hi).symm⟩
  rw [kostkaNum, kostkaNum, this]

/-- A tableau of shape `sh` with letters `< N` has `sh.sum` boxes, so there is none unless
the content adds up to `sh.sum`. -/
lemma kostkaNum_eq_zero_of_sum_ne (N : ℕ) (sh : List ℕ) (c : ℕ → ℕ)
    (h : ∑ i ∈ Finset.range N, c i ≠ sh.sum) : kostkaNum N sh c = 0 := by
  have hempty : IsEmpty (tabSet N sh c) := by
    refine ⟨fun P => h ?_⟩
    obtain ⟨-, hsh, hlt, hcount⟩ := P.2
    rw [← hsh, ← length_flatten_eq_sum_shape, length_eq_sum_count hlt]
    exact Finset.sum_congr rfl fun i hi => (hcount i (Finset.mem_range.1 hi)).symm
  rw [kostkaNum, Nat.card_of_isEmpty]

/-- If there is an intermediate shape between `rho` and `lam`, then `rho ⊆ lam`. -/
lemma included_of_midSet_nonempty {lam rho : List ℕ} {s : ℕ}
    (h : (midSet lam rho s).Nonempty) : Included rho lam := by
  obtain ⟨nu, -, h1, h2, -⟩ := h
  exact h2.included.trans h1.included

open Classical in
/-- The cardinality of `midSet` as a sum over all partitions of `s`. -/
lemma card_midSet_eq_sum (lam rho : List ℕ) (s : ℕ) :
    Nat.card (midSet lam rho s) = ∑ nu : {p : List ℕ // IsPart p ∧ p.sum = s},
      if HorizStrip lam nu.1 ∧ HorizStrip nu.1 rho then 1 else 0 := by
  classical
  have hcard : Nat.card (midSet lam rho s)
      = Nat.card {nu : {p : List ℕ // IsPart p ∧ p.sum = s} //
          HorizStrip lam nu.1 ∧ HorizStrip nu.1 rho} := by
    refine Nat.card_congr ⟨fun nu => ⟨⟨nu.1, nu.2.1, nu.2.2.2.2⟩, nu.2.2.1, nu.2.2.2.1⟩,
      fun nu => ⟨nu.1.1, nu.1.2.1, nu.2.1, nu.2.2, nu.1.2.2⟩, ?_, ?_⟩
    · rintro ⟨nu, hnu⟩; rfl
    · rintro ⟨⟨nu, hnu⟩, h⟩; rfl
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

/-- Peeling off the two largest letters of a tableau. -/
theorem kostkaNum_two_step (hsh : IsPart sh) (h2 : m + c N + c (N + 1) = sh.sum) :
    kostkaNum (N + 2) sh c
      = ∑ rho : {p : List ℕ // IsPart p ∧ p.sum = m},
          Nat.card (midSet sh rho.1 (m + c N)) * kostkaNum N rho.1 c := by
  classical
  rw [kostkaNum_succ (N := N + 1) (m := m + c N) hsh (by omega)]
  have step : ∀ nu : {p : List ℕ // IsPart p ∧ p.sum = m + c N},
      (if HorizStrip sh nu.1 then kostkaNum (N + 1) nu.1 c else 0)
        = ∑ rho : {p : List ℕ // IsPart p ∧ p.sum = m},
            if HorizStrip sh nu.1 ∧ HorizStrip nu.1 rho.1 then kostkaNum N rho.1 c else 0 := by
    intro nu
    by_cases hstrip : HorizStrip sh nu.1
    · rw [if_pos hstrip, kostkaNum_succ nu.2.1 (by rw [nu.2.2])]
      refine Finset.sum_congr rfl fun rho _ => ?_
      by_cases h : HorizStrip nu.1 rho.1
      · rw [if_pos h, if_pos ⟨hstrip, h⟩]
      · rw [if_neg h, if_neg (show ¬ (HorizStrip sh nu.1 ∧ HorizStrip nu.1 rho.1) from
          fun hc => h hc.2)]
    · rw [if_neg hstrip]
      exact (Finset.sum_eq_zero fun rho _ => if_neg fun hc => hstrip hc.1).symm
  rw [Finset.sum_congr rfl fun nu _ => step nu, Finset.sum_comm]
  refine Finset.sum_congr rfl fun rho _ => ?_
  rw [card_midSet_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun nu _ => ?_
  by_cases h : HorizStrip sh nu.1 ∧ HorizStrip nu.1 rho.1
  · rw [if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h, zero_mul]

/-- Exchanging the multiplicities of the two largest letters does not change the Kostka
number. -/
theorem kostkaNum_swap_top (hsh : IsPart sh) {c d : ℕ → ℕ} (hlt : ∀ i < N, c i = d i)
    (hN : c N = d (N + 1)) (hN' : c (N + 1) = d N)
    (hsum : ∑ i ∈ Finset.range (N + 2), c i = sh.sum) :
    kostkaNum (N + 2) sh c = kostkaNum (N + 2) sh d := by
  classical
  set m := ∑ i ∈ Finset.range N, c i with hm
  have hcsum : m + c N + c (N + 1) = sh.sum := by
    rw [hm, ← hsum, Finset.sum_range_succ, Finset.sum_range_succ]
  have hdsum : m + d N + d (N + 1) = sh.sum := by omega
  rw [kostkaNum_two_step hsh hcsum, kostkaNum_two_step hsh hdsum]
  refine Finset.sum_congr rfl fun rho _ => ?_
  have hkos : kostkaNum N rho.1 c = kostkaNum N rho.1 d := kostkaNum_congr N rho.1 hlt
  rw [hkos]
  rcases Nat.eq_zero_or_pos (kostkaNum N rho.1 d) with h0 | -
  · rw [h0, mul_zero, mul_zero]
  congr 1
  rcases eq_or_ne (Nat.card (midSet sh rho.1 (m + c N))) 0 with hz | hz
  · rcases Set.eq_empty_or_nonempty (midSet sh rho.1 (m + d N)) with he | hne
    · rw [hz, he]; simp
    · have hsub : Included rho.1 sh := included_of_midSet_nonempty hne
      have := card_midSet_add_comm sh rho.1 rho.2.1 hsub (a := d N) (b := c N)
        (by rw [rho.2.2]; omega)
      rw [rho.2.2] at this
      rw [this, hz]
  · have hne : (midSet sh rho.1 (m + c N)).Nonempty := by
      rw [Nat.card_ne_zero] at hz
      obtain ⟨x⟩ := hz.1
      exact ⟨x.1, x.2⟩
    have hsub : Included rho.1 sh := included_of_midSet_nonempty hne
    have := card_midSet_add_comm sh rho.1 rho.2.1 hsub (a := c N) (b := d N)
      (by rw [rho.2.2]; omega)
    rw [rho.2.2] at this
    exact this

/-- Exchanging the multiplicities of two adjacent letters `k` and `k + 1` (both smaller
than `N`) does not change the Kostka number. -/
theorem kostkaNum_swap :
    ∀ (N : ℕ) (sh : List ℕ) (c d : ℕ → ℕ) (k : ℕ), IsPart sh → k + 1 < N →
      (∀ i, i ≠ k → i ≠ k + 1 → c i = d i) → c k = d (k + 1) → c (k + 1) = d k →
      ∑ i ∈ Finset.range N, c i = sh.sum →
      kostkaNum N sh c = kostkaNum N sh d := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro sh c d k hsh hk hne h1 h2 hsum
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hk) with heq | hlt
    · -- `k + 1 = N - 1`: the two largest letters
      obtain rfl : N = k + 2 := heq.symm
      exact kostkaNum_swap_top hsh (fun i hi => hne i (by omega) (by omega)) h1 h2 hsum
    · -- `k + 1 < N - 1`: peel off the largest letter and use the induction hypothesis
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      have hkM : k + 1 < M := by omega
      have hcM : c M = d M := hne M (by omega) (by omega)
      set m := ∑ i ∈ Finset.range M, c i with hm
      have hcsum : m + c M = sh.sum := by rw [hm, ← hsum, Finset.sum_range_succ]
      have hdsum : m + d M = sh.sum := by omega
      rw [kostkaNum_succ (N := M) (m := m) hsh hcsum, kostkaNum_succ (N := M) (m := m) hsh hdsum]
      refine Finset.sum_congr rfl fun nu _ => ?_
      by_cases hstrip : HorizStrip sh nu.1
      · rw [if_pos hstrip, if_pos hstrip]
        exact ih M (by omega) nu.1 c d k nu.2.1 hkM hne h1 h2 (by rw [nu.2.2])
      · rw [if_neg hstrip, if_neg hstrip]

/-! ### Invariance under an arbitrary permutation of the letters -/

/-- The content `c` with its first `N` letters permuted by `σ`. -/
def permContent (N : ℕ) (c : ℕ → ℕ) (σ : Equiv.Perm (Fin N)) : ℕ → ℕ :=
  fun i => if h : i < N then c (σ ⟨i, h⟩) else c i

@[simp] lemma permContent_one (N : ℕ) (c : ℕ → ℕ) : permContent N c 1 = c := by
  funext i
  simp only [permContent, Equiv.Perm.coe_one, id_eq]
  split <;> rfl

lemma permContent_mul (N : ℕ) (c : ℕ → ℕ) (σ τ : Equiv.Perm (Fin N)) :
    permContent N c (σ * τ) = permContent N (permContent N c σ) τ := by
  funext i
  simp only [permContent, Equiv.Perm.coe_mul, Function.comp_apply]
  by_cases h : i < N
  · rw [dif_pos h, dif_pos h, dif_pos (τ ⟨i, h⟩).2, Fin.eta]
  · rw [dif_neg h, dif_neg h, dif_neg h]

lemma sum_permContent (N : ℕ) (c : ℕ → ℕ) (σ : Equiv.Perm (Fin N)) :
    ∑ i ∈ Finset.range N, permContent N c σ i = ∑ i ∈ Finset.range N, c i := by
  rw [Finset.sum_range, Finset.sum_range]
  have h : ∀ i : Fin N, permContent N c σ i = c (σ i) := by
    intro i
    simp only [permContent, dif_pos i.2, Fin.eta]
  simp only [h]
  exact Equiv.sum_comp σ fun i : Fin N => c i

/-- **The Kostka numbers are symmetric**: permuting the letters does not change the number
of tableaux of a given shape and content. -/
theorem kostkaNum_permContent (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    ∀ (sh : List ℕ) (c : ℕ → ℕ), IsPart sh → ∑ i ∈ Finset.range N, c i = sh.sum →
      kostkaNum N sh (permContent N c σ) = kostkaNum N sh c := by
  cases N with
  | zero =>
    intro sh c _ _
    have : permContent 0 c σ = c := by
      funext i
      simp [permContent]
    rw [this]
  | succ n =>
    have hmem : σ ∈ Submonoid.closure
        (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top σ
    induction hmem using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro sh c hsh hsum
      refine kostkaNum_swap (n + 1) sh _ c i.1 hsh (by omega) ?_ ?_ ?_ ?_
      · intro j hj hj'
        simp only [permContent]
        split
        · rename_i h
          rw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff, hj])
            (by simp [Fin.ext_iff, Fin.val_succ, hj'])]
        · rfl
      · simp only [permContent, dif_pos (show i.1 < n + 1 by omega)]
        rw [show (⟨i.1, show i.1 < n + 1 by omega⟩ : Fin (n + 1)) = i.castSucc from rfl,
          Equiv.swap_apply_left]
        rfl
      · simp only [permContent, dif_pos (show i.1 + 1 < n + 1 by omega)]
        rw [show (⟨i.1 + 1, show i.1 + 1 < n + 1 by omega⟩ : Fin (n + 1)) = i.succ from rfl,
          Equiv.swap_apply_right]
        rfl
      · rw [sum_permContent, hsum]
    | one =>
      intro sh c _ _
      rw [permContent_one]
    | mul x y _ _ hx hy =>
      intro sh c hsh hsum
      rw [permContent_mul, hy sh _ hsh (by rw [sum_permContent, hsum]), hx sh c hsh hsum]

/-! ### Dependence only on the multiset of the content -/

/-- Two families of naturals indexed by `Fin N` with the same multiset of values differ by
a permutation of the indices. -/
lemma exists_perm_comp_eq {N : ℕ} {c d : Fin N → ℕ}
    (h : Finset.univ.val.map c = Finset.univ.val.map d) :
    ∃ σ : Equiv.Perm (Fin N), ∀ i, c (σ i) = d i := by
  classical
  have hc : ∀ (f : Fin N → ℕ) (v : ℕ),
      Fintype.card {i : Fin N // f i = v} = Multiset.count v (Finset.univ.val.map f) := by
    intro f v
    rw [Multiset.count_map, Fintype.card_subtype]
    simp [Finset.filter, eq_comm]
  have hcard : ∀ v : ℕ,
      Fintype.card {i : Fin N // d i = v} = Fintype.card {i : Fin N // c i = v} := by
    intro v
    rw [hc, hc, h]
  refine ⟨(Equiv.sigmaFiberEquiv d).symm.trans
      ((Equiv.sigmaCongrRight fun v => Fintype.equivOfCardEq (hcard v)).trans
        (Equiv.sigmaFiberEquiv c)), fun i => ?_⟩
  exact (Fintype.equivOfCardEq (hcard (d i)) ⟨i, rfl⟩).2

/-- **The Kostka number only depends on the multiset of the content**: two contents with
the same multiset of multiplicities give the same number of tableaux. -/
theorem kostkaNum_eq_of_multiset_eq (N : ℕ) (sh : List ℕ) (c d : ℕ → ℕ) (hsh : IsPart sh)
    (hsum : ∑ i ∈ Finset.range N, c i = sh.sum)
    (h : (Finset.univ.val.map fun i : Fin N => c i)
      = (Finset.univ.val.map fun i : Fin N => d i)) :
    kostkaNum N sh c = kostkaNum N sh d := by
  obtain ⟨σ, hσ⟩ := exists_perm_comp_eq h
  rw [← kostkaNum_permContent N σ sh c hsh hsum]
  refine kostkaNum_congr N sh fun i hi => ?_
  simpa [permContent, dif_pos hi] using hσ ⟨i, hi⟩

end List
