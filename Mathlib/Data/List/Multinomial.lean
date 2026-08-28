/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Multinomial coefficients of a list of natural numbers

This is a port of `theories/Combi/multinomial.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi).  The multinomial coefficient
`List.multinomialList s` of a list `s = [i₀, …, i_{k-1}]` of natural numbers is the number
of ways of splitting a set of `s.sum` elements into blocks of sizes `i₀, …, i_{k-1}`; it is
defined by the recursion `C[i :: s] = (i + s.sum).choose i * C[s]` (Coq `multinomial`).

## Main definitions and results

* `List.multinomialList` : the multinomial coefficient of a list (Coq `'C[s]`).
* `List.multinomialList_mul_prod_factorial` : `C[s] * ∏ i! = (s.sum)!` (Coq
  `multinomial_fact`).
* `List.multinomialList_eq_div` : `C[s] = (s.sum)! / ∏ i!` (Coq `multinomial_factd`).
* `List.multinomialList_append` : the multinomial coefficient of a concatenation (Coq
  `multinomial_cat`).
* `List.multinomialList_of_perm` : it only depends on the multiset of the entries (Coq
  `perm_multinomial`).
* `List.multinomialList_filter_ne_zero` : removing zero entries does not change it (Coq
  `multinomial_filter_neq0`).
* `List.multinomialList_eq_nat_multinomial` : it agrees with Mathlib's `Nat.multinomial`.
-/

namespace List

open Nat

/-- The multinomial coefficient of a list of natural numbers, defined by the recursion
`C[i :: s] = (i + s.sum).choose i * C[s]` (Coq `multinomial`). -/
def multinomialList : List ℕ → ℕ
  | [] => 1
  | i :: s => (i + s.sum).choose i * multinomialList s

@[simp] lemma multinomialList_nil : multinomialList [] = 1 := rfl

@[simp] lemma multinomialList_cons (i : ℕ) (s : List ℕ) :
    multinomialList (i :: s) = (i + s.sum).choose i * multinomialList s := rfl

lemma multinomialList_singleton (i : ℕ) : multinomialList [i] = 1 := by
  simp [multinomialList]

lemma multinomialList_pair (a b : ℕ) : multinomialList [a, b] = (a + b).choose a := by
  simp [multinomialList]

/-- **The multinomial coefficient counts the arrangements**: `C[s] * ∏ i! = (s.sum)!`
(Coq `multinomial_fact`). -/
theorem multinomialList_mul_prod_factorial (s : List ℕ) :
    multinomialList s * (s.map Nat.factorial).prod = Nat.factorial s.sum := by
  induction s with
  | nil => simp
  | cons i s ih =>
    have hle : i ≤ i + s.sum := Nat.le_add_right _ _
    have hchoose := Nat.choose_mul_factorial_mul_factorial hle
    rw [Nat.add_sub_cancel_left] at hchoose
    simp only [multinomialList_cons, List.map_cons, List.prod_cons, List.sum_cons]
    calc (i + s.sum).choose i * multinomialList s * (Nat.factorial i * (s.map Nat.factorial).prod)
        = (i + s.sum).choose i * Nat.factorial i *
            (multinomialList s * (s.map Nat.factorial).prod) := by ring
      _ = (i + s.sum).choose i * Nat.factorial i * Nat.factorial s.sum := by rw [ih]
      _ = Nat.factorial (i + s.sum) := hchoose

/-- The product of the factorials of the entries divides the factorial of the sum (Coq
`dvdn_prodfact`). -/
theorem prod_factorial_dvd_factorial_sum (s : List ℕ) :
    (s.map Nat.factorial).prod ∣ Nat.factorial s.sum :=
  ⟨multinomialList s, by rw [← multinomialList_mul_prod_factorial s]; ring⟩

lemma prod_factorial_pos (s : List ℕ) : 0 < (s.map Nat.factorial).prod := by
  refine List.prod_pos fun a ha => ?_
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 ha
  exact Nat.factorial_pos i

/-- The multinomial coefficient as a quotient of factorials (Coq `multinomial_factd`). -/
theorem multinomialList_eq_div (s : List ℕ) :
    multinomialList s = Nat.factorial s.sum / (s.map Nat.factorial).prod := by
  rw [← multinomialList_mul_prod_factorial s,
    Nat.mul_div_cancel _ (prod_factorial_pos s)]

/-- Two lists with the same entries up to permutation have the same multinomial
coefficient (Coq `perm_multinomial`). -/
theorem multinomialList_of_perm {s t : List ℕ} (h : s.Perm t) :
    multinomialList s = multinomialList t := by
  rw [multinomialList_eq_div, multinomialList_eq_div, h.sum_eq, (h.map Nat.factorial).prod_eq]

/-- The multinomial coefficient of a concatenation (Coq `multinomial_cat`). -/
theorem multinomialList_append (s t : List ℕ) :
    multinomialList (s ++ t)
      = (s.sum + t.sum).choose s.sum * multinomialList s * multinomialList t := by
  have key : multinomialList (s ++ t) * ((s ++ t).map Nat.factorial).prod
      = ((s.sum + t.sum).choose s.sum * multinomialList s * multinomialList t) *
        ((s ++ t).map Nat.factorial).prod := by
    rw [multinomialList_mul_prod_factorial, List.map_append, List.prod_append,
      List.sum_append]
    have hle : s.sum ≤ s.sum + t.sum := Nat.le_add_right _ _
    have hchoose := Nat.choose_mul_factorial_mul_factorial hle
    rw [Nat.add_sub_cancel_left] at hchoose
    calc Nat.factorial (s.sum + t.sum)
        = (s.sum + t.sum).choose s.sum * Nat.factorial s.sum * Nat.factorial t.sum := hchoose.symm
      _ = (s.sum + t.sum).choose s.sum *
            (multinomialList s * (s.map Nat.factorial).prod) *
            (multinomialList t * (t.map Nat.factorial).prod) := by
            rw [multinomialList_mul_prod_factorial, multinomialList_mul_prod_factorial]
      _ = (s.sum + t.sum).choose s.sum * multinomialList s * multinomialList t *
            ((s.map Nat.factorial).prod * (t.map Nat.factorial).prod) := by ring
  exact Nat.eq_of_mul_eq_mul_right (prod_factorial_pos (s ++ t)) key

/-- The multinomial coefficient of a constant list (Coq `multinomial_nseq`). -/
theorem multinomialList_replicate (n a : ℕ) :
    multinomialList (List.replicate n a) * (Nat.factorial a ^ n) = Nat.factorial (a * n) := by
  have hsum : (List.replicate n a).sum = a * n := by
    rw [List.sum_replicate, smul_eq_mul, Nat.mul_comm]
  have hprod : ((List.replicate n a).map Nat.factorial).prod = Nat.factorial a ^ n := by
    rw [List.map_replicate, List.prod_replicate]
  rw [← hprod, multinomialList_mul_prod_factorial, hsum]

/-- The number of orderings of `n` distinct elements (Coq `multinomial_nseq1`). -/
theorem multinomialList_replicate_one (n : ℕ) :
    multinomialList (List.replicate n 1) = Nat.factorial n := by
  have := multinomialList_replicate n 1
  simpa using this

/-- Removing the zero entries does not change the sum of a list. -/
lemma sum_filter_ne_zero (s : List ℕ) :
    (s.filter (fun i => decide (i ≠ 0))).sum = s.sum := by
  induction s with
  | nil => rfl
  | cons i s ih =>
    by_cases hi : i = 0
    · subst hi
      simpa using ih
    · rw [List.filter_cons_of_pos (by simpa using hi), List.sum_cons, List.sum_cons, ih]

/-- Removing the zero entries does not change the multinomial coefficient (Coq
`multinomial_filter_neq0`). -/
theorem multinomialList_filter_ne_zero (s : List ℕ) :
    multinomialList (s.filter (fun i => decide (i ≠ 0))) = multinomialList s := by
  induction s with
  | nil => rfl
  | cons i s ih =>
    by_cases hi : i = 0
    · subst hi
      simpa using ih
    · rw [List.filter_cons_of_pos (by simpa using hi), multinomialList_cons,
        multinomialList_cons, ih, sum_filter_ne_zero]

/-- The multinomial coefficient of a list agrees with Mathlib's `Nat.multinomial` over the
index set of the list. -/
theorem multinomialList_eq_nat_multinomial (s : List ℕ) :
    multinomialList s = Nat.multinomial Finset.univ (fun i : Fin s.length => s.get i) := by
  have hsum : ∑ i : Fin s.length, s.get i = s.sum := by
    rw [← List.sum_ofFn]
    congr 1
    exact List.ofFn_get s
  have hprod : ∏ i : Fin s.length, Nat.factorial (s.get i) = (s.map Nat.factorial).prod := by
    rw [← List.prod_ofFn]
    congr 1
    conv_rhs => rw [← List.ofFn_get s]
    rw [List.map_ofFn]
    rfl
  have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin s.length))
    (fun i => s.get i)
  rw [hsum, hprod] at hspec
  refine Nat.eq_of_mul_eq_mul_left (prod_factorial_pos s) ?_
  rw [hspec, mul_comm, multinomialList_mul_prod_factorial]

end List
