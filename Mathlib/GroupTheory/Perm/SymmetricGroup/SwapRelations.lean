/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Algebra.Group.End
import Mathlib.Tactic.Group

/-!
# The Coxeter relations between transpositions

Following `theories/SymGroup/presentSn.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we check the two relations satisfied
by the transpositions of a set: two transpositions sharing exactly one point satisfy the
braid relation, and two transpositions with disjoint supports commute.

## Main results

* `Equiv.Perm.swap_mul_swap_pow_three` : `(swap a b * swap b c) ^ 3 = 1`.
* `Equiv.Perm.swap_mul_swap_comm` : transpositions with disjoint supports commute.
* `Equiv.Perm.swap_mul_swap_pow_two` : `(swap a b * swap c d) ^ 2 = 1` for disjoint supports.
-/

open Equiv

namespace Equiv.Perm


variable {α : Type*} [DecidableEq α]

/-- Two transpositions sharing exactly one point satisfy the braid relation, in the form
`(swap a b * swap b c) ^ 3 = 1`. -/
theorem swap_mul_swap_pow_three {a b c : α} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (Equiv.swap a b * Equiv.swap b c) ^ 3 = 1 := by
  have h1 : Equiv.swap a b * Equiv.swap b c * Equiv.swap a b = Equiv.swap a c := by
    have h := Equiv.swap_mul_swap_mul_swap (x := c) (y := b) (z := a) hbc.symm hac.symm
    rwa [Equiv.swap_comm b a, Equiv.swap_comm c b] at h
  have h2 : Equiv.swap b c * Equiv.swap a b * Equiv.swap b c = Equiv.swap a c := by
    have h := Equiv.swap_mul_swap_mul_swap (x := a) (y := b) (z := c) hab hac
    rwa [Equiv.swap_comm c a] at h
  calc (Equiv.swap a b * Equiv.swap b c) ^ 3
      = (Equiv.swap a b * Equiv.swap b c * Equiv.swap a b)
        * (Equiv.swap b c * Equiv.swap a b * Equiv.swap b c) := by
        simp only [pow_succ, pow_zero, one_mul]; group
    _ = 1 := by rw [h1, h2, Equiv.swap_mul_self]

/-- Two transpositions with disjoint supports commute. -/
theorem swap_mul_swap_comm {a b c d : α} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b := by
  have h : Equiv.swap a b * Equiv.swap c d * (Equiv.swap a b)⁻¹ = Equiv.swap c d := by
    have h := Equiv.swap_apply_apply (Equiv.swap a b) c d
    rw [Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm,
      Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm] at h
    exact h.symm
  calc Equiv.swap a b * Equiv.swap c d
      = (Equiv.swap a b * Equiv.swap c d * (Equiv.swap a b)⁻¹) * Equiv.swap a b := by group
    _ = Equiv.swap c d * Equiv.swap a b := by rw [h]

/-- Two transpositions with disjoint supports satisfy `(swap a b * swap c d) ^ 2 = 1`. -/
theorem swap_mul_swap_pow_two {a b c d : α} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : (Equiv.swap a b * Equiv.swap c d) ^ 2 = 1 := by
  calc (Equiv.swap a b * Equiv.swap c d) ^ 2
      = Equiv.swap a b * (Equiv.swap c d * Equiv.swap a b) * Equiv.swap c d := by
        simp only [pow_succ, pow_zero, one_mul]; group
    _ = 1 := by
        rw [← swap_mul_swap_comm hac had hbc hbd, ← mul_assoc, Equiv.swap_mul_self, one_mul,
          Equiv.swap_mul_self]

end Equiv.Perm
