/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Plactic.Basic

/-!
# Restricting a word to its large letters

Keeping only the letters of a word that lie in an upper set is compatible with Knuth
(plactic) equivalence: an elementary Knuth transformation either keeps its three letters or
removes its smallest one, in which case the two words have the same restriction.  This is
the counterpart, for upper sets, of
`Mathlib.Combinatorics.Young.Plactic.Restrict`, and the Lean 4 port of
`plactic_filter_le` in `theories/LRrule/plactic.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

## Main results

* `List.placticEquiv_filter_of_isUpperSet` : Knuth equivalent words have Knuth equivalent
  restrictions to an upper set of letters.
-/

namespace List

variable {T : Type*} [LinearOrder T] {p : T → Bool}

/-- An elementary Knuth transformation restricts to a Knuth equivalence between the
restrictions of the two words to an upper set of letters. -/
lemma placticEquiv_filter_of_isUpperSet_of_placticStep
    (hp : ∀ x y : T, x ≤ y → p x → p y) {u v : List T} (h : PlacticStep u v) :
    PlacticEquiv (u.filter p) (v.filter p) := by
  cases h with
  | @knuthAC x y z hxy hyz a b =>
    by_cases hx : p x
    · have hy : p y := hp x y hxy hx
      have hz : p z := hp y z hyz.le hy
      simp only [List.filter_append, List.filter_cons, hx, hy, hz, if_true]
      exact (PlacticStep.knuthAC hxy hyz _ _).plactic
    · simp only [List.filter_append, List.filter_cons, hx]
      by_cases hy : p y <;> by_cases hz : p z <;> simp [hy, hz, PlacticEquiv.refl]
  | @knuthCA x y z hxy hyz a b =>
    by_cases hx : p x
    · have hy : p y := hp x y hxy.le hx
      have hz : p z := hp y z hyz hy
      simp only [List.filter_append, List.filter_cons, hx, hy, hz, if_true]
      exact (PlacticStep.knuthCA hxy hyz _ _).plactic
    · simp only [List.filter_append, List.filter_cons, hx]
      by_cases hy : p y <;> by_cases hz : p z <;> simp [hy, hz, PlacticEquiv.refl]

/-- Knuth equivalent words have Knuth equivalent restrictions to an upper set of letters
(Coq `plactic_filter_le`). -/
theorem placticEquiv_filter_of_isUpperSet (hp : ∀ x y : T, x ≤ y → p x → p y)
    {u v : List T} (h : PlacticEquiv u v) :
    PlacticEquiv (u.filter p) (v.filter p) := by
  induction h with
  | rel _ _ hstep => exact placticEquiv_filter_of_isUpperSet_of_placticStep hp hstep
  | refl _ => exact PlacticEquiv.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

end List
