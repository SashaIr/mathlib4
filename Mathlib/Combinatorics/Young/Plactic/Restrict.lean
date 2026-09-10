/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Plactic.Monoid
public import Mathlib.Combinatorics.Young.Plactic.RobinsonSchensted
public import Mathlib.Combinatorics.Young.Tableau.Restrict

/-!
# Restricting a word to its small letters

Keeping only the letters `< N` of a word is compatible with Knuth (plactic) equivalence,
because an elementary Knuth transformation either keeps its three letters or removes the
largest of them from both words.  Consequently the insertion tableau of the restricted
word is the restriction of the insertion tableau (Coq `filter_gtnX_RS` in
`theories/LRrule/plactic.v` of [Coq-Combi](https://github.com/math-comp/Coq-Combi)).

## Main results

* `Young.placticEquiv_ltFilter` : Knuth equivalent words have Knuth equivalent
  restrictions.
* `Young.toWord_dropMax` : the reading word of the restriction of a tableau is the
  restriction of its reading word.
* `Young.RS_ltFilter` : **`RS (ltFilter N w) = dropMax N (RS w)`**.
-/

@[expose] public section

namespace Young

open List

variable {N : ℕ}

/-- An elementary Knuth transformation restricts to a Knuth equivalence between the
restrictions of the two words. -/
lemma placticEquiv_ltFilter_of_placticStep {u v : List ℕ} (h : PlacticStep u v) :
    PlacticEquiv (ltFilter N u) (ltFilter N v) := by
  cases h with
  | @knuthAC x y z hxy hyz c1 c2 =>
    by_cases hz : z < N
    · have hy : y < N := hyz.trans hz
      have hx : x < N := lt_of_le_of_lt hxy hy
      simp only [ltFilter, List.filter_append, List.filter_cons, hx, hy, hz, decide_true,
        ite_true]
      exact (PlacticStep.knuthAC hxy hyz _ _).plactic
    · simp only [ltFilter, List.filter_append, List.filter_cons, hz, decide_false]
      by_cases hx : x < N <;> by_cases hy : y < N <;>
        simp [hx, hy, PlacticEquiv.refl]
  | @knuthCA x y z hxy hyz c1 c2 =>
    by_cases hz : z < N
    · have hy : y < N := lt_of_le_of_lt hyz hz
      have hx : x < N := hxy.trans hy
      simp only [ltFilter, List.filter_append, List.filter_cons, hx, hy, hz, decide_true,
        ite_true]
      exact (PlacticStep.knuthCA hxy hyz _ _).plactic
    · simp only [ltFilter, List.filter_append, List.filter_cons, hz, decide_false]
      by_cases hx : x < N <;> by_cases hy : y < N <;>
        simp [hx, hy, PlacticEquiv.refl]

/-- Knuth equivalent words have Knuth equivalent restrictions. -/
theorem placticEquiv_ltFilter {u v : List ℕ} (h : PlacticEquiv u v) :
    PlacticEquiv (ltFilter N u) (ltFilter N v) := by
  induction h with
  | rel _ _ hstep => exact placticEquiv_ltFilter_of_placticStep hstep
  | refl _ => exact PlacticEquiv.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- Restricting a concatenation restricts each factor. -/
lemma ltFilter_append (N : ℕ) (a b : List ℕ) :
    ltFilter N (a ++ b) = ltFilter N a ++ ltFilter N b := List.filter_append _ _

/-- If all the rows of a tableau have no letter `< N`, its reading word has none either. -/
lemma ltFilter_toWord_eq_nil {P : List (List ℕ)} (h : ∀ r ∈ P, ltFilter N r = []) :
    ltFilter N (toWord P) = [] := by
  induction P with
  | nil => simp [toWord]
  | cons r P ih =>
    have hr : ltFilter N r = [] := h r (by simp)
    have hP : ∀ s ∈ P, ltFilter N s = [] := fun s hs => h s (by simp [hs])
    have htoWord : toWord (r :: P) = toWord P ++ r := by
      simp [toWord, List.reverse_cons]
    rw [htoWord, ltFilter_append, ih hP, hr]
    rfl

/-- The reading word of the restriction of a tableau is the restriction of its reading
word. -/
theorem toWord_dropMax {P : List (List ℕ)} (hP : IsTableau P) (N : ℕ) :
    toWord (dropMax N P) = ltFilter N (toWord P) := by
  induction P with
  | nil => simp [toWord]
  | cons r P ih =>
    have htoWord : toWord (r :: P) = toWord P ++ r := by
      simp [toWord, List.reverse_cons]
    have hPtab : IsTableau P := hP.2.2.2
    rw [dropMax_cons, htoWord, ltFilter_append]
    split_ifs with hr
    · have hall : ∀ s ∈ P, ltFilter N s = [] := by
        intro s hs
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
        have h0 : ltFilter N ((r :: P).getD 0 []) = [] := hr
        have := ltFilter_eq_nil_of_le hP (Nat.zero_le (i + 1)) h0
        rwa [List.getD_eq_getElem _ _ (by simpa using hi)] at this
      rw [ltFilter_toWord_eq_nil hall, hr]
      simp [toWord]
    · have h2 : toWord (ltFilter N r :: dropMax N P) = toWord (dropMax N P) ++ ltFilter N r := by
        simp [toWord, List.reverse_cons]
      rw [h2, ih hPtab]

/-- **The insertion tableau of the letters `< N` of a word is the restriction to the
letters `< N` of its insertion tableau.** -/
theorem RS_ltFilter (N : ℕ) (w : List ℕ) : RS (ltFilter N w) = dropMax N (RS w) := by
  have hP : IsTableau (RS w) := isTableau_RS w
  have h1 : PlacticEquiv (ltFilter N w) (ltFilter N (toWord (RS w))) :=
    placticEquiv_ltFilter (plactic_toWord_RS w).symm
  rw [← toWord_dropMax hP N, placticEquiv_iff_RS_eq] at h1
  rw [h1, RS_toWord (isTableau_dropMax hP)]

end Young
