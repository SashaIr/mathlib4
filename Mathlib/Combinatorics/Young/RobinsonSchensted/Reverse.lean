/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Greene.Reverse
public import Mathlib.Combinatorics.Young.Plactic.Restrict
public import Mathlib.Combinatorics.Young.Plactic.Standardization
public import Mathlib.Combinatorics.Young.Tableau.ConjugateRestrict
public import Mathlib.Combinatorics.Young.Tableau.StandardRestrict

/-!
# The insertion tableau of a reversed standard word

Reversing a standard word transposes its Robinson–Schensted insertion tableau (Coq
`RS_rev_uniq` of `theories/LRrule/Greene_inv.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi)).

The proof combines three results already available in the library: reversing a word with
distinct letters conjugates the shape of its insertion tableau
(`Young.shape_RS_reverse_of_nodup`), restricting a word to its letters `< k` restricts its
insertion tableau (`Young.RS_ltFilter`), transposing a standard tableau commutes with that
restriction (`Young.shape_dropMax_conjTab`), and a standard tableau is determined by the
shapes of its restrictions (`Young.eq_of_shape_dropMax_eq`).

## Main results

* `Young.RS_reverse` : `RS w.reverse = conjTab (RS w)` for a standard word `w`.
-/

@[expose] public section

namespace Young

open List

/-- Restricting to the letters `< N` commutes with reversing a word. -/
lemma ltFilter_reverse (N : ℕ) (w : List ℕ) : ltFilter N w.reverse = (ltFilter N w).reverse :=
  List.filter_reverse

/-- **The insertion tableau of a reversed standard word is the transpose of the insertion
tableau of the word** (Coq `RS_rev_uniq`). -/
theorem RS_reverse {w : List ℕ} (hw : IsStd w) : RS w.reverse = conjTab (RS w) := by
  have hstd : IsStdTab (RS w) := isStdTab_RS hw
  refine eq_of_shape_dropMax_eq (isStdTab_RS (IsStd.of_perm hw (List.reverse_perm w)))
    hstd.conjTab fun k => ?_
  rw [shape_dropMax_conjTab hstd, ← RS_ltFilter, ← RS_ltFilter, ltFilter_reverse]
  exact shape_RS_reverse_of_nodup ((IsStd.nodup hw).filter _)

end Young
