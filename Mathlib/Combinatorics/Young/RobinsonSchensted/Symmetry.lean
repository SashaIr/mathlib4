/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Plactic.Restrict
import Mathlib.Combinatorics.Young.Plactic.Standardization
import Mathlib.Combinatorics.Young.RobinsonSchensted.RestrictRecording
import Mathlib.Combinatorics.Young.Tableau.StandardRestrict
import Mathlib.Combinatorics.Young.Word.InverseStandardFilter

/-!
# Symmetry of the Robinson–Schensted correspondence

A Lean 4 port of the main theorems of `theories/LRrule/stdplact.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi): inverting a standard word exchanges
its insertion and recording tableaux (Coq `RSinvstdE` and `invseqRSPQE`).

The proof compares the two standard tableaux through the shapes of their restrictions.
The restriction of the insertion tableau `RS (invStd w)` to the letters `< k` is the
insertion tableau of the word obtained by keeping the letters `< k` of `invStd w`
(`List.RS_ltFilter`), that is of the inverse of the standardisation of the prefix
`w.take k` (`List.ltFilter_invStd`); since a standard word, its inverse and its
standardisation all have insertion tableaux of the same shape, this is the shape of
`RS (w.take k)`, which is the shape of the restriction of `RSQ w` to the letters `< k`
(`List.dropMax_RSQ`).  A standard tableau being determined by the shapes of its
restrictions (`List.eq_of_shape_dropMax_eq`), the two tableaux are equal.

## Main results

* `List.RS_invStd` : **the insertion tableau of the inverse of a standard word is the
  recording tableau of the word** (Coq `RSinvstdE`).
* `List.RSQ_invStd` : dually, the recording tableau of the inverse is the insertion
  tableau.
* `List.IsInvSeq.RS_eq_RSQ` : the same statement for a pair of inverse standard words
  (Coq `invseqRSPQE`).
-/

namespace List

open List

/-- **The insertion tableau of the inverse of a standard word is the recording tableau of
the word** (Coq `RSinvstdE`). -/
theorem RS_invStd {w : List ℕ} (hw : IsStd w) : RS (invStd w) = RSQ w := by
  refine eq_of_shape_dropMax_eq (isStdTab_RS (isStd_invStd hw)) (isStdTab_RSQ w) fun k => ?_
  rw [dropMax_RSQ, ← RS_ltFilter, ltFilter_invStd hw, shape_RS_invStd (std_isStd _),
    shape_RS_std, shape_RSQ]

/-- The recording tableau of the inverse of a standard word is its insertion tableau. -/
theorem RSQ_invStd {w : List ℕ} (hw : IsStd w) : RSQ (invStd w) = RS w := by
  have h := RS_invStd (isStd_invStd hw)
  rw [invStd_invStd hw] at h
  exact h.symm

/-- A word inverse to a standard word is its inverse. -/
theorem IsInvSeq.eq_invStd {u v : List ℕ} (hu : IsStd u) (h : IsInvSeq u v) :
    v = invStd u := by
  have hlen : v.length = (invStd u).length := by rw [length_invStd, h.1]
  refine List.ext_getElem hlen fun j hj hj' => ?_
  have hju : j < u.length := by rw [h.1]; exact hj
  have hi : u.idxOf j < u.length := hu.idxOf_lt hju
  obtain ⟨-, hv⟩ := h.2 _ hi
  rw [hu.getD_idxOf hju] at hv
  rw [← List.getD_eq_getElem _ 0 hj, ← List.getD_eq_getElem _ 0 hj', hv,
    getD_invStd hju]

/-- Two inverse standard words have exchanged insertion and recording tableaux
(Coq `invseqRSPQE`). -/
theorem IsInvSeq.RS_eq_RSQ {u v : List ℕ} (hu : IsStd u) (h : IsInvSeq u v) :
    RS v = RSQ u := by
  rw [h.eq_invStd hu]
  exact RS_invStd hu

end List
