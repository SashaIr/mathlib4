/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Plactic.Standardization
public import Mathlib.Combinatorics.Young.RobinsonSchensted.RestrictRecording
public import Mathlib.Combinatorics.Young.RobinsonSchensted.Symmetry
public import Mathlib.Combinatorics.Young.Tableau.StandardRestrict
public import Mathlib.Combinatorics.Young.Word.StandardizationCongr

/-!
# The recording tableau of a standardized word

Standardizing a word does not change its recording tableau, because the recording tableau
of a word is determined by the shapes of the insertion tableaux of its prefixes, and those
are unchanged by standardization.  Together with the symmetry of the Robinson–Schensted
correspondence this gives Coq `RSinvstdE` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi): the insertion tableau of the inverse of
the standardized word is the recording tableau of the word.

## Main results

* `List.RSQ_std` : `RSQ (std w) = RSQ w`.
* `List.RS_invStd_std` : **`RS (invStd (std w)) = RSQ w`** (Coq `RSinvstdE`).
-/

@[expose] public section

namespace List

variable {T : Type*} [LinearOrder T]

/-- Standardizing a word does not change its recording tableau. -/
theorem RSQ_std (w : List T) : RSQ (std w) = RSQ w := by
  refine eq_of_shape_dropMax_eq (isStdTab_RSQ _) (isStdTab_RSQ _) fun k => ?_
  rw [dropMax_RSQ, dropMax_RSQ, shape_RSQ, shape_RSQ, ← shape_RS_std ((std w).take k),
    ← shape_RS_std (w.take k), std_take_std]

/-- **The insertion tableau of the inverse of the standardized word is the recording
tableau** (Coq `RSinvstdE`). -/
theorem RS_invStd_std (w : List T) : RS (invStd (std w)) = RSQ w := by
  rw [RS_invStd (std_isStd w), RSQ_std]

end List
