/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Word.Standardization
import Mathlib.Combinatorics.Young.RobinsonSchensted.InsertionTableau

/-!
# Standard tableaux

A Lean 4 port of the basic part of `theories/Combi/stdtab.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

A *standard tableau* is a Young tableau over `ℕ` whose reading word is a standard word,
that is, whose entries are exactly `0, …, n-1`.

## Main definitions

* `List.IsStdTab t` : `t` is a standard tableau (Coq `is_stdtab`).

## Main results

* `List.IsStd.of_perm` : being standard only depends on the multiset of letters.
* `List.IsStdTab.nodup_getD` : the rows of a standard tableau are duplicate-free.
* `List.isStdTab_RS` : the insertion tableau of a standard word is a standard tableau
  (Coq `RSstdE`).
* `List.isStdTab_RS_std` : the insertion tableau of the standardization of any word is a
  standard tableau.
* `List.mem_toWord_iff_of_isStdTab` : the entries of a standard tableau are exactly
  `0, …, n-1`, where `n` is its number of boxes.
-/

namespace List

open List

/-- A standard tableau: a tableau over `ℕ` whose reading word is standard
(Coq `is_stdtab`). -/
def IsStdTab (t : List (List ℕ)) : Prop := IsTableau t ∧ IsStd (toWord t)

instance decidableIsStdTab (t : List (List ℕ)) : Decidable (IsStdTab t) :=
  inferInstanceAs (Decidable (IsTableau t ∧ IsStd (toWord t)))

/-- Being a standard word only depends on the multiset of letters. -/
lemma IsStd.of_perm {u v : List ℕ} (h : IsStd u) (hp : v.Perm u) : IsStd v := by
  rw [IsStd, hp.length_eq]
  exact hp.trans h

/-- Coq `RSstdE`: the insertion tableau of a standard word is a standard tableau. -/
theorem isStdTab_RS {w : List ℕ} (h : IsStd w) : IsStdTab (RS w) :=
  ⟨isTableau_RS w, h.of_perm (perm_toWord_RS w)⟩

/-- The insertion tableau of the standardization of a word is a standard tableau. -/
theorem isStdTab_RS_std {T : Type*} [LinearOrder T] (w : List T) : IsStdTab (RS (std w)) :=
  isStdTab_RS (std_isStd w)

/-- The rows of a standard tableau are duplicate-free. -/
lemma IsStdTab.nodup_getD {t : List (List ℕ)} (h : IsStdTab t) (i : ℕ) :
    (t.getD i []).Nodup := by
  rcases Nat.lt_or_ge i t.length with hi | hi
  · have hnd : (toWord t).Nodup := h.2.nodup_iff.2 List.nodup_range
    refine hnd.sublist ?_
    rw [toWord]
    exact List.sublist_flatten_of_mem
      (by rw [List.getD_eq_getElem _ _ hi]; exact List.mem_reverse.2 (List.getElem_mem hi))
  · rw [List.getD_eq_default _ _ hi]; exact List.nodup_nil

/-- The shape of a standard tableau is a partition. -/
lemma isPart_shape_of_isStdTab {t : List (List ℕ)} (h : IsStdTab t) : IsPart (shape t) :=
  isPart_shape h.1

/-- The entries of a standard tableau are exactly `0, …, n-1`, where `n` is its size. -/
lemma mem_toWord_iff_of_isStdTab {t : List (List ℕ)} (h : IsStdTab t) (x : ℕ) :
    x ∈ toWord t ↔ x < sizeTab t := by
  have hperm : (toWord t).Perm (List.range (toWord t).length) := h.2
  rw [hperm.mem_iff, List.mem_range, length_toWord]

end List
