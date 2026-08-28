/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Word.Yamanouchi
import Mathlib.Combinatorics.Young.RobinsonSchensted.Bijection

/-!
# Standard tableaux and Yamanouchi words

A Lean 4 port of the correspondence between standard tableaux and Yamanouchi words of
`theories/Combi/stdtab.v` from [Coq-Combi](https://github.com/math-comp/Coq-Combi).

Reading off, from the largest label down to the smallest, the row in which each label of a
standard tableau sits produces a Yamanouchi word, whose evaluation is the shape of the
tableau.  This is a bijection between standard tableaux with `n` boxes and Yamanouchi
words of length `n`.

## Main definitions

* `List.yamOfStdTab Q` : the Yamanouchi word of a standard tableau (Coq `yam_of_stdtab`).
* `List.stdTabOfYam y` : the standard tableau of a Yamanouchi word
  (Coq `stdtab_of_yam`).

## Main results

* `List.stdTabOfYam_spec` : the tableau of a Yamanouchi word is standard, its shape is
  the evaluation of the word, and its recording word is the reversed word.
* `List.yamOfStdTab_spec` : the word of a standard tableau is Yamanouchi and its
  evaluation is the shape of the tableau.
* `List.stdTabEquivYam` : standard tableaux with `n` boxes are in bijection with
  Yamanouchi words of length `n` (Coq `stdtab_of_yamK` / `yam_of_stdtabK`).
-/

namespace List

open List

/-- The Yamanouchi word of a standard tableau: the rows of the labels, read from the
largest label to the smallest (Coq `yam_of_stdtab`). -/
def yamOfStdTab (Q : List (List ℕ)) : List ℕ := (rowsOf Q).reverse

/-- The standard tableau of a Yamanouchi word (Coq `stdtab_of_yam`). -/
def stdTabOfYam (y : List ℕ) : List (List ℕ) := recTab y.reverse

@[simp] lemma yamOfStdTab_nil : yamOfStdTab [] = [] := rfl

@[simp] lemma stdTabOfYam_nil : stdTabOfYam [] = [] := rfl

lemma length_yamOfStdTab (Q : List (List ℕ)) : (yamOfStdTab Q).length = sizeTab Q := by
  simp [yamOfStdTab, rowsOf]

lemma sizeTab_recTab (rows : List ℕ) : sizeTab (recTab rows) = rows.length := by
  rw [← length_toWord, (perm_toWord_recTab rows).length_eq, List.length_range]

lemma sizeTab_stdTabOfYam (y : List ℕ) : sizeTab (stdTabOfYam y) = y.length := by
  rw [stdTabOfYam, sizeTab_recTab, List.length_reverse]

/-- The tableau of a Yamanouchi word is a standard tableau whose shape is the evaluation
of the word, and its recording word is the reversed word. -/
theorem stdTabOfYam_spec {y : List ℕ} (h : IsYam y) :
    IsStdTab (stdTabOfYam y) ∧ shape (stdTabOfYam y) = evalseq y ∧
      rowsOf (stdTabOfYam y) = y.reverse := by
  induction y with
  | nil => exact ⟨⟨trivial, by simp [IsStd, toWord]⟩, rfl, rfl⟩
  | cons i y ih =>
    obtain ⟨hstd, hshape, hrows⟩ := ih h.2
    set q := stdTabOfYam y with hq
    have hexp : stdTabOfYam (i :: y) = addBox q i y.length := by
      rw [stdTabOfYam, List.reverse_cons, recTab_concat, List.length_reverse, hq, stdTabOfYam]
    have hc : IsAddCorner (evalseq y) i := isAddCorner_evalseq h
    have hqlen : q.length = (evalseq y).length := by
      have := congrArg List.length hshape
      rwa [length_shape] at this
    have hi : i ≤ q.length := by
      rw [hqlen]
      exact le_length_of_isAddCorner hc
    have hsize : sizeTab q = y.length := by rw [hq, sizeTab_stdTabOfYam]
    have hlt : ∀ x ∈ toWord q, x < y.length := by
      intro x hx
      have := (mem_toWord_iff_of_isStdTab hstd x).1 hx
      omega
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hexp]
      exact isTableau_addBox hstd.1 hlt (by rw [hshape]; exact hc) hi
    · rw [stdTabOfYam]
      exact isStd_toWord_recTab _
    · rw [hexp, shape_addBox hi, hshape, evalseq_cons]
    · -- the recording word
      have hsizeadd : sizeTab (addBox q i y.length) = y.length + 1 := by
        rw [← hexp, sizeTab_stdTabOfYam, List.length_cons]
      have hmem : ∀ x, x < y.length → ∃ r ∈ q, x ∈ r := by
        intro x hx
        exact mem_toWord_iff.1 ((mem_toWord_iff_of_isStdTab hstd x).2 (by omega))
      have hnot : ∀ r ∈ q, y.length ∉ r := by
        intro r hr hcon
        have := hlt _ (mem_toWord_iff.2 ⟨r, hr, hcon⟩)
        omega
      rw [hexp, rowsOf, hsizeadd, List.range_succ, List.map_append]
      have h1 : (List.range y.length).map (rowIdx (addBox q i y.length)) =
          (List.range y.length).map (rowIdx q) := by
        refine List.map_congr_left ?_
        intro x hx
        rw [List.mem_range] at hx
        exact rowIdx_addBox_of_ne hi (by omega) (hmem x hx)
      rw [h1]
      simp only [List.map_cons, List.map_nil]
      rw [rowIdx_addBox_self hi hnot]
      have h3 : (List.range y.length).map (rowIdx q) = rowsOf q := by
        rw [rowsOf, hsize]
      rw [h3, hrows, List.reverse_cons]

/-- The word of a standard tableau is a Yamanouchi word whose evaluation is the shape of
the tableau. -/
theorem yamOfStdTab_spec {Q : List (List ℕ)} (h : IsStdTab Q) :
    IsYam (yamOfStdTab Q) ∧ evalseq (yamOfStdTab Q) = shape Q := by
  generalize hn : sizeTab Q = n
  induction n generalizing Q with
  | zero =>
    have h0 : Q = [] := h.1.eq_nil_of_sizeTab_eq_zero hn
    subst h0
    exact ⟨trivial, rfl⟩
  | succ n ih =>
    obtain ⟨hQ', hsize, hadd, hile⟩ := remBox_max_spec h hn
    obtain ⟨hyam, heval⟩ := ih hQ' hsize
    have hrows : yamOfStdTab Q = rowIdx Q n :: yamOfStdTab (remBox Q (rowIdx Q n)) := by
      rw [yamOfStdTab, rowsOf_eq_concat h hn, List.reverse_append]
      rfl
    have hshape : shape Q = incrNth (shape (remBox Q (rowIdx Q n))) (rowIdx Q n) := by
      nth_rewrite 1 [← hadd]
      exact shape_addBox hile n
    have heval' : evalseq (yamOfStdTab Q) = shape Q := by
      rw [hrows, evalseq_cons, heval, hshape]
    refine ⟨?_, heval'⟩
    rw [hrows] at heval' ⊢
    rw [isYam_cons]
    exact ⟨by rw [heval']; exact isPart_shape h.1, hyam⟩

/-! ### The bijection -/

/-- Coq `stdtab_of_yamK`. -/
theorem stdTabOfYam_yamOfStdTab {Q : List (List ℕ)} (h : IsStdTab Q) :
    stdTabOfYam (yamOfStdTab Q) = Q := by
  rw [stdTabOfYam, yamOfStdTab, List.reverse_reverse]
  exact recTab_rowsOf h

/-- Coq `yam_of_stdtabK`. -/
theorem yamOfStdTab_stdTabOfYam {y : List ℕ} (h : IsYam y) :
    yamOfStdTab (stdTabOfYam y) = y := by
  rw [yamOfStdTab, (stdTabOfYam_spec h).2.2, List.reverse_reverse]

/-- Standard tableaux with `n` boxes are in bijection with Yamanouchi words of length
`n`. -/
def stdTabEquivYam (n : ℕ) :
    {Q : List (List ℕ) // IsStdTab Q ∧ sizeTab Q = n} ≃ {y : List ℕ // IsYam y ∧ y.length = n}
    where
  toFun Q := ⟨yamOfStdTab Q.1, (yamOfStdTab_spec Q.2.1).1, by
    rw [length_yamOfStdTab, Q.2.2]⟩
  invFun y := ⟨stdTabOfYam y.1, (stdTabOfYam_spec y.2.1).1, by
    rw [sizeTab_stdTabOfYam, y.2.2]⟩
  left_inv Q := Subtype.ext (stdTabOfYam_yamOfStdTab Q.2.1)
  right_inv y := Subtype.ext (yamOfStdTab_stdTabOfYam y.2.1)

end List
