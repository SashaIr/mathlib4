/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Tableau.Restrict
import Mathlib.Combinatorics.Young.Word.Yamanouchi
import Mathlib.Combinatorics.Young.Plactic.RobinsonSchensted

/-!
# Yamanouchi words and plactic classes

A Lean 4 port of `theories/LRrule/Yam_plact.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

The Yamanouchi words of a given evaluation form a plactic class: being Yamanouchi is
invariant under the Knuth relations, and two Yamanouchi words are Knuth equivalent as
soon as they have the same evaluation.  The proof goes through the *Yamanouchi tableau*
`yamTab sh`, whose `i`-th row only contains the letter `i`; it is the unique tableau
whose reading word is Yamanouchi, and the insertion tableau of a Yamanouchi word `y` is
`yamTab (evalseq y)`.

## Main definitions

* `List.Dominant l` : every letter of `l` occurs at least as often as its successor.
* `List.yamTab sh` : the Yamanouchi tableau of shape `sh` (Coq `yamtab`).

## Main results

* `List.PlacticStep.isYam_iff`, `List.PlacticEquiv.isYam_iff` : being Yamanouchi is
  invariant under Knuth equivalence (Coq `is_yam_plactic`).
* `List.eq_yamTab_of_isYam_toWord` : a tableau whose reading word is Yamanouchi is a
  Yamanouchi tableau (Coq `yamtab_unique`).
* `List.RS_eq_yamTab` : the insertion tableau of a Yamanouchi word `y` is
  `yamTab (evalseq y)` (Coq `RS_yam`), and `List.shape_RS_of_isYam` : its shape is
  `evalseq y` (Coq `shape_RS_yam`).
* `List.placticEquiv_hyperYam` : a Yamanouchi word is Knuth equivalent to the
  hyperstandard Yamanouchi word of its evaluation (Coq `yam_plactic_hyper`).
* `List.isYam_placticEquiv_iff` : for a Yamanouchi word `y`, the words Knuth equivalent
  to `y` are exactly the Yamanouchi words of the same evaluation (Coq
  `yam_plactic_shape`).
-/

namespace List

open List

/-! ### Dominant words -/

/-- A word is dominant when each letter occurs at least as often as its successor. -/
def Dominant (l : List ℕ) : Prop := ∀ n, l.count (n + 1) ≤ l.count n

lemma isYam_iff_dominant_drop {w : List ℕ} : IsYam w ↔ ∀ i, Dominant (w.drop i) :=
  isYam_iff_count

lemma IsYam.dominant_drop {w : List ℕ} (h : IsYam w) (i : ℕ) : Dominant (w.drop i) :=
  isYam_iff_dominant_drop.1 h i

lemma IsYam.dominant {w : List ℕ} (h : IsYam w) : Dominant w := by
  simpa using h.dominant_drop 0

lemma Dominant.of_perm {l l' : List ℕ} (hperm : l.Perm l') (h : Dominant l) : Dominant l' :=
  fun n ↦ by rw [← hperm.count_eq, ← hperm.count_eq]; exact h n

/-- A suffix of a Yamanouchi word is Yamanouchi. -/
lemma IsYam.suffix {v w : List ℕ} (h : IsYam w) (hv : v <:+ w) : IsYam v := by
  obtain ⟨i, rfl⟩ : ∃ i, v = w.drop i := ⟨_, suffix_iff_eq_drop.1 hv⟩
  refine isYam_iff_dominant_drop.2 fun j ↦ ?_
  rw [drop_drop]
  exact h.dominant_drop _

lemma isYam_cons_iff {a : ℕ} {l : List ℕ} : IsYam (a :: l) ↔ Dominant (a :: l) ∧ IsYam l := by
  constructor
  · intro h
    exact ⟨h.dominant, h.suffix (suffix_cons a l)⟩
  · rintro ⟨hd, hl⟩
    refine isYam_iff_dominant_drop.2 fun i ↦ ?_
    match i with
    | 0 => simpa using hd
    | (i + 1) => simpa using hl.dominant_drop i

/-! ### The four count lemmas behind the invariance -/

private lemma dominant_cons_of_lt {x z : ℕ} {A : List ℕ} (hxz : x < z) (hA : Dominant A)
    (h : Dominant (x :: z :: A)) : Dominant (x :: A) := by
  intro n
  have h1 := h n
  have h2 := hA n
  simp only [count_cons, beq_iff_eq] at h1 ⊢
  split_ifs at h1 ⊢ <;> omega

private lemma dominant_cons_of_lt' {x y z : ℕ} {s : List ℕ} (hxy : x ≤ y) (hyz : y < z)
    (hs : Dominant s) (hys : Dominant (y :: s)) (h : Dominant (z :: x :: y :: s)) :
    Dominant (z :: y :: s) := by
  intro n
  have h1 := h n
  have h2 := hys n
  have h3 := hs n
  simp only [count_cons, beq_iff_eq] at h1 h2 ⊢
  split_ifs at h1 h2 ⊢ <;> omega

private lemma dominant_cons_of_lt'' {x y z : ℕ} {s : List ℕ} (hxy : x < y) (hyz : y ≤ z)
    (hs : Dominant s) (h1 : Dominant (z :: x :: s)) (h2 : Dominant (y :: z :: x :: s)) :
    Dominant (z :: s) := by
  intro n
  have k1 := h1 n
  have k2 := h2 n
  have k3 := hs n
  simp only [count_cons, beq_iff_eq] at k1 k2 ⊢
  split_ifs at k1 k2 ⊢ <;> omega

/-! ### Invariance of the Yamanouchi property under the Knuth relations -/

/-- Replacing a suffix by a Yamanouchi permutation of it preserves the Yamanouchi
property. -/
lemma isYam_append_of_perm {p q q' : List ℕ} (hperm : q.Perm q') (h : IsYam (p ++ q))
    (hq' : IsYam q') : IsYam (p ++ q') := by
  refine isYam_iff_dominant_drop.2 fun i ↦ ?_
  rw [drop_append]
  rcases le_or_gt i p.length with hi | hi
  · have h0 : i - p.length = 0 := by omega
    rw [h0, drop_zero]
    refine Dominant.of_perm (hperm.append_left _) ?_
    have := h.dominant_drop i
    rwa [drop_append, h0, drop_zero] at this
  · rw [drop_of_length_le hi.le, nil_append]
    exact hq'.dominant_drop _

private lemma isYam_knuthAC {x y z : ℕ} (hxy : x ≤ y) (hyz : y < z) (s : List ℕ) :
    IsYam (x :: z :: y :: s) ↔ IsYam (z :: x :: y :: s) := by
  have hperm : (x :: z :: y :: s).Perm (z :: x :: y :: s) := Perm.swap _ _ _
  simp only [isYam_cons_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, h3, h4⟩
    · exact Dominant.of_perm hperm h1
    · exact dominant_cons_of_lt (lt_of_le_of_lt hxy hyz) h3 h1
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, h3, h4⟩
    · exact Dominant.of_perm hperm.symm h1
    · exact dominant_cons_of_lt' hxy hyz h4.dominant h3 h1

private lemma isYam_knuthCA {x y z : ℕ} (hxy : x < y) (hyz : y ≤ z) (s : List ℕ) :
    IsYam (y :: x :: z :: s) ↔ IsYam (y :: z :: x :: s) := by
  have hperm : (x :: z :: s).Perm (z :: x :: s) := Perm.swap _ _ _
  have hperm' : (y :: x :: z :: s).Perm (y :: z :: x :: s) := hperm.cons y
  simp only [isYam_cons_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, h4⟩
    · exact Dominant.of_perm hperm' h1
    · exact Dominant.of_perm hperm h2
    · exact dominant_cons_of_lt (lt_of_lt_of_le hxy hyz) h4.dominant h2
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, h4⟩
    · exact Dominant.of_perm hperm'.symm h1
    · exact Dominant.of_perm hperm.symm h2
    · exact dominant_cons_of_lt'' hxy hyz h4.dominant h2 h1

/-- Being Yamanouchi is invariant under one Knuth transformation (Coq `is_yam_plactic`). -/
theorem PlacticStep.isYam_iff {u v : List ℕ} (h : PlacticStep u v) : IsYam u ↔ IsYam v := by
  induction h with
  | @knuthAC x y z hxy hyz p s =>
    have hperm : (x :: z :: y :: s).Perm (z :: x :: y :: s) := Perm.swap _ _ _
    constructor
    · intro hu
      exact isYam_append_of_perm hperm hu
        ((isYam_knuthAC hxy hyz s).1 (hu.suffix (suffix_append p _)))
    · intro hv
      exact isYam_append_of_perm hperm.symm hv
        ((isYam_knuthAC hxy hyz s).2 (hv.suffix (suffix_append p _)))
  | @knuthCA x y z hxy hyz p s =>
    have hperm : (y :: x :: z :: s).Perm (y :: z :: x :: s) := (Perm.swap _ _ _).cons _
    constructor
    · intro hu
      exact isYam_append_of_perm hperm hu
        ((isYam_knuthCA hxy hyz s).1 (hu.suffix (suffix_append p _)))
    · intro hv
      exact isYam_append_of_perm hperm.symm hv
        ((isYam_knuthCA hxy hyz s).2 (hv.suffix (suffix_append p _)))

/-- Being Yamanouchi is invariant under Knuth equivalence (Coq `is_yam_plactic`). -/
theorem PlacticEquiv.isYam_iff {u v : List ℕ} (h : PlacticEquiv u v) : IsYam u ↔ IsYam v := by
  induction h with
  | rel a b hab => exact hab.isYam_iff
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

/-- Knuth equivalent words have the same evaluation. -/
theorem evalseq_eq_of_placticEquiv {u v : List ℕ} (h : PlacticEquiv u v) :
    evalseq u = evalseq v :=
  ext_getD_of_getLastD_ne_zero (getLastD_evalseq_ne_zero _) (getLastD_evalseq_ne_zero _)
    fun i ↦ by rw [getD_evalseq, getD_evalseq, h.perm.count_eq]

/-! ### The Yamanouchi tableau -/

/-- Auxiliary definition for `yamTab`: the list of rows whose `j`-th row consists of
`sh.getD j 0` copies of the letter `d + j` (Coq `yamtab_rec`). -/
def yamTabAux : ℕ → List ℕ → List (List ℕ)
  | _, [] => []
  | d, m :: sh => List.replicate m d :: yamTabAux (d + 1) sh

/-- The Yamanouchi tableau of shape `sh`: its `i`-th row only contains the letter `i`
(Coq `yamtab`). -/
def yamTab (sh : List ℕ) : List (List ℕ) := yamTabAux 0 sh

@[simp] lemma yamTabAux_nil (d : ℕ) : yamTabAux d [] = [] := rfl

@[simp] lemma yamTabAux_cons (d m : ℕ) (sh : List ℕ) :
    yamTabAux d (m :: sh) = List.replicate m d :: yamTabAux (d + 1) sh := rfl

@[simp] lemma yamTab_nil : yamTab [] = [] := rfl

lemma shape_yamTabAux (d : ℕ) (sh : List ℕ) : shape (yamTabAux d sh) = sh := by
  induction sh generalizing d with
  | nil => rfl
  | cons m sh ih => simp [ih]

/-- Coq `shape_yamtab`. -/
@[simp] lemma shape_yamTab (sh : List ℕ) : shape (yamTab sh) = sh := shape_yamTabAux 0 sh

@[simp] lemma length_yamTab (sh : List ℕ) : (yamTab sh).length = sh.length := by
  have h : (shape (yamTab sh)).length = sh.length := by rw [shape_yamTab]
  simpa [shape] using h

lemma getD_yamTabAux (d : ℕ) (sh : List ℕ) (i : ℕ) :
    (yamTabAux d sh).getD i [] = List.replicate (sh.getD i 0) (d + i) := by
  induction sh generalizing d i with
  | nil => simp
  | cons m sh ih =>
    cases i with
    | zero => simp
    | succ j =>
      simp only [yamTabAux_cons, getD_cons_succ, ih]
      congr 1
      omega

/-- The `i`-th row of the Yamanouchi tableau of shape `sh` consists of `sh.getD i 0`
copies of the letter `i`. -/
lemma getD_yamTab (sh : List ℕ) (i : ℕ) :
    (yamTab sh).getD i [] = List.replicate (sh.getD i 0) i := by
  simpa [yamTab] using getD_yamTabAux 0 sh i

lemma hyperYamRev_concat (l : List ℕ) (m : ℕ) :
    hyperYamRev (l ++ [m]) = (hyperYamRev l).map (· + 1) ++ List.replicate m 0 := by
  induction l with
  | nil => simp
  | cons s0 s ih => simp [ih, map_replicate, append_assoc]

lemma hyperYam_cons (m : ℕ) (sh : List ℕ) :
    hyperYam (m :: sh) = (hyperYam sh).map (· + 1) ++ List.replicate m 0 := by
  rw [hyperYam, reverse_cons, hyperYamRev_concat, hyperYam]

lemma toWord_yamTabAux (d : ℕ) (sh : List ℕ) :
    toWord (yamTabAux d sh) = (hyperYam sh).map (· + d) := by
  induction sh generalizing d with
  | nil => simp
  | cons m sh ih =>
    rw [yamTabAux_cons, toWord_cons, ih, hyperYam_cons, map_append, map_map, map_replicate]
    congr 1
    · exact map_congr_left fun x _ ↦ by simp only [Function.comp_apply]; omega
    · simp

/-- The reading word of the Yamanouchi tableau of shape `sh` is the hyperstandard
Yamanouchi word of evaluation `sh` (Coq `to_word_yamtab`). -/
lemma toWord_yamTab (sh : List ℕ) : toWord (yamTab sh) = hyperYam sh := by
  simpa [yamTab] using toWord_yamTabAux 0 sh

/-- Coq `yamtabP`: the Yamanouchi tableau of a partition shape is a tableau. -/
lemma isTableau_yamTab {sh : List ℕ} (h : IsPart sh) : IsTableau (yamTab sh) := by
  refine isTableau_of_getD (fun i hi ↦ ?_) (fun i ↦ ?_) fun i ↦ ?_
  · rw [getD_yamTab]
    simp only [ne_eq, replicate_eq_nil_iff]
    have := h.getD_pos (i := i) (by simpa using hi)
    omega
  · rw [getD_yamTab]
    exact isChain_iff_pairwise.2 (pairwise_replicate.2 (Or.inr le_rfl))
  · rw [getD_yamTab, getD_yamTab]
    refine dominate_of_getElem (by simpa using h.getD_succ_le i) fun j hj ↦ ?_
    simp only [getElem_replicate]
    omega

/-! ### Uniqueness of the Yamanouchi tableau -/

/-- In a tableau of natural numbers, the entries of the `i`-th row are at least `i`. -/
lemma IsTableau.index_le_getElem {t : List (List ℕ)} (h : IsTableau t) {i c : ℕ}
    (hc : c < (t.getD i []).length) : i ≤ (t.getD i [])[c] := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have hlen : c < (t.getD i []).length :=
      lt_of_lt_of_le hc (h.dominate_getD (Nat.lt_succ_self i)).length_le
    exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih hlen) (h.col_lt hc))

/-- Splitting the reading word of a tableau at its `i`-th row. -/
lemma toWord_eq_append_getD_append {t : List (List ℕ)} {i : ℕ} (hi : i < t.length) :
    toWord t = toWord (t.drop (i + 1)) ++ (t.getD i [] ++ toWord (t.take i)) := by
  conv_lhs => rw [← take_append_drop (i + 1) t]
  rw [toWord, reverse_append, flatten_append, ← toWord, ← toWord, take_add_one,
    getElem?_eq_getElem hi]
  simp only [Option.toList_some]
  rw [toWord_concat, List.getD_eq_getElem _ _ hi]

/-- Every letter of the reading word of the first `i` rows lies in one of those rows. -/
lemma exists_lt_of_mem_toWord_take {t : List (List ℕ)} {i x : ℕ}
    (hx : x ∈ toWord (t.take i)) : ∃ j < i, x ∈ t.getD j [] := by
  rw [toWord, mem_flatten] at hx
  obtain ⟨r, hr, hxr⟩ := hx
  rw [mem_reverse] at hr
  obtain ⟨j, hj, rfl⟩ := getElem_of_mem hr
  rw [length_take] at hj
  rw [getElem_take] at hxr
  exact ⟨j, by omega, by rwa [List.getD_eq_getElem _ _ (by omega : j < t.length)]⟩

/-- Coq `yamtab_unique`: in a tableau whose reading word is Yamanouchi, the `i`-th row
consists of copies of the letter `i`. -/
theorem getD_eq_replicate_of_isYam_toWord {t : List (List ℕ)} (htab : IsTableau t)
    (hyam : IsYam (toWord t)) (i : ℕ) :
    t.getD i [] = List.replicate ((shape t).getD i 0) i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  rcases Nat.lt_or_ge i t.length with hi | hi
  · have hlt : ∀ x ∈ toWord (t.take i), x < i := by
      intro x hx
      obtain ⟨j, hj, hxj⟩ := exists_lt_of_mem_toWord_take hx
      rw [ih j hj, mem_replicate] at hxj
      omega
    have hz : ∀ n, i ≤ n → (toWord (t.take i)).count n = 0 := by
      intro n hn
      refine count_eq_zero.2 fun hmem ↦ ?_
      have := hlt n hmem
      omega
    have hne : t.getD i [] ≠ [] := htab.getD_ne_nil hi
    set r := t.getD i [] with hr
    have hlen : 0 < r.length := length_pos_iff.2 hne
    have hcl : r.length - 1 < r.length := by omega
    set b := r[r.length - 1] with hbdef
    have hib : i ≤ b := htab.index_le_getElem hcl
    have hbi : b ≤ i := by
      by_contra hcon
      push Not at hcon
      have hrsplit : r.dropLast ++ [b] = r := by
        rw [hbdef, ← getLast_eq_getElem hne]
        exact dropLast_append_getLast hne
      have hsplit : toWord t =
          (toWord (t.drop (i + 1)) ++ r.dropLast) ++ (b :: toWord (t.take i)) := by
        rw [toWord_eq_append_getD_append hi, ← hr]
        conv_lhs => rw [← hrsplit]
        simp [append_assoc]
      have hsuf : (b :: toWord (t.take i)) <:+ toWord t := hsplit ▸ suffix_append _ _
      have hdom := (hyam.suffix hsuf).dominant (b - 1)
      rw [show b - 1 + 1 = b by omega, count_cons_self,
        count_cons_of_ne (by omega : ¬ b = b - 1), hz b (by omega),
        hz (b - 1) (by omega)] at hdom
      omega
    have hall : ∀ x ∈ r, x = i := by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := getElem_of_mem hx
      have h1 : i ≤ r[c] := htab.index_le_getElem hc
      have h2 : r[c] ≤ b := htab.row_le (by omega : c ≤ r.length - 1) hcl
      omega
    rw [getD_shape, ← hr, eq_replicate_iff]
    exact ⟨rfl, hall⟩
  · rw [getD_shape, List.getD_eq_default _ _ hi]
    simp

/-- Coq `yamtab_unique`: a tableau whose reading word is Yamanouchi is the Yamanouchi
tableau of its shape. -/
theorem eq_yamTab_of_isYam_toWord {t : List (List ℕ)} (htab : IsTableau t)
    (hyam : IsYam (toWord t)) : t = yamTab (shape t) := by
  refine eq_of_getD_eq (fun i hi ↦ ?_) (fun i hi ↦ ?_) fun i ↦ ?_
  · exact IsTableau.getD_ne_nil htab hi
  · exact IsTableau.getD_ne_nil (isTableau_yamTab (isPart_shape htab)) hi
  · rw [getD_yamTab, getD_eq_replicate_of_isYam_toWord htab hyam]

/-! ### Insertion tableau of a Yamanouchi word -/

/-- Coq `RS_yam_RS`: the insertion tableau of a Yamanouchi word is a Yamanouchi tableau. -/
theorem RS_eq_yamTab_shape {y : List ℕ} (h : IsYam y) : RS y = yamTab (shape (RS y)) :=
  eq_yamTab_of_isYam_toWord (isTableau_RS y) ((plactic_toWord_RS y).isYam_iff.2 h)

/-- Coq `shape_RS_yam`: the shape of the insertion tableau of a Yamanouchi word is its
evaluation. -/
theorem shape_RS_of_isYam {y : List ℕ} (h : IsYam y) : shape (RS y) = evalseq y := by
  rw [← evalseq_eq_of_placticEquiv (plactic_toWord_RS y)]
  conv_rhs => rw [RS_eq_yamTab_shape h, toWord_yamTab]
  rw [evalseq_hyperYam (isPart_shape (isTableau_RS y))]

/-- Coq `RS_yam`: the insertion tableau of a Yamanouchi word is the Yamanouchi tableau of
its evaluation. -/
theorem RS_eq_yamTab {y : List ℕ} (h : IsYam y) : RS y = yamTab (evalseq y) := by
  rw [RS_eq_yamTab_shape h, shape_RS_of_isYam h]

/-- Coq `yam_plactic_hyper`: a Yamanouchi word is Knuth equivalent to the hyperstandard
Yamanouchi word of its evaluation. -/
theorem placticEquiv_hyperYam {y : List ℕ} (h : IsYam y) :
    PlacticEquiv y (hyperYam (evalseq y)) := by
  rw [← toWord_yamTab, ← RS_eq_yamTab h]
  exact (plactic_toWord_RS y).symm

/-- Coq `yam_plactic_shape`: the plactic class of a Yamanouchi word consists of the
Yamanouchi words with the same evaluation. -/
theorem isYam_placticEquiv_iff {y z : List ℕ} (h : IsYam y) :
    PlacticEquiv y z ↔ IsYam z ∧ evalseq y = evalseq z := by
  constructor
  · intro hpl
    exact ⟨hpl.isYam_iff.1 h, evalseq_eq_of_placticEquiv hpl⟩
  · rintro ⟨hz, hev⟩
    rw [placticEquiv_iff_RS_eq, RS_eq_yamTab h, RS_eq_yamTab hz, hev]

end List
