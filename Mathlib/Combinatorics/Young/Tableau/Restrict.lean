/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Shape.HorizontalStrip
import Mathlib.Combinatorics.Young.Shape.NatPartition
import Mathlib.Combinatorics.Young.RobinsonSchensted.InsertionTableau

/-!
# Removing the largest letter of a tableau

Let `P` be a Young tableau whose entries are letters `< N + 1`.  Removing from `P` all the
boxes containing the largest letter `N` leaves a tableau with entries `< N`, whose shape
`nu` is obtained from the shape of `P` by removing a horizontal strip.  Conversely, given
a tableau of shape `nu` with entries `< N` and a shape `sh` such that `sh / nu` is a
horizontal strip, filling the boxes of `sh / nu` with the letter `N` produces a tableau of
shape `sh`.

This is the recursive description of Young tableaux by the letter they contain, and it is
the combinatorial content of the Pieri rule.

## Main definitions

* `List.ltFilter N r` : the letters `< N` of a row `r`.
* `List.dropMax N P` : the tableau `P` with all the letters `N` removed.
* `List.addMax N sh Q` : the tableau `Q` completed to the shape `sh` by letters `N`.
* `List.tabSet N sh c` : the tableaux of shape `sh`, entries `< N` and content `c`.
* `List.kostkaNum N sh c` : the number of such tableaux.

## Main results

* `List.kostkaNum_succ` : the recursion
  `K_{sh, c} = ∑_{nu} K_{nu, c}`, the sum being over the shapes `nu` such that `sh / nu`
  is a horizontal strip with `c N` boxes.
-/

namespace List

open List

/-! ### Filtering the small letters of a row -/

/-- The letters `< N` of a row. -/
def ltFilter (N : ℕ) (r : List ℕ) : List ℕ := r.filter (fun x => decide (x < N))

@[simp] lemma ltFilter_nil (N : ℕ) : ltFilter N [] = [] := rfl

lemma ltFilter_cons_of_lt {N a : ℕ} (r : List ℕ) (h : a < N) :
    ltFilter N (a :: r) = a :: ltFilter N r := by
  simp [ltFilter, h]

lemma ltFilter_cons_of_ge {N a : ℕ} (r : List ℕ) (h : ¬ a < N) :
    ltFilter N (a :: r) = ltFilter N r := by
  simp [ltFilter, h]

@[simp] lemma mem_ltFilter {N x : ℕ} {r : List ℕ} : x ∈ ltFilter N r ↔ x ∈ r ∧ x < N := by
  simp [ltFilter]

lemma ltFilter_sublist (N : ℕ) (r : List ℕ) : (ltFilter N r).Sublist r := List.filter_sublist

lemma length_ltFilter_le (N : ℕ) (r : List ℕ) : (ltFilter N r).length ≤ r.length :=
  (ltFilter_sublist N r).length_le

lemma isRow_ltFilter {N : ℕ} {r : List ℕ} (hr : IsRow r) : IsRow (ltFilter N r) :=
  List.IsChain.sublist hr (ltFilter_sublist N r)

lemma count_ltFilter (N : ℕ) (r : List ℕ) (i : ℕ) :
    (ltFilter N r).count i = if i < N then r.count i else 0 := by
  induction r with
  | nil => simp
  | cons a r ih =>
    by_cases ha : a < N
    · rw [ltFilter_cons_of_lt r ha, List.count_cons, List.count_cons, ih]
      by_cases hi : i < N
      · simp [hi]
      · have hai : ¬ a = i := by omega
        simp [hi, hai]
    · rw [ltFilter_cons_of_ge r ha, ih, List.count_cons]
      by_cases hi : i < N
      · have hai : ¬ a = i := by omega
        simp [hi, hai]
      · simp [hi]

/-- In a weakly increasing list, every entry is at least the first one. -/
lemma IsRow.headD_le_of_mem {r : List ℕ} (hr : IsRow r) {x d : ℕ} (hx : x ∈ r) :
    r.headD d ≤ x := by
  cases r with
  | nil => simp at hx
  | cons a t =>
    rcases List.mem_cons.1 hx with rfl | hx
    · simp
    · have := List.isChain_iff_pairwise.1 hr
      rw [List.pairwise_cons] at this
      simpa using this.1 x hx

/-- For a weakly increasing row, the letters `< N` form an initial segment, and the
letters at the following positions are `≥ N`. -/
lemma ltFilter_spec {N : ℕ} {r : List ℕ} (hr : IsRow r) :
    ltFilter N r = r.take (ltFilter N r).length ∧
      ∀ c, (hc : c < r.length) → (r[c] < N ↔ c < (ltFilter N r).length) := by
  induction r with
  | nil => simp
  | cons a t ih =>
    by_cases ha : a < N
    · obtain ⟨ih1, ih2⟩ := ih hr.of_cons
      rw [ltFilter_cons_of_lt t ha]
      refine ⟨by simp only [List.length_cons, List.take_succ_cons]; rw [← ih1], fun c hc => ?_⟩
      cases c with
      | zero => simpa using ha
      | succ j =>
        have hj : j < t.length := by simpa using hc
        simpa using ih2 j hj
    · have hall : ∀ x ∈ a :: t, ¬ x < N := by
        intro x hx
        have := hr.headD_le_of_mem (d := 0) hx
        simp only [List.headD_cons] at this
        omega
      have hnil : ltFilter N (a :: t) = [] := by
        rw [ltFilter, List.filter_eq_nil_iff]
        intro x hx
        simpa using hall x hx
      rw [hnil]
      refine ⟨by simp, fun c hc => ?_⟩
      simp only [List.length_nil, Nat.not_lt_zero, iff_false, not_lt]
      have := hall (a :: t)[c] (List.getElem_mem hc)
      omega

lemma ltFilter_eq_take {N : ℕ} {r : List ℕ} (hr : IsRow r) :
    ltFilter N r = r.take (ltFilter N r).length := (ltFilter_spec hr).1

lemma ltFilter_prefix {N : ℕ} {r : List ℕ} (hr : IsRow r) : ltFilter N r <+: r := by
  conv_rhs => rw [← List.take_append_drop (ltFilter N r).length r, ← ltFilter_eq_take hr]
  exact List.prefix_append _ _

lemma getElem_ltFilter {N : ℕ} {r : List ℕ} (hr : IsRow r) {c : ℕ}
    (hc : c < (ltFilter N r).length) :
    (ltFilter N r)[c] = r[c]'(lt_of_lt_of_le hc (length_ltFilter_le N r)) :=
  (ltFilter_prefix hr).getElem hc

lemma lt_length_ltFilter_iff {N : ℕ} {r : List ℕ} (hr : IsRow r) {c : ℕ} (hc : c < r.length) :
    r[c] < N ↔ c < (ltFilter N r).length := (ltFilter_spec hr).2 c hc

/-- A row whose letters are `< N + 1` is its part `< N` followed by copies of `N`. -/
lemma ltFilter_append_replicate {N : ℕ} {r : List ℕ} (hr : IsRow r)
    (hlt : ∀ x ∈ r, x < N + 1) :
    ltFilter N r ++ List.replicate (r.length - (ltFilter N r).length) N = r := by
  have hpre : ltFilter N r = r.take (ltFilter N r).length := ltFilter_eq_take hr
  have hdrop : r.drop (ltFilter N r).length = List.replicate
      (r.length - (ltFilter N r).length) N := by
    refine List.eq_replicate_iff.2 ⟨by simp, fun x hx => ?_⟩
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_drop]
    have hlen : (ltFilter N r).length + c < r.length := by
      simp only [List.length_drop] at hc
      omega
    have h1 : ¬ r[(ltFilter N r).length + c] < N := by
      rw [lt_length_ltFilter_iff hr hlen]
      omega
    have h2 := hlt _ (List.getElem_mem hlen)
    omega
  conv_rhs => rw [← List.take_append_drop (ltFilter N r).length r]
  rw [← hpre, hdrop]

/-! ### Rows of a tableau -/

lemma IsTableau.getD_ne_nil {t : List (List ℕ)} (h : IsTableau t) {i : ℕ} (hi : i < t.length) :
    t.getD i [] ≠ [] := by
  have hpos : 0 < (shape t).getD i 0 :=
    (isPart_shape h).getD_pos (by simpa [shape] using hi)
  rw [getD_shape] at hpos
  intro hc
  rw [hc] at hpos
  simp at hpos

/-- Two lists of nonempty rows with the same rows are equal. -/
lemma eq_of_getD_eq {A B : List (List ℕ)} (hA : ∀ i < A.length, A.getD i [] ≠ [])
    (hB : ∀ i < B.length, B.getD i [] ≠ []) (h : ∀ i, A.getD i [] = B.getD i []) : A = B := by
  have hlen : A.length = B.length := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hB A.length hlt (by rw [← h, List.getD_eq_default _ _ (le_refl _)])
    · exact hA B.length hlt (by rw [h, List.getD_eq_default _ _ (le_refl _)])
  refine List.ext_getElem hlen fun i h1 h2 => ?_
  rw [← List.getD_eq_getElem _ _ h1, ← List.getD_eq_getElem _ _ h2]
  exact h i

/-- The length of a list of letters `< M`, counted letter by letter. -/
lemma length_eq_sum_count {l : List ℕ} {M : ℕ} (h : ∀ x ∈ l, x < M) :
    l.length = ∑ i ∈ Finset.range M, l.count i := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a < M := h a (by simp)
    have hl : ∀ x ∈ l, x < M := fun x hx => h x (by simp [hx])
    have hcount : ∀ i, (a :: l).count i = l.count i + if a = i then 1 else 0 := by
      intro i
      rw [List.count_cons]
      by_cases hai : a = i <;> simp [hai]
    simp only [List.length_cons, ih hl]
    rw [Finset.sum_congr rfl (fun i _ => hcount i), Finset.sum_add_distrib,
      Finset.sum_ite_eq (Finset.range M) a (fun _ => 1), ite_eq_left (Finset.mem_range.2 ha)]

/-! ### Removing the largest letter -/

/-- The tableau `P` with all the letters `≥ N` removed. -/
def dropMax (N : ℕ) : List (List ℕ) → List (List ℕ)
  | [] => []
  | r :: P => if ltFilter N r = [] then [] else ltFilter N r :: dropMax N P

@[simp] lemma dropMax_nil (N : ℕ) : dropMax N [] = [] := rfl

lemma dropMax_cons (N : ℕ) (r : List ℕ) (P : List (List ℕ)) :
    dropMax N (r :: P) = if ltFilter N r = [] then [] else ltFilter N r :: dropMax N P := rfl

/-- If the letters `< N` have disappeared from a row of a tableau, they have disappeared
from all the rows below. -/
lemma ltFilter_eq_nil_of_le {N : ℕ} {P : List (List ℕ)} (hP : IsTableau P) {i j : ℕ}
    (hij : i ≤ j) (h : ltFilter N (P.getD i []) = []) : ltFilter N (P.getD j []) = [] := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact h
  have hall : ∀ x ∈ P.getD i [], ¬ x < N := by
    intro x hx
    have : x ∉ ltFilter N (P.getD i []) := by rw [h]; simp
    rw [mem_ltFilter] at this
    tauto
  rw [ltFilter, List.filter_eq_nil_iff]
  intro x hx
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hx
  have hdom : Dominate (P.getD j []) (P.getD i []) := hP.dominate_getD hlt
  have hci : c < (P.getD i []).length := lt_of_lt_of_le hc hdom.length_le
  have h1 : (P.getD i [])[c] < (P.getD j [])[c] := hdom.getElem_lt c hc
  have h2 := hall _ (List.getElem_mem hci)
  simp only [decide_eq_true_eq]
  omega

lemma length_dropMax_le (N : ℕ) (P : List (List ℕ)) : (dropMax N P).length ≤ P.length := by
  induction P with
  | nil => simp
  | cons r P ih =>
    rw [dropMax_cons]
    split_ifs with h
    · simp
    · simpa using ih

lemma getD_dropMax_ne_nil {N : ℕ} {P : List (List ℕ)} {i : ℕ}
    (hi : i < (dropMax N P).length) : (dropMax N P).getD i [] ≠ [] := by
  induction P generalizing i with
  | nil => simp at hi
  | cons r P ih =>
    rw [dropMax_cons] at hi ⊢
    split_ifs at hi ⊢ with h
    · simp at hi
    · cases i with
      | zero => simpa using h
      | succ j => exact ih (by simpa using hi)

/-- The rows of `dropMax N P` are the rows of `P` with the letters `≥ N` removed. -/
lemma getD_dropMax {N : ℕ} {P : List (List ℕ)} (hP : IsTableau P) (i : ℕ) :
    (dropMax N P).getD i [] = ltFilter N (P.getD i []) := by
  induction P generalizing i with
  | nil => simp
  | cons r P ih =>
    rw [dropMax_cons]
    split_ifs with h
    · have h0 : ltFilter N ((r :: P).getD 0 []) = [] := h
      rw [List.getD_eq_default _ _ (by simp)]
      exact (ltFilter_eq_nil_of_le hP (Nat.zero_le i) h0).symm
    · cases i with
      | zero => rfl
      | succ j => simpa using ih hP.of_cons j

/-! ### Rows and the flattening -/

lemma mem_flatten_of_mem_getD {P : List (List ℕ)} {x : ℕ} {i : ℕ} (hx : x ∈ P.getD i []) :
    x ∈ P.flatten := by
  rcases lt_or_ge i P.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi] at hx
    exact List.mem_flatten.2 ⟨P[i], List.getElem_mem hi, hx⟩
  · rw [List.getD_eq_default _ _ hi] at hx
    simp at hx

lemma mem_getD_of_mem_flatten {P : List (List ℕ)} {x : ℕ} (hx : x ∈ P.flatten) :
    ∃ j, x ∈ P.getD j [] := by
  obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
  exact ⟨j, by rwa [List.getD_eq_getElem _ _ hj]⟩

/-! ### `dropMax` is a tableau -/

lemma dominate_ltFilter {N : ℕ} {u v : List ℕ} (hu : IsRow u) (hv : IsRow v)
    (h : Dominate u v) : Dominate (ltFilter N u) (ltFilter N v) := by
  have hkey : ∀ c, c < (ltFilter N u).length → c < (ltFilter N v).length := by
    intro c hc
    have hcu : c < u.length := lt_of_lt_of_le hc (length_ltFilter_le N u)
    have hcv : c < v.length := lt_of_lt_of_le hcu h.length_le
    have h1 : u[c] < N := (lt_length_ltFilter_iff hu hcu).2 hc
    have h2 : v[c] < u[c] := h.getElem_lt c hcu
    exact (lt_length_ltFilter_iff hv hcv).1 (by omega)
  have hlen : (ltFilter N u).length ≤ (ltFilter N v).length := by
    by_contra hlt
    push Not at hlt
    exact absurd (hkey _ hlt) (lt_irrefl _)
  refine dominate_of_getElem hlen fun c hc => ?_
  have hcu : c < u.length := lt_of_lt_of_le hc (length_ltFilter_le N u)
  rw [getElem_ltFilter hu hc, getElem_ltFilter hv (hkey c hc)]
  exact h.getElem_lt c hcu

lemma isTableau_dropMax {N : ℕ} {P : List (List ℕ)} (hP : IsTableau P) :
    IsTableau (dropMax N P) := by
  refine isTableau_of_getD (fun i hi => getD_dropMax_ne_nil hi) (fun i => ?_) (fun i => ?_)
  · rw [getD_dropMax hP]
    exact isRow_ltFilter (hP.isRow_getD i)
  · rw [getD_dropMax hP, getD_dropMax hP]
    exact dominate_ltFilter (hP.isRow_getD (i + 1)) (hP.isRow_getD i)
      (hP.dominate_getD (Nat.lt_succ_self i))

lemma getD_shape_dropMax {N : ℕ} {P : List (List ℕ)} (hP : IsTableau P) (i : ℕ) :
    (shape (dropMax N P)).getD i 0 = (ltFilter N (P.getD i [])).length := by
  rw [getD_shape, getD_dropMax hP]

lemma lt_of_mem_flatten_dropMax {N : ℕ} {P : List (List ℕ)} (hP : IsTableau P) {x : ℕ}
    (hx : x ∈ (dropMax N P).flatten) : x < N := by
  obtain ⟨j, hj⟩ := mem_getD_of_mem_flatten hx
  rw [getD_dropMax hP, mem_ltFilter] at hj
  exact hj.2

/-- Removing the largest letter from a tableau removes a horizontal strip from its
shape. -/
lemma horizStrip_shape_dropMax {N : ℕ} {P : List (List ℕ)} (hP : IsTableau P)
    (hlt : ∀ x ∈ P.flatten, x < N + 1) :
    HorizStrip (shape P) (shape (dropMax N P)) := by
  refine ⟨(isPart_shape (isTableau_dropMax hP)).included_iff_getD.2 fun i => ?_, fun i => ?_⟩
  · rw [getD_shape_dropMax hP, getD_shape]
    exact length_ltFilter_le _ _
  · rw [getD_shape_dropMax hP, getD_shape]
    set u := P.getD (i + 1) [] with hu
    set v := P.getD i [] with hv
    have hdom : Dominate u v := hP.dominate_getD (Nat.lt_succ_self i)
    have hkey : ∀ c, c < u.length → c < (ltFilter N v).length := by
      intro c hc
      have hcv : c < v.length := lt_of_lt_of_le hc hdom.length_le
      have h1 : v[c]'hcv < u[c]'hc := hdom.getElem_lt c hc
      have h2 : u[c]'hc < N + 1 := hlt _ (mem_flatten_of_mem_getD (List.getElem_mem hc))
      have h3 : v[c]'hcv < N := by omega
      exact (lt_length_ltFilter_iff (show IsRow v from hP.isRow_getD i) hcv).1 h3
    by_contra hlt'
    push Not at hlt'
    exact absurd (hkey _ hlt') (lt_irrefl _)

/-- The letters of `dropMax N P` are the letters `< N` of `P`. -/
lemma count_flatten_dropMax {N : ℕ} {P : List (List ℕ)} (hP : IsTableau P) (i : ℕ) :
    (dropMax N P).flatten.count i = if i < N then P.flatten.count i else 0 := by
  induction P with
  | nil => simp
  | cons r P ih =>
    rw [dropMax_cons]
    by_cases h : ltFilter N r = []
    · rw [ite_eq_left h]
      have hzero : ∀ x ∈ (r :: P).flatten, ¬ x < N := by
        intro x hx
        obtain ⟨j, hj⟩ := mem_getD_of_mem_flatten hx
        have hj0 : ltFilter N ((r :: P).getD j []) = [] :=
          ltFilter_eq_nil_of_le hP (Nat.zero_le j) h
        intro hxN
        have hmem : x ∈ ltFilter N ((r :: P).getD j []) := mem_ltFilter.2 ⟨hj, hxN⟩
        rw [hj0] at hmem
        simp at hmem
      by_cases hi : i < N
      · rw [ite_eq_left hi]
        simp only [List.flatten_nil, List.count_nil]
        exact (List.count_eq_zero_of_not_mem fun hc => hzero i hc hi).symm
      · rw [ite_eq_right hi]
        simp
    · rw [ite_eq_right h, List.flatten_cons, List.flatten_cons, List.count_append, List.count_append,
        count_ltFilter, ih hP.of_cons]
      by_cases hi : i < N <;> simp [hi]

/-! ### Adding the largest letter -/

/-- The tableau `Q` completed to the shape `sh` by boxes filled with the letter `N`. -/
def addMax (N : ℕ) (sh : List ℕ) (Q : List (List ℕ)) : List (List ℕ) :=
  List.ofFn fun i : Fin sh.length =>
    Q.getD i [] ++ List.replicate (sh.getD i 0 - (Q.getD i []).length) N

@[simp] lemma length_addMax (N : ℕ) (sh : List ℕ) (Q : List (List ℕ)) :
    (addMax N sh Q).length = sh.length := by simp [addMax]

@[simp] lemma ltFilter_replicate (N k : ℕ) : ltFilter N (List.replicate k N) = [] := by
  rw [ltFilter, List.filter_eq_nil_iff]
  intro x hx
  rw [List.eq_of_mem_replicate hx]
  simp

section AddMax

variable {N : ℕ} {sh : List ℕ} {Q : List (List ℕ)}

lemma getD_addMax (hstrip : HorizStrip sh (shape Q)) (i : ℕ) :
    (addMax N sh Q).getD i [] =
      Q.getD i [] ++ List.replicate (sh.getD i 0 - (Q.getD i []).length) N := by
  rcases lt_or_ge i sh.length with hi | hi
  · rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp [addMax, List.getElem?_eq_getElem hi]
  · have hQlen : Q.length ≤ sh.length := by
      have := hstrip.included.length_le
      simpa [shape] using this
    have hQi : Q.getD i [] = [] := List.getD_eq_default _ _ (by omega)
    have hshi : sh.getD i 0 = 0 := List.getD_eq_default _ _ hi
    rw [List.getD_eq_default _ _ (by simpa using hi), hQi, hshi]
    simp

lemma length_getD_addMax (hstrip : HorizStrip sh (shape Q)) (i : ℕ) :
    ((addMax N sh Q).getD i []).length = sh.getD i 0 := by
  have hle : (Q.getD i []).length ≤ sh.getD i 0 := by
    have := hstrip.included.getD_le i
    rwa [getD_shape] at this
  rw [getD_addMax hstrip]
  simp only [List.length_append, List.length_replicate]
  omega

lemma shape_addMax (hstrip : HorizStrip sh (shape Q)) :
    shape (addMax N sh Q) = sh := by
  refine List.ext_getElem (by simp [shape]) fun i h1 h2 => ?_
  rw [← List.getD_eq_getElem _ _ h1, ← List.getD_eq_getElem _ _ h2, getD_shape]
  exact length_getD_addMax hstrip i

/-- Appending copies of a largest letter to a row gives a row. -/
lemma isRow_append_replicate {r : List ℕ} (hr : IsRow r) (hle : ∀ x ∈ r, x ≤ N) (k : ℕ) :
    IsRow (r ++ List.replicate k N) := by
  rw [IsRow, List.isChain_iff_pairwise, List.pairwise_append]
  refine ⟨List.isChain_iff_pairwise.1 hr, ?_, fun x hx y hy => ?_⟩
  · rw [List.pairwise_replicate]
    exact Or.inr (le_refl N)
  · rw [List.eq_of_mem_replicate hy]
    exact hle x hx

lemma isTableau_addMax (hsh : IsPart sh) (hQ : IsTableau Q) (hstrip : HorizStrip sh (shape Q))
    (hlt : ∀ x ∈ Q.flatten, x < N) : IsTableau (addMax N sh Q) := by
  have hlen : ∀ i, ((addMax N sh Q).getD i []).length = sh.getD i 0 :=
    length_getD_addMax hstrip
  have hQle : ∀ i, (Q.getD i []).length ≤ sh.getD i 0 := by
    intro i
    have := hstrip.included.getD_le i
    rwa [getD_shape] at this
  refine isTableau_of_getD (fun i hi => ?_) (fun i => ?_) (fun i => ?_)
  · have hpos : 0 < sh.getD i 0 := hsh.getD_pos (by simpa using hi)
    intro hc
    rw [← hlen i, hc] at hpos
    simp at hpos
  · rw [getD_addMax hstrip]
    exact isRow_append_replicate (hQ.isRow_getD i)
      (fun x hx => le_of_lt (hlt x (mem_flatten_of_mem_getD hx))) _
  · -- domination
    refine dominate_of_getElem (by rw [hlen, hlen]; exact hsh.getD_succ_le i) fun c hc => ?_
    rw [hlen] at hc
    have hcv : c < ((addMax N sh Q).getD i []).length := by
      rw [hlen]
      exact lt_of_lt_of_le hc (hsh.getD_succ_le i)
    have hrow1 := getD_addMax (N := N) hstrip (i + 1)
    have hrow0 := getD_addMax (N := N) hstrip i
    by_cases hcq : c < (Q.getD (i + 1) []).length
    · -- both entries come from `Q`
      have hdomQ : Dominate (Q.getD (i + 1) []) (Q.getD i []) :=
        hQ.dominate_getD (Nat.lt_succ_self i)
      have hci : c < (Q.getD i []).length := lt_of_lt_of_le hcq hdomQ.length_le
      have h1 : ((addMax N sh Q).getD (i + 1) [])[c]'(by rw [hlen]; exact hc)
          = (Q.getD (i + 1) [])[c]'hcq := by
        rw [List.getElem_of_eq hrow1]
        exact List.getElem_append_left hcq
      have h2 : ((addMax N sh Q).getD i [])[c]'hcv = (Q.getD i [])[c]'hci := by
        rw [List.getElem_of_eq hrow0]
        exact List.getElem_append_left hci
      rw [h1, h2]
      exact hdomQ.getElem_lt c hcq
    · -- the entry of the lower row is the largest letter
      push Not at hcq
      have hci : c < (Q.getD i []).length := by
        have := hstrip.getD_succ_le i
        rw [getD_shape] at this
        omega
      have h1 : ((addMax N sh Q).getD (i + 1) [])[c]'(by rw [hlen]; exact hc) = N := by
        rw [List.getElem_of_eq hrow1, List.getElem_append_right hcq]
        simp
      have h2 : ((addMax N sh Q).getD i [])[c]'hcv = (Q.getD i [])[c]'hci := by
        rw [List.getElem_of_eq hrow0]
        exact List.getElem_append_left hci
      rw [h1, h2]
      exact hlt _ (mem_flatten_of_mem_getD (List.getElem_mem hci))

lemma lt_of_mem_flatten_addMax (hstrip : HorizStrip sh (shape Q))
    (hlt : ∀ x ∈ Q.flatten, x < N) {x : ℕ} (hx : x ∈ (addMax N sh Q).flatten) : x < N + 1 := by
  obtain ⟨j, hj⟩ := mem_getD_of_mem_flatten hx
  rw [getD_addMax hstrip, List.mem_append] at hj
  rcases hj with hj | hj
  · exact lt_trans (hlt x (mem_flatten_of_mem_getD hj)) (Nat.lt_succ_self N)
  · rw [List.eq_of_mem_replicate hj]
    exact Nat.lt_succ_self N

/-- Adding and then removing the largest letter gives back the original tableau. -/
lemma dropMax_addMax (hsh : IsPart sh) (hQ : IsTableau Q) (hstrip : HorizStrip sh (shape Q))
    (hlt : ∀ x ∈ Q.flatten, x < N) : dropMax N (addMax N sh Q) = Q := by
  have hA : IsTableau (addMax N sh Q) := isTableau_addMax hsh hQ hstrip hlt
  refine eq_of_getD_eq (fun i _ => getD_dropMax_ne_nil (N := N) (by assumption))
    (fun i hi => hQ.getD_ne_nil hi) fun i => ?_
  rw [getD_dropMax hA, getD_addMax hstrip, ltFilter, List.filter_append]
  have h1 : List.filter (fun x => decide (x < N)) (Q.getD i []) = Q.getD i [] := by
    rw [List.filter_eq_self]
    intro x hx
    simpa using hlt x (mem_flatten_of_mem_getD hx)
  have h2 : List.filter (fun x => decide (x < N))
      (List.replicate (sh.getD i 0 - (Q.getD i []).length) N) = [] := ltFilter_replicate _ _
  rw [h1, h2, List.append_nil]

end AddMax

/-- Removing and then adding back the largest letter gives back the original tableau. -/
lemma addMax_dropMax {N : ℕ} {P : List (List ℕ)} (hP : IsTableau P)
    (hlt : ∀ x ∈ P.flatten, x < N + 1) : addMax N (shape P) (dropMax N P) = P := by
  have hD : IsTableau (dropMax N P) := isTableau_dropMax hP
  have hstrip : HorizStrip (shape P) (shape (dropMax N P)) := horizStrip_shape_dropMax hP hlt
  refine eq_of_getD_eq (fun i hi => ?_) (fun i hi => hP.getD_ne_nil hi) fun i => ?_
  · rw [getD_addMax hstrip]
    intro hc
    have hi' : i < (shape P).length := by simpa using hi
    have hpos : 0 < (shape P).getD i 0 := (isPart_shape hP).getD_pos hi'
    have hle : ((dropMax N P).getD i []).length ≤ (shape P).getD i 0 := by
      have := hstrip.included.getD_le i
      rwa [getD_shape] at this
    have hzero : ((dropMax N P).getD i [] ++
        List.replicate ((shape P).getD i 0 - ((dropMax N P).getD i []).length) N).length = 0 := by
      rw [hc]
      simp
    simp only [List.length_append, List.length_replicate] at hzero
    omega
  · rw [getD_addMax hstrip, getD_dropMax hP, getD_shape]
    exact ltFilter_append_replicate (hP.isRow_getD i)
      (fun x hx => hlt x (mem_flatten_of_mem_getD hx))

/-! ### Counting tableaux with a given content -/

lemma length_flatten_eq_sum_shape (P : List (List ℕ)) : P.flatten.length = (shape P).sum := by
  simp [shape, List.length_flatten]

/-- Removing the largest letter removes as many boxes as there were largest letters. -/
lemma sum_shape_dropMax {N : ℕ} {P : List (List ℕ)} (hP : IsTableau P)
    (hlt : ∀ x ∈ P.flatten, x < N + 1) :
    (shape (dropMax N P)).sum + P.flatten.count N = (shape P).sum := by
  have h1 : (shape (dropMax N P)).sum = ∑ i ∈ Finset.range N, P.flatten.count i := by
    rw [← length_flatten_eq_sum_shape,
      length_eq_sum_count (M := N) (fun x hx => lt_of_mem_flatten_dropMax hP hx)]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [count_flatten_dropMax hP, ite_eq_left (Finset.mem_range.1 hi)]
  have h2 : (shape P).sum = ∑ i ∈ Finset.range (N + 1), P.flatten.count i := by
    rw [← length_flatten_eq_sum_shape, length_eq_sum_count hlt]
  rw [h1, h2, Finset.sum_range_succ]

/-- The tableaux of shape `sh` with entries `< N` and content `c`. -/
def tabSet (N : ℕ) (sh : List ℕ) (c : ℕ → ℕ) : Set (List (List ℕ)) :=
  {P | IsTableau P ∧ shape P = sh ∧ (∀ x ∈ P.flatten, x < N) ∧ ∀ i < N, P.flatten.count i = c i}

/-- The number of tableaux of shape `sh` with entries `< N` and content `c`: a Kostka
number. -/
noncomputable def kostkaNum (N : ℕ) (sh : List ℕ) (c : ℕ → ℕ) : ℕ := Nat.card (tabSet N sh c)

instance finite_tabSet (N : ℕ) (sh : List ℕ) (c : ℕ → ℕ) : Finite (tabSet N sh c) := by
  refine Finite.of_injective
    (β := Fin sh.sum → Fin (N + 1))
    (fun P i => ((⟨min (P.1.flatten.getD i 0) N, by omega⟩ : Fin (N + 1)))) ?_
  intro X Y h
  obtain ⟨hP, hPsh, hPlt, -⟩ := X.2
  obtain ⟨hR, hRsh, hRlt, -⟩ := Y.2
  set P := X.1 with hPdef
  set R := Y.1 with hRdef
  have hlenP : P.flatten.length = sh.sum := by rw [length_flatten_eq_sum_shape, hPsh]
  have hlenR : R.flatten.length = sh.sum := by rw [length_flatten_eq_sum_shape, hRsh]
  have hflat : P.flatten = R.flatten := by
    refine List.ext_getElem (by rw [hlenP, hlenR]) fun i h1 h2 => ?_
    have hi : i < sh.sum := by rwa [hlenP] at h1
    have := congrFun h ⟨i, hi⟩
    simp only [Fin.mk.injEq] at this
    have hP1 : P.flatten.getD i 0 = P.flatten[i] := List.getD_eq_getElem _ _ h1
    have hR1 : R.flatten.getD i 0 = R.flatten[i] := List.getD_eq_getElem _ _ h2
    have hPlt' : P.flatten[i] < N := hPlt _ (List.getElem_mem h1)
    have hRlt' : R.flatten[i] < N := hRlt _ (List.getElem_mem h2)
    rw [hP1, hR1] at this
    omega
  exact Subtype.ext (eq_of_shape_eq_of_flatten_eq (by rw [hPsh, hRsh]) hflat)

/-! ### The recursion on the largest letter -/

/-- The pairs consisting of a shape `nu` of size `m` such that `sh / nu` is a horizontal
strip, together with a tableau of shape `nu`, entries `< N` and content `c`. -/
def pairSet (N : ℕ) (sh : List ℕ) (c : ℕ → ℕ) (m : ℕ) : Set ((List ℕ) × List (List ℕ)) :=
  {x | (IsPart x.1 ∧ x.1.sum = m) ∧ HorizStrip sh x.1 ∧ x.2 ∈ tabSet N x.1 c}

variable {N : ℕ} {sh : List ℕ} {c : ℕ → ℕ} {m : ℕ}

lemma dropMax_mem_pairSet (hm : m + c N = sh.sum) {P : List (List ℕ)}
    (hP : P ∈ tabSet (N + 1) sh c) :
    (shape (dropMax N P), dropMax N P) ∈ pairSet N sh c m := by
  obtain ⟨hPtab, hPsh, hPlt, hPcount⟩ := hP
  have hcountN : P.flatten.count N = c N := hPcount N (Nat.lt_succ_self N)
  have hsum := sum_shape_dropMax hPtab hPlt
  refine ⟨⟨isPart_shape (isTableau_dropMax hPtab),
      show (shape (dropMax N P)).sum = m by rw [hPsh] at hsum; omega⟩,
    hPsh ▸ horizStrip_shape_dropMax hPtab hPlt,
    isTableau_dropMax hPtab, rfl, fun x hx => lt_of_mem_flatten_dropMax hPtab hx, fun i hi => ?_⟩
  rw [count_flatten_dropMax hPtab, ite_eq_left hi]
  exact hPcount i (by omega)

lemma addMax_mem_tabSet (hsh : IsPart sh) (hm : m + c N = sh.sum)
    {x : (List ℕ) × List (List ℕ)} (hx : x ∈ pairSet N sh c m) :
    addMax N sh x.2 ∈ tabSet (N + 1) sh c := by
  obtain ⟨⟨hnu, hnusum⟩, hstrip, hQtab, hQsh, hQlt, hQcount⟩ := hx
  have hstrip' : HorizStrip sh (shape x.2) := by rw [hQsh]; exact hstrip
  have hAtab : IsTableau (addMax N sh x.2) := isTableau_addMax hsh hQtab hstrip' hQlt
  have hAlt : ∀ y ∈ (addMax N sh x.2).flatten, y < N + 1 :=
    fun y hy => lt_of_mem_flatten_addMax hstrip' hQlt hy
  have hdrop : dropMax N (addMax N sh x.2) = x.2 := dropMax_addMax hsh hQtab hstrip' hQlt
  refine ⟨hAtab, shape_addMax hstrip', hAlt, fun i hi => ?_⟩
  rcases lt_or_ge i N with hiN | hiN
  · have := count_flatten_dropMax hAtab (N := N) i
    rw [hdrop, ite_eq_left hiN] at this
    rw [← this]
    exact hQcount i hiN
  · have hiN' : i = N := by omega
    subst hiN'
    have hsum := sum_shape_dropMax hAtab hAlt
    rw [hdrop, hQsh, shape_addMax hstrip', hnusum] at hsum
    omega

lemma addMax_dropMax_of_mem {P : List (List ℕ)} (hP : P ∈ tabSet (N + 1) sh c) :
    addMax N sh (dropMax N P) = P := by
  obtain ⟨hPtab, hPsh, hPlt, -⟩ := hP
  rw [← hPsh]
  exact addMax_dropMax hPtab hPlt

lemma dropMax_addMax_of_mem (hsh : IsPart sh) {x : (List ℕ) × List (List ℕ)}
    (hx : x ∈ pairSet N sh c m) :
    (shape (dropMax N (addMax N sh x.2)), dropMax N (addMax N sh x.2)) = x := by
  obtain ⟨⟨hnu, hnusum⟩, hstrip, hQtab, hQsh, hQlt, -⟩ := hx
  have hstrip' : HorizStrip sh (shape x.2) := by rw [hQsh]; exact hstrip
  have hdrop : dropMax N (addMax N sh x.2) = x.2 := dropMax_addMax hsh hQtab hstrip' hQlt
  rw [hdrop, hQsh]

/-- Removing the largest letter is a bijection between the tableaux of shape `sh` with
letters `< N + 1` and content `c` and the pairs of a shape `nu` with `sh / nu` a
horizontal strip and a tableau of shape `nu` with letters `< N` and content `c`. -/
noncomputable def dropMaxEquiv (hsh : IsPart sh) (hm : m + c N = sh.sum) :
    (tabSet (N + 1) sh c) ≃ (pairSet N sh c m) where
  toFun P := ⟨(shape (dropMax N P.1), dropMax N P.1), dropMax_mem_pairSet hm P.2⟩
  invFun x := ⟨addMax N sh x.1.2, addMax_mem_tabSet hsh hm x.2⟩
  left_inv P := Subtype.ext (addMax_dropMax_of_mem P.2)
  right_inv x := Subtype.ext (dropMax_addMax_of_mem hsh x.2)

/-- The pairs of a shape and a tableau, sorted by shape. -/
def pairSetEquivSigma (N : ℕ) (sh : List ℕ) (c : ℕ → ℕ) (m : ℕ) :
    (pairSet N sh c m) ≃
      Σ nu : {p : List ℕ // IsPart p ∧ p.sum = m},
        {Q : List (List ℕ) // HorizStrip sh nu.1 ∧ Q ∈ tabSet N nu.1 c} where
  toFun x := ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩
  invFun s := ⟨(s.1.1, s.2.1), ⟨s.1.2, s.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

open Classical in
/-- **The recursion on the largest letter**: a tableau with letters `< N + 1` is a tableau
with letters `< N` together with a horizontal strip of boxes filled with the letter `N`.
This is the combinatorial content of the Pieri rule. -/
theorem kostkaNum_succ (hsh : IsPart sh) (hm : m + c N = sh.sum) :
    kostkaNum (N + 1) sh c
      = ∑ nu : {p : List ℕ // IsPart p ∧ p.sum = m},
          if HorizStrip sh nu.1 then kostkaNum N nu.1 c else 0 := by
  classical
  haveI : ∀ nu : {p : List ℕ // IsPart p ∧ p.sum = m},
      Finite {Q : List (List ℕ) // HorizStrip sh nu.1 ∧ Q ∈ tabSet N nu.1 c} := by
    intro nu
    haveI : Finite (tabSet N nu.1 c) := finite_tabSet N nu.1 c
    refine Finite.of_injective (fun Q => (⟨Q.1, Q.2.2⟩ : tabSet N nu.1 c)) ?_
    intro x y h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext h
  rw [kostkaNum, Nat.card_congr ((dropMaxEquiv hsh hm).trans (pairSetEquivSigma N sh c m)),
    Nat.card_sigma]
  refine Finset.sum_congr rfl fun nu _ => ?_
  by_cases hstrip : HorizStrip sh nu.1
  · rw [ite_eq_left hstrip, kostkaNum]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun Q => and_iff_right hstrip)
  · rw [ite_eq_right hstrip]
    have : IsEmpty {Q : List (List ℕ) // HorizStrip sh nu.1 ∧ Q ∈ tabSet N nu.1 c} :=
      ⟨fun Q => hstrip Q.2.1⟩
    exact Nat.card_of_isEmpty

end List
