/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Tableau.Standard
import Mathlib.Combinatorics.Young.RobinsonSchensted.Injective

/-!
# The recording tableau of the Robinson–Schensted correspondence

A Lean 4 port of the pair-of-tableaux part of `theories/LRrule/Schensted.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

The recording word of `List.RSmap` lists the rows in which the successive boxes of the
insertion tableau appear.  Labelling the box created at step `k` by `k` produces the
*recording tableau*, a standard tableau of the same shape as the insertion tableau.  The
Robinson–Schensted correspondence therefore sends a word to a pair of tableaux of the
same shape, the second of which is standard, and this pair determines the word.

## Main definitions

* `List.addBox q i k` : append the label `k` at the end of row `i` of `q`.
* `List.recTab rows` : the tableau recording the rows listed by `rows`.
* `List.RSQ w` : the recording tableau of the word `w` (Coq the second component of
  `RStabmap`).
* `List.rowsOf Q` : the recording word read off a recording tableau.

## Main results

* `List.shape_addBox` : adding a box changes the shape by `List.incrNth`.
* `List.isTableau_addBox` : adding a box with a larger label at an addable corner of a
  tableau yields a tableau.
* `List.shape_RSQ` : the recording tableau has the same shape as the insertion tableau.
* `List.isStdTab_RSQ` : the recording tableau is a standard tableau.
* `List.rowsOf_RSQ` : the recording word can be read off the recording tableau.
* `List.RS_RSQ_injective` : the pair (insertion tableau, recording tableau) determines
  the word.
-/

namespace List

open List

/-! ### Adding a labelled box -/

/-- Append the label `k` at the end of row `i` of `q`. -/
def addBox : List (List ℕ) → ℕ → ℕ → List (List ℕ)
  | [], _, k => [[k]]
  | q0 :: q, 0, k => (q0 ++ [k]) :: q
  | q0 :: q, i + 1, k => q0 :: addBox q i k

@[simp] lemma addBox_nil (i k : ℕ) : addBox [] i k = [[k]] := by cases i <;> rfl

@[simp] lemma addBox_cons_zero (q0 : List ℕ) (q : List (List ℕ)) (k : ℕ) :
    addBox (q0 :: q) 0 k = (q0 ++ [k]) :: q := rfl

@[simp] lemma addBox_cons_succ (q0 : List ℕ) (q : List (List ℕ)) (i k : ℕ) :
    addBox (q0 :: q) (i + 1) k = q0 :: addBox q i k := rfl

/-- Adding a box at the end of row `i` changes the shape by `List.incrNth`. -/
lemma shape_addBox {q : List (List ℕ)} {i : ℕ} (hi : i ≤ q.length) (k : ℕ) :
    shape (addBox q i k) = incrNth (shape q) i := by
  induction q generalizing i with
  | nil =>
    obtain rfl : i = 0 := by simpa using hi
    rfl
  | cons q0 q ih =>
    cases i with
    | zero => simp [shape]
    | succ j =>
      rw [addBox_cons_succ, shape_cons, shape_cons, incrNth_cons_succ,
        ih (by simpa using hi)]

lemma length_addBox {q : List (List ℕ)} {i : ℕ} (hi : i ≤ q.length) (k : ℕ) :
    (addBox q i k).length = max q.length (i + 1) := by
  have := congrArg List.length (shape_addBox hi k)
  rwa [length_shape, length_incrNth, length_shape] at this

/-- Adding a box permutes the letters of the reading word. -/
lemma perm_toWord_addBox (q : List (List ℕ)) (i k : ℕ) :
    (toWord (addBox q i k)).Perm (k :: toWord q) := by
  induction q generalizing i with
  | nil => simp [toWord]
  | cons q0 q ih =>
    cases i with
    | zero =>
      rw [addBox_cons_zero, toWord_cons, toWord_cons, ← List.append_assoc]
      exact List.perm_append_singleton k _
    | succ j =>
      rw [addBox_cons_succ, toWord_cons, toWord_cons]
      exact ((ih j).append_right q0).trans (by rw [List.cons_append])

/-- Adding a box with a label larger than all entries, at an addable corner of a tableau,
yields a tableau. -/
lemma isTableau_addBox {q : List (List ℕ)} {i k : ℕ} (htab : IsTableau q)
    (hlt : ∀ x ∈ toWord q, x < k) (hc : IsAddCorner (shape q) i) (hi : i ≤ q.length) :
    IsTableau (addBox q i k) := by
  induction q generalizing i with
  | nil => exact ⟨by simp, by simp [IsRow], by simp, by simp⟩
  | cons q0 q ih =>
    obtain ⟨hne, hrow, hdom, htab'⟩ := htab
    have hq0 : ∀ x ∈ q0, x < k := by
      intro x hx
      exact hlt x (by rw [toWord_cons]; exact List.mem_append_right _ hx)
    have hq' : ∀ x ∈ toWord q, x < k := by
      intro x hx
      exact hlt x (by rw [toWord_cons]; exact List.mem_append_left _ hx)
    have hq0pos : 0 < q0.length := List.length_pos_iff.2 hne
    cases i with
    | zero =>
      refine ⟨by simp, ?_, ?_, htab'⟩
      · rw [IsRow, List.isChain_iff_pairwise, List.pairwise_append]
        refine ⟨by rw [← List.isChain_iff_pairwise]; exact hrow, by simp, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        exact hb ▸ le_of_lt (hq0 a ha)
      · exact hdom.append_right [k]
    | succ j =>
      have hcq : IsAddCorner (shape q) j := by
        cases j with
        | zero => exact Or.inl rfl
        | succ m =>
          refine Or.inr ?_
          rcases hc with h | h
          · exact absurd h (by omega)
          · simpa using h
      have hij : j ≤ q.length := by simpa using hi
      refine ⟨hne, hrow, ?_, ih htab' hq' hcq hij⟩
      cases q with
      | nil =>
        rw [addBox_nil]
        refine dominate_of_getElem (Nat.succ_le_of_lt hq0pos) ?_
        intro m hm
        have hm0 : m = 0 := by simpa using hm
        subst hm0
        simpa using hq0 q0[0] (List.getElem_mem hq0pos)
      | cons q1 q' =>
        cases j with
        | zero =>
          rw [addBox_cons_zero]
          have hlen : q1.length < q0.length := by
            rcases hc with h | h
            · exact absurd h (by omega)
            · simpa [shape] using h
          simp only [List.headD_cons]
          refine dominate_of_getElem (by simp; omega) ?_
          intro m hm
          simp only [List.length_append, List.length_singleton] at hm
          rcases lt_or_ge m q1.length with hlt' | hge
          · rw [List.getElem_append_left hlt']
            have := hdom.getElem_lt m hlt'
            simpa using this
          · have hm1 : m = q1.length := by omega
            subst hm1
            rw [List.getElem_append_right (by omega)]
            simp only [Nat.sub_self, List.getElem_singleton]
            exact hq0 q0[q1.length] (List.getElem_mem (by omega))
        | succ m =>
          rw [addBox_cons_succ]
          simpa using hdom

/-! ### The recording tableau -/

/-- Auxiliary construction of the recording tableau: the boxes are added in the rows
listed by `rows`, and labelled by their position in `rows`. -/
def recTabAux (rows : List ℕ) : List (List ℕ) × ℕ :=
  rows.foldl (fun p i => (addBox p.1 i p.2, p.2 + 1)) ([], 0)

/-- The recording tableau of a list of rows. -/
def recTab (rows : List ℕ) : List (List ℕ) := (recTabAux rows).1

@[simp] lemma recTab_nil : recTab [] = [] := rfl

lemma recTabAux_snd (rows : List ℕ) : (recTabAux rows).2 = rows.length := by
  induction rows using List.reverseRecOn with
  | nil => rfl
  | append_singleton rows i ih => simp [recTabAux] at ih ⊢; omega

lemma recTab_concat (rows : List ℕ) (i : ℕ) :
    recTab (rows ++ [i]) = addBox (recTab rows) i rows.length := by
  have h := recTabAux_snd rows
  simp only [recTab, recTabAux, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [show ((rows.foldl (fun p i => (addBox p.1 i p.2, p.2 + 1)) ([], 0)).2) = rows.length from h]

lemma perm_toWord_recTab (rows : List ℕ) :
    (toWord (recTab rows)).Perm (List.range rows.length) := by
  induction rows using List.reverseRecOn with
  | nil => simp [toWord]
  | append_singleton rows i ih =>
    rw [recTab_concat]
    calc (toWord (addBox (recTab rows) i rows.length)).Perm
          (rows.length :: toWord (recTab rows)) := perm_toWord_addBox _ i _
      _ ~ (rows.length :: List.range rows.length) := ih.cons _
      _ ~ (List.range rows.length ++ [rows.length]) :=
          (List.perm_append_singleton _ _).symm
      _ = List.range (rows.length + 1) := List.range_succ.symm
      _ = List.range (rows ++ [i]).length := by simp

lemma lt_of_mem_toWord_recTab {rows : List ℕ} {x : ℕ} (hx : x ∈ toWord (recTab rows)) :
    x < rows.length := by
  have := (perm_toWord_recTab rows).mem_iff.1 hx
  simpa using this

lemma isStd_toWord_recTab (rows : List ℕ) : IsStd (toWord (recTab rows)) := by
  have h := perm_toWord_recTab rows
  rw [IsStd, h.length_eq, List.length_range]
  exact h

/-! ### The pair of tableaux of a word -/

variable {T : Type*} [LinearOrder T]

/-- The recording tableau of the word `w`. -/
def RSQ (w : List T) : List (List ℕ) := recTab (RSmap w).2

lemma length_RSmap_snd (w : List T) : (RSmap w).2.length = w.length := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w l ih => rw [RSmap_concat]; simp [ih]

lemma RSQ_concat (w : List T) (l : T) :
    RSQ (w ++ [l]) = addBox (RSQ w) (bumpRow (RS w) l) w.length := by
  rw [RSQ, RSmap_concat, RSmap_fst, recTab_concat, length_RSmap_snd]
  rfl

/-- The recording tableau has the same shape as the insertion tableau. -/
theorem shape_RSQ (w : List T) : shape (RSQ w) = shape (RS w) := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w l ih =>
    have hlen : (RSQ w).length = (RS w).length := by
      have := congrArg List.length ih
      rwa [length_shape, length_shape] at this
    have hle : bumpRow (RS w) l ≤ (RSQ w).length := by
      rw [hlen]; exact bumpRow_le_length _ l
    rw [RSQ_concat, shape_addBox hle, ih, RS_concat, shape_insTab]

/-- The recording tableau is a standard tableau. -/
theorem isStdTab_RSQ (w : List T) : IsStdTab (RSQ w) := by
  refine ⟨?_, isStd_toWord_recTab _⟩
  induction w using List.reverseRecOn with
  | nil => simp [RSQ]
  | append_singleton w l ih =>
    have hshape := shape_RSQ w
    have hlen : (RSQ w).length = (RS w).length := by
      have := congrArg List.length hshape
      rwa [length_shape, length_shape] at this
    have hle : bumpRow (RS w) l ≤ (RSQ w).length := by
      rw [hlen]; exact bumpRow_le_length _ l
    have hlt : ∀ x ∈ toWord (RSQ w), x < (RSmap w).2.length := by
      intro x hx
      exact lt_of_mem_toWord_recTab hx
    have hc : IsAddCorner (shape (RSQ w)) (bumpRow (RS w) l) := by
      rw [hshape]
      exact isAddCorner_bumpRow (isTableau_RS w) l
    rw [RSQ_concat]
    rw [← length_RSmap_snd w]
    exact isTableau_addBox ih hlt hc hle

/-! ### Recovering the recording word from the recording tableau -/

lemma mem_toWord_iff {Q : List (List ℕ)} {x : ℕ} : x ∈ toWord Q ↔ ∃ r ∈ Q, x ∈ r := by
  simp [toWord]

lemma getD_addBox_of_ne {q : List (List ℕ)} {i k j : ℕ} (hi : i ≤ q.length) (hj : j ≠ i) :
    (addBox q i k).getD j [] = q.getD j [] := by
  induction q generalizing i j with
  | nil =>
    obtain rfl : i = 0 := by simpa using hi
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    simp
  | cons q0 q ih =>
    cases i with
    | zero =>
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      simp
    | succ i' =>
      cases j with
      | zero => simp
      | succ m =>
        rw [addBox_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
        exact ih (by simpa using hi) (by omega)

lemma getD_addBox_self {q : List (List ℕ)} {i k : ℕ} (hi : i ≤ q.length) :
    (addBox q i k).getD i [] = q.getD i [] ++ [k] := by
  induction q generalizing i with
  | nil =>
    obtain rfl : i = 0 := by simpa using hi
    simp
  | cons q0 q ih =>
    cases i with
    | zero => simp
    | succ i' =>
      rw [addBox_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
      exact ih (by simpa using hi)

/-- The index of the row of `Q` containing the label `k`. -/
def rowIdx (Q : List (List ℕ)) (k : ℕ) : ℕ := Q.findIdx (fun r => k ∈ r)

lemma rowIdx_eq_of {Q : List (List ℕ)} {k i : ℕ} (hi : i < Q.length) (hmem : k ∈ Q.getD i [])
    (hlt : ∀ j, j < i → k ∉ Q.getD j []) : rowIdx Q k = i := by
  rw [rowIdx, List.findIdx_eq hi]
  refine ⟨?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ hi] at hmem
    simpa using hmem
  · intro j hji
    have := hlt j hji
    rw [List.getD_eq_getElem _ _ (by omega)] at this
    simpa [rowIdx] using this

lemma rowIdx_spec {Q : List (List ℕ)} {k : ℕ} (h : ∃ r ∈ Q, k ∈ r) :
    rowIdx Q k < Q.length ∧ k ∈ Q.getD (rowIdx Q k) [] ∧
      ∀ j, j < rowIdx Q k → k ∉ Q.getD j [] := by
  have hlt : rowIdx Q k < Q.length := by
    refine List.findIdx_lt_length_of_exists ?_
    obtain ⟨r, hr, hkr⟩ := h
    exact ⟨r, hr, by simpa using hkr⟩
  refine ⟨hlt, ?_, ?_⟩
  · have := List.findIdx_getElem (p := fun r => decide (k ∈ r)) (xs := Q) (w := hlt)
    rw [List.getD_eq_getElem _ _ hlt]
    change k ∈ Q[rowIdx Q k]
    exact this
  · intro j hj
    have := List.not_of_lt_findIdx (p := fun r => decide (k ∈ r)) (xs := Q) hj
    rw [List.getD_eq_getElem _ _ (by omega)]
    simpa using this

lemma rowIdx_addBox_of_ne {Q : List (List ℕ)} {i k x : ℕ} (hi : i ≤ Q.length) (hx : x ≠ k)
    (hex : ∃ r ∈ Q, x ∈ r) : rowIdx (addBox Q i k) x = rowIdx Q x := by
  obtain ⟨hlt, hmem, hbelow⟩ := rowIdx_spec hex
  have hlen : Q.length ≤ (addBox Q i k).length := by
    rw [length_addBox hi]; exact le_max_left _ _
  refine rowIdx_eq_of (lt_of_lt_of_le hlt hlen) ?_ ?_
  · by_cases hii : rowIdx Q x = i
    · rw [hii, getD_addBox_self hi]
      rw [hii] at hmem
      exact List.mem_append_left _ hmem
    · rw [getD_addBox_of_ne hi hii]
      exact hmem
  · intro j hj
    by_cases hji : j = i
    · rw [hji, getD_addBox_self hi]
      intro hcon
      rcases List.mem_append.1 hcon with hc | hc
      · exact hbelow j hj (by rw [hji]; exact hc)
      · exact hx (List.mem_singleton.1 hc)
    · rw [getD_addBox_of_ne hi hji]
      exact hbelow j hj

lemma rowIdx_addBox_self {Q : List (List ℕ)} {i k : ℕ} (hi : i ≤ Q.length)
    (hk : ∀ r ∈ Q, k ∉ r) : rowIdx (addBox Q i k) k = i := by
  have hlen : i < (addBox Q i k).length := by
    rw [length_addBox hi]
    exact lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_right _ _)
  refine rowIdx_eq_of hlen ?_ ?_
  · rw [getD_addBox_self hi]
    exact List.mem_append_right _ (by simp)
  · intro j hj
    rw [getD_addBox_of_ne hi (by omega)]
    intro hcon
    have hjq : j < Q.length := by
      by_contra hcon'
      rw [List.getD_eq_default _ _ (by omega)] at hcon
      simp at hcon
    exact hk _ (List.getElem_mem hjq) (by rwa [List.getD_eq_getElem _ _ hjq] at hcon)

/-- The recording word read off a recording tableau. -/
def rowsOf (Q : List (List ℕ)) : List ℕ := (List.range (sizeTab Q)).map (rowIdx Q)

lemma sizeTab_RSQ (w : List T) : sizeTab (RSQ w) = w.length := by
  rw [sizeTab, shape_RSQ, ← sizeTab, sizeTab_RS]

/-- The recording word of `w` can be read off its recording tableau. -/
theorem rowsOf_RSQ (w : List T) : rowsOf (RSQ w) = (RSmap w).2 := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w l ih =>
    have hlenQ : (RSQ w).length = (RS w).length := by
      have := congrArg List.length (shape_RSQ w)
      rwa [length_shape, length_shape] at this
    have hle : bumpRow (RS w) l ≤ (RSQ w).length := by
      rw [hlenQ]; exact bumpRow_le_length _ l
    have hrows : (RSmap w).2.length = w.length := length_RSmap_snd w
    have hQ' : RSQ (w ++ [l]) = addBox (RSQ w) (bumpRow (RS w) l) w.length := RSQ_concat w l
    have hmem : ∀ x, x < w.length → ∃ r ∈ RSQ w, x ∈ r := by
      intro x hx
      refine mem_toWord_iff.1 ?_
      have := (perm_toWord_recTab (RSmap w).2).mem_iff (a := x)
      rw [RSQ]
      rw [this, List.mem_range, hrows]
      exact hx
    have hnot : ∀ r ∈ RSQ w, w.length ∉ r := by
      intro r hr hcon
      have : w.length ∈ toWord (RSQ w) := mem_toWord_iff.2 ⟨r, hr, hcon⟩
      rw [RSQ] at this
      have := lt_of_mem_toWord_recTab this
      omega
    rw [rowsOf, sizeTab_RSQ, List.length_append, List.length_singleton, List.range_succ,
      List.map_append, hQ']
    simp only [List.map_cons, List.map_nil]
    have h1 : (List.range w.length).map (rowIdx (addBox (RSQ w) (bumpRow (RS w) l) w.length)) =
        (List.range w.length).map (rowIdx (RSQ w)) := by
      refine List.map_congr_left ?_
      intro x hx
      rw [List.mem_range] at hx
      exact rowIdx_addBox_of_ne hle (by omega) (hmem x hx)
    rw [h1]
    have h2 : rowIdx (addBox (RSQ w) (bumpRow (RS w) l) w.length) w.length =
        bumpRow (RS w) l := rowIdx_addBox_self hle hnot
    rw [h2]
    have h3 : (List.range w.length).map (rowIdx (RSQ w)) = rowsOf (RSQ w) := by
      rw [rowsOf, sizeTab_RSQ]
    rw [h3, ih, RSmap_concat, RSmap_fst]

/-- **The Robinson–Schensted correspondence is injective**: the pair consisting of the
insertion tableau and the recording tableau determines the word. -/
theorem RS_RSQ_injective {w w' : List T} (h : RS w = RS w') (hQ : RSQ w = RSQ w') : w = w' := by
  refine RSmap_injective (Prod.ext ?_ ?_)
  · rw [RSmap_fst, RSmap_fst, h]
  · rw [← rowsOf_RSQ, ← rowsOf_RSQ, hQ]

end List
