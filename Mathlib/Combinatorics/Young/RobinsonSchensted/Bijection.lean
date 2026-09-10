/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.RobinsonSchensted.RecordingTableau
public import Mathlib.Combinatorics.Young.RobinsonSchensted.ReverseInsertion

/-!
# The Robinson–Schensted correspondence is a bijection

A Lean 4 port of the surjectivity part of the Robinson–Schensted correspondence of
`theories/LRrule/Schensted.v` from [Coq-Combi](https://github.com/math-comp/Coq-Combi).

Every pair `(P, Q)` consisting of a tableau `P` and a standard tableau `Q` of the same
shape is the image of a (unique) word under `w ↦ (RS w, RSQ w)`.  The word is
reconstructed by repeatedly removing the box carrying the largest label of `Q` and
undoing the corresponding Schensted insertion in `P`.

## Main definitions

* `Young.remBox Q i` : remove the last box of row `i` of `Q`.

## Main results

* `Young.remBox_spec` : removing the last box of a row at a removable corner of a tableau
  yields a tableau, and adding the box back gives the original tableau.
* `Young.recTab_rowsOf` : a standard tableau is the recording tableau of its recording
  word.
* `Young.exists_word_RS_RSQ` : surjectivity of the Robinson–Schensted correspondence.
* `Young.RS_RSQ_bijOn` : the Robinson–Schensted correspondence is a bijection between
  words and pairs (tableau, standard tableau of the same shape).
-/

@[expose] public section

namespace Young

open List

/-! ### Prefixes and domination -/

/-- A prefix of a dominating row still dominates. -/
lemma Dominate.of_prefix {T : Type*} [LinearOrder T] {u u' v : List T} (h : Dominate u v)
    (hp : u' <+: u) : Dominate u' v := by
  refine dominate_of_getElem (le_trans hp.length_le h.length_le) ?_
  intro i hi
  rw [hp.getElem hi]
  exact h.getElem_lt i (lt_of_lt_of_le hi hp.length_le)

/-! ### Removing the last box of a row -/

/-- Remove the last box of row `i` of `Q`; the row itself disappears if it becomes
empty. -/
def remBox : List (List ℕ) → ℕ → List (List ℕ)
  | [], _ => []
  | q0 :: q, 0 => if q0.dropLast = [] then q else q0.dropLast :: q
  | q0 :: q, (i + 1) => q0 :: remBox q i

@[simp] lemma remBox_nil (i : ℕ) : remBox [] i = [] := by cases i <;> rfl

lemma remBox_cons_zero (q0 : List ℕ) (q : List (List ℕ)) :
    remBox (q0 :: q) 0 = if q0.dropLast = [] then q else q0.dropLast :: q := rfl

@[simp] lemma remBox_cons_succ (q0 : List ℕ) (q : List (List ℕ)) (i : ℕ) :
    remBox (q0 :: q) (i + 1) = q0 :: remBox q i := rfl

/-- Removing the last box of a row at a removable corner of a tableau yields a tableau,
and adding the box back gives the original tableau. -/
lemma remBox_spec {q : List (List ℕ)} (h : IsTableau q) {i n : ℕ} (hi : i < q.length)
    (hlast : (q.getD i []).getLast? = some n) (hc : IsRemCorner (shape q) i) :
    IsTableau (remBox q i) ∧ addBox (remBox q i) i n = q ∧ i ≤ (remBox q i).length ∧
      ((remBox q i).headD []) <+: (q.headD []) := by
  induction q generalizing i with
  | nil => simp at hi
  | cons q0 q ih =>
    obtain ⟨hne, hrow, hdom, htab⟩ := h
    cases i with
    | zero =>
      rw [IsRemCorner, getD_shape, getD_shape] at hc
      simp only [List.getD_cons_zero] at hc hlast
      have hhead : (q0 :: q).getD 1 [] = q.headD [] := by cases q <;> rfl
      rw [hhead] at hc
      have ht0 : q0.dropLast ++ [n] = q0 := List.dropLast_append_getLast? n hlast
      have hlen : q0.dropLast.length + 1 = q0.length := by rw [← ht0]; simp
      by_cases hdl : q0.dropLast = []
      · have h1 : q0.length = 1 := by rw [← hlen, hdl]; rfl
        have hq : q = [] := by
          cases q with
          | nil => rfl
          | cons q1 q2 =>
            exfalso
            have h2 : 0 < q1.length := List.length_pos_iff.2 htab.1
            simp only [List.headD_cons] at hc
            omega
        subst hq
        refine ⟨by simp [remBox_cons_zero, hdl], ?_, by simp [remBox_cons_zero, hdl], ?_⟩
        · rw [remBox_cons_zero, ite_eq_left hdl, addBox_nil, ← ht0, hdl]
          rfl
        · rw [remBox_cons_zero, ite_eq_left hdl]
          simp
      · have hrem : remBox (q0 :: q) 0 = q0.dropLast :: q := by
          rw [remBox_cons_zero, ite_eq_right hdl]
        rw [hrem]
        refine ⟨⟨hdl, ?_, ?_, htab⟩, ?_, Nat.zero_le _, ?_⟩
        · exact List.IsChain.sublist hrow (List.dropLast_sublist q0)
        · refine dominate_of_getElem (by omega) ?_
          intro k hk
          rw [List.getElem_dropLast]
          exact hdom.getElem_lt k hk
        · rw [addBox_cons_zero, ht0]
        · simpa using List.dropLast_prefix q0
    | succ j =>
      have hij : j < q.length := by simpa using hi
      have hcj : IsRemCorner (shape q) j := by
        rw [IsRemCorner, getD_shape, getD_shape] at hc ⊢
        simpa using hc
      have hlastj : (q.getD j []).getLast? = some n := by simpa using hlast
      obtain ⟨htab', hadd, hile, hpre⟩ := ih htab hij hlastj hcj
      refine ⟨⟨hne, hrow, ?_, htab'⟩, ?_, ?_, ?_⟩
      · exact hdom.of_prefix hpre
      · rw [remBox_cons_succ, addBox_cons_succ, hadd]
      · simpa using hile
      · simp

/-! ### The box carrying the largest label of a standard tableau -/

/-- In a standard tableau with `n + 1` boxes, the largest label `n` sits at the end of its
row, and that box is a removable corner. -/
lemma stdTab_max_spec {Q : List (List ℕ)} (hQ : IsStdTab Q) {n : ℕ} (hn : sizeTab Q = n + 1) :
    rowIdx Q n < Q.length ∧ (Q.getD (rowIdx Q n) []).getLast? = some n ∧
      IsRemCorner (shape Q) (rowIdx Q n) := by
  have hmem : n ∈ toWord Q := (mem_toWord_iff_of_isStdTab hQ n).2 (by omega)
  obtain ⟨hlt, hmemR, -⟩ := rowIdx_spec (mem_toWord_iff.1 hmem)
  set i := rowIdx Q n with hi
  set R := Q.getD i [] with hR
  have hRmem : R ∈ Q := by rw [hR, List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
  have hle : ∀ x ∈ R, x ≤ n := by
    intro x hx
    have hxw : x ∈ toWord Q := mem_toWord_iff.2 ⟨R, hRmem, hx⟩
    have := (mem_toWord_iff_of_isStdTab hQ x).1 hxw
    omega
  have hRne : R ≠ [] := by
    intro h0
    rw [h0] at hmemR
    simp at hmemR
  have hRpos : 0 < R.length := List.length_pos_iff.2 hRne
  obtain ⟨m, hm⟩ : ∃ m, R.getLast? = some m := by
    cases h0 : R.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 h0) hRne
    | some m => exact ⟨m, rfl⟩
  have hrow : IsRow R := hQ.1.isRow_getD i
  have hnm : n ≤ m := le_getLast_of_pairwise_le (List.isChain_iff_pairwise.1 hrow) hm hmemR
  have hmn : m ≤ n := hle m (List.mem_of_getLast? hm)
  rw [le_antisymm hmn hnm] at hm
  refine ⟨hlt, hm, ?_⟩
  rw [IsRemCorner, getD_shape, getD_shape, ← hR]
  have hdom : Dominate (Q.getD (i + 1) []) R := hQ.1.dominate_getD (Nat.lt_succ_self i)
  rcases lt_or_eq_of_le hdom.length_le with h | h
  · exact h
  · exfalso
    have hidx : R.length - 1 < (Q.getD (i + 1) []).length := by omega
    have h1 := hdom.getElem_lt (R.length - 1) hidx
    have h2 : R[R.length - 1]'(by omega) = n := by
      have h3 : (List.getLast? R) = R[R.length - 1]? := List.getLast?_eq_getElem?
      rw [hm, List.getElem?_eq_getElem (by omega)] at h3
      exact (Option.some.inj h3).symm
    have hrowmem : Q.getD (i + 1) [] ∈ Q := by
      have hlt' : i + 1 < Q.length := by
        by_contra hcon
        rw [List.getD_eq_default _ _ (by omega)] at hidx
        simp at hidx
      rw [List.getD_eq_getElem _ _ hlt']
      exact List.getElem_mem hlt'
    have hxw : (Q.getD (i + 1) [])[R.length - 1] ∈ toWord Q :=
      mem_toWord_iff.2 ⟨_, hrowmem, List.getElem_mem hidx⟩
    have hxle := (mem_toWord_iff_of_isStdTab hQ _).1 hxw
    rw [h2] at h1
    omega

/-- Removing the box of the largest label of a standard tableau leaves a standard
tableau with one box less. -/
lemma remBox_max_spec {Q : List (List ℕ)} (hQ : IsStdTab Q) {n : ℕ} (hn : sizeTab Q = n + 1) :
    IsStdTab (remBox Q (rowIdx Q n)) ∧ sizeTab (remBox Q (rowIdx Q n)) = n ∧
      addBox (remBox Q (rowIdx Q n)) (rowIdx Q n) n = Q ∧
      rowIdx Q n ≤ (remBox Q (rowIdx Q n)).length := by
  obtain ⟨hlt, hlast, hc⟩ := stdTab_max_spec hQ hn
  obtain ⟨htab', hadd, hile, -⟩ := remBox_spec hQ.1 hlt hlast hc
  set i := rowIdx Q n
  set Q' := remBox Q i
  have hperm : (toWord Q).Perm (n :: toWord Q') := by
    rw [← hadd]
    exact perm_toWord_addBox Q' i n
  have hlenQ : (toWord Q).length = n + 1 := by rw [length_toWord, hn]
  have hstd : (toWord Q).Perm (List.range (n + 1)) := by
    have := hQ.2
    rwa [IsStd, hlenQ] at this
  have hcons : (n :: toWord Q').Perm (n :: List.range n) := by
    refine hperm.symm.trans (hstd.trans ?_)
    rw [List.range_succ]
    exact List.perm_append_singleton n (List.range n)
  have hQ'perm : (toWord Q').Perm (List.range n) := hcons.cons_inv
  have hsize : sizeTab Q' = n := by
    rw [← length_toWord, hQ'perm.length_eq, List.length_range]
  refine ⟨⟨htab', ?_⟩, hsize, hadd, hile⟩
  rw [IsStd, hQ'perm.length_eq, List.length_range]
  exact hQ'perm

/-- The recording word of a standard tableau ends with the row of its largest label. -/
lemma rowsOf_eq_concat {Q : List (List ℕ)} (hQ : IsStdTab Q) {n : ℕ} (hn : sizeTab Q = n + 1) :
    rowsOf Q = rowsOf (remBox Q (rowIdx Q n)) ++ [rowIdx Q n] := by
  obtain ⟨hQ', hsize, hadd, hile⟩ := remBox_max_spec hQ hn
  set i := rowIdx Q n
  set Q' := remBox Q i
  have hmap : (List.range n).map (rowIdx Q) = (List.range n).map (rowIdx Q') := by
    refine List.map_congr_left ?_
    intro x hx
    rw [List.mem_range] at hx
    have hex : ∃ r ∈ Q', x ∈ r :=
      mem_toWord_iff.1 ((mem_toWord_iff_of_isStdTab hQ' x).2 (by omega))
    rw [← hadd]
    exact rowIdx_addBox_of_ne hile (by omega) hex
  rw [rowsOf, hn, List.range_succ, List.map_append, hmap, rowsOf, hsize]
  rfl

/-- A standard tableau is the recording tableau of its own recording word. -/
theorem recTab_rowsOf {Q : List (List ℕ)} (hQ : IsStdTab Q) : recTab (rowsOf Q) = Q := by
  generalize hn : sizeTab Q = n
  induction n generalizing Q with
  | zero =>
    have h0 : Q = [] := hQ.1.eq_nil_of_sizeTab_eq_zero hn
    subst h0
    rfl
  | succ n ih =>
    obtain ⟨hQ', hsize, hadd, -⟩ := remBox_max_spec hQ hn
    have hrows := rowsOf_eq_concat hQ hn
    have hlen : (rowsOf (remBox Q (rowIdx Q n))).length = n := by
      rw [rowsOf, List.length_map, List.length_range, hsize]
    rw [hrows, recTab_concat, hlen, ih hQ' hsize, hadd]

/-! ### Surjectivity of the Robinson–Schensted correspondence -/

variable {T : Type*} [LinearOrder T]

/-- Every pair consisting of a tableau and a standard tableau of the same shape is the
image of a word under `Young.RSmap` (Coq `RS_bij_2`). -/
theorem exists_word_RSmap {P : List (List T)} (hP : IsTableau P) {Q : List (List ℕ)}
    (hQ : IsStdTab Q) (hμ : shape Q = shape P) : ∃ w : List T, RSmap w = (P, rowsOf Q) := by
  generalize hn : sizeTab Q = n
  induction n generalizing P Q with
  | zero =>
    have h0 : Q = [] := hQ.1.eq_nil_of_sizeTab_eq_zero hn
    subst h0
    have hP0 : P = [] := by
      have hs : shape P = [] := by rw [← hμ]; rfl
      rw [shape] at hs
      exact List.map_eq_nil_iff.1 hs
    subst hP0
    exact ⟨[], rfl⟩
  | succ n ih =>
    obtain ⟨hQ', hsize, hadd, hile⟩ := remBox_max_spec hQ hn
    obtain ⟨-, hlast, hc⟩ := stdTab_max_spec hQ hn
    set i := rowIdx Q n
    set Q' := remBox Q i
    have hcP : IsRemCorner (shape P) i := by rw [← hμ]; exact hc
    obtain ⟨P', l, -, htabP', hins, hbump, -⟩ := invInsTab_spec hP hcP
    have hμP : shape P = incrNth (shape P') i := by rw [← hins, shape_insTab, hbump]
    have hμQ : shape Q = incrNth (shape Q') i := by rw [← hadd, shape_addBox hile]
    have hμ' : shape Q' = shape P' := by
      have h3 : IsPart (incrNth (shape P') i) := by rw [← hμP]; exact isPart_shape hP
      have h4 : IsPart (incrNth (shape Q') i) := by rw [← hμQ]; exact isPart_shape hQ.1
      have e1 : decrNth (incrNth (shape P') i) i = shape P' :=
        decrNth_incrNth (isPart_shape htabP') h3
      have e2 : decrNth (incrNth (shape Q') i) i = shape Q' :=
        decrNth_incrNth (isPart_shape hQ'.1) h4
      rw [← e1, ← e2, ← hμP, ← hμQ, hμ]
    obtain ⟨w', hw'⟩ := ih htabP' hQ' hμ' hsize
    refine ⟨w' ++ [l], ?_⟩
    rw [RSmap_concat, hw']
    dsimp only
    rw [hins, hbump, rowsOf_eq_concat hQ hn]

/-- **Surjectivity of the Robinson–Schensted correspondence**: every pair consisting of a
tableau `P` and a standard tableau `Q` of the same shape comes from a word. -/
theorem exists_word_RS_RSQ {P : List (List T)} (hP : IsTableau P) {Q : List (List ℕ)}
    (hQ : IsStdTab Q) (hμ : shape Q = shape P) : ∃ w : List T, RS w = P ∧ RSQ w = Q := by
  obtain ⟨w, hw⟩ := exists_word_RSmap hP hQ hμ
  refine ⟨w, ?_, ?_⟩
  · rw [← RSmap_fst, hw]
  · rw [RSQ]
    simp only [hw]
    exact recTab_rowsOf hQ

/-- **The Robinson–Schensted correspondence is a bijection** between words over a linear
order and pairs consisting of a tableau and a standard tableau of the same shape. -/
theorem RS_RSQ_bijOn :
    Set.BijOn (fun w : List T => (RS w, RSQ w)) Set.univ
      {p : List (List T) × List (List ℕ) |
        IsTableau p.1 ∧ IsStdTab p.2 ∧ shape p.2 = shape p.1} := by
  refine ⟨fun w _ => ⟨isTableau_RS w, isStdTab_RSQ w, shape_RSQ w⟩, ?_, ?_⟩
  · intro w _ w' _ h
    exact RS_RSQ_injective (congrArg Prod.fst h) (congrArg Prod.snd h)
  · rintro ⟨P, Q⟩ ⟨hP, hQ, hμ⟩
    obtain ⟨w, h1, h2⟩ := exists_word_RS_RSQ hP hQ hμ
    exact ⟨w, Set.mem_univ w, by simp [h1, h2]⟩

/-- Restricted to standard words, the Robinson–Schensted correspondence is a bijection
onto the pairs of standard tableaux of the same shape. -/
theorem RS_RSQ_bijOn_isStd :
    Set.BijOn (fun w : List ℕ => (RS w, RSQ w)) {w | IsStd w}
      {p : List (List ℕ) × List (List ℕ) |
        IsStdTab p.1 ∧ IsStdTab p.2 ∧ shape p.1 = shape p.2} := by
  refine ⟨fun w hw => ⟨isStdTab_RS hw, isStdTab_RSQ w, (shape_RSQ w).symm⟩, ?_, ?_⟩
  · intro w _ w' _ h
    exact RS_RSQ_injective (congrArg Prod.fst h) (congrArg Prod.snd h)
  · rintro ⟨P, Q⟩ ⟨hP, hQ, hμ⟩
    obtain ⟨w, h1, h2⟩ := exists_word_RS_RSQ hP.1 hQ hμ.symm
    have hperm := perm_toWord_RS w
    rw [h1] at hperm
    exact ⟨w, hP.2.of_perm hperm.symm, by simp [h1, h2]⟩

end Young
