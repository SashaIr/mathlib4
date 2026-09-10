/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.RobinsonSchensted.Injective

/-!
# Reverse insertion at a removable corner

A Lean 4 port of the remaining part of the reverse insertion theory of
`theories/LRrule/Schensted.v` from [Coq-Combi](https://github.com/math-comp/Coq-Combi).

`Young.invInsTab t i` removes the last box of row `i` of the tableau `t` and pushes the
removed letters upwards.  When the box removed is a *removable corner* of the shape of
`t`, this operation is exactly the inverse of Schensted insertion: it produces a tableau
`t'` and a letter `l` with `insTab t' l = t` and `bumpRow t' l = i`.

## Main results

* `Young.dominate_of_dominate_insRow` : domination can be undone (the converse of
  `Young.dominate_insRow_of_bumped`).
* `Young.invInsTab_spec` : reverse insertion at a removable corner succeeds and undoes
  insertion in a tableau (Coq `invinstabnrowK`).
-/

@[expose] public section

namespace Young

open List

variable {T : Type*} [LinearOrder T]

/-! ### Undoing domination -/

/-- The converse of `Young.dominate_insRow_of_bumped`: if the rows obtained after
inserting `l` in `r` and the bumped letter `b` in `u` dominate each other, then so did the
original rows. -/
lemma dominate_of_dominate_insRow {u r : List T} (hu : IsRow u) (hr : IsRow r) {l b : T}
    (hb : bumped r l = some b) (hdom : Dominate (insRow u b) (insRow r l)) : Dominate u r := by
  set p := insPos r l with hp
  set q := insPos u b with hq
  have hplen : p < r.length := insPos_lt_length_of_bumped hb
  have hbr : b = r[p]'hplen := bumped_eq_getElem hb
  have hrlen : (insRow r l).length = r.length := insRow_length_of_bumped hb
  have hulen : u.length ≤ r.length := by
    have h1 : u.length ≤ (insRow u b).length := length_le_insRow_length u b
    have h2 := hdom.length_le
    omega
  have hqp : q ≤ p := by
    by_contra hcon
    push Not at hcon
    have hq1 : q < (insRow u b).length := insPos_lt_insRow_length u b
    have hq2 : q < (insRow r l).length := lt_of_lt_of_le hq1 hdom.length_le
    have hqr : q < r.length := by omega
    have e1 : (insRow u b)[q]'hq1 = b := insRow_getElem_insPos_eq u b
    have e2 : (insRow r l)[q]'hq2 = r[q] := insRow_getElem_eq hqr (by omega) hq2
    have h3 := hdom.getElem_lt q hq1
    rw [e1, e2] at h3
    have h4 : b ≤ r[q] := by rw [hbr]; exact hr.getElem_le (le_of_lt hcon) hqr
    exact absurd h3 (not_lt.2 h4)
  refine dominate_of_getElem hulen ?_
  intro i hi
  have hir : i < r.length := lt_of_lt_of_le hi hulen
  have hiins : i < (insRow u b).length := lt_of_lt_of_le hi (length_le_insRow_length u b)
  have hiins' : i < (insRow r l).length := by omega
  rcases lt_or_ge i q with hlt | hge
  · have e1 : (insRow u b)[i] = u[i] := insRow_getElem_eq hi (by omega) hiins
    have e2 : (insRow r l)[i] = r[i] := insRow_getElem_eq hir (by omega) hiins'
    have h3 := hdom.getElem_lt i hiins
    rw [e1, e2] at h3
    exact h3
  · rcases le_or_gt i p with hip | hip
    · have hqu : q < u.length := lt_of_le_of_lt hge hi
      have hbu : b < u[q]'hqu := lt_of_getElem?_insPos (List.getElem?_eq_getElem hqu)
      calc r[i] ≤ r[p]'hplen := hr.getElem_le hip hplen
        _ = b := hbr.symm
        _ < u[q]'hqu := hbu
        _ ≤ u[i] := hu.getElem_le hge hi
    · have e1 : (insRow u b)[i] = u[i] := insRow_getElem_eq hi (by omega) hiins
      have e2 : (insRow r l)[i] = r[i] := insRow_getElem_eq hir (by omega) hiins'
      have h3 := hdom.getElem_lt i hiins
      rw [e1, e2] at h3
      exact h3

/-! ### Reverse insertion at a removable corner -/

/-- If every entry of a row is at most `b`, inserting `b` bumps nothing out. -/
lemma insPos_eq_length_of_forall_le {r : List T} {b : T} (h : ∀ y ∈ r, y ≤ b) :
    insPos r b = r.length := by
  induction r with
  | nil => rfl
  | cons x r ih =>
    rw [insPos_cons, ite_eq_right (not_lt.2 (h x List.mem_cons_self)),
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    simp

lemma bumped_eq_none_of_forall_le {r : List T} {b : T} (h : ∀ y ∈ r, y ≤ b) :
    bumped r b = none :=
  bumped_eq_none_iff.2 (insPos_eq_length_of_forall_le h)

/-- Coq `invinstabnrowK`: at a removable corner of its shape, reverse insertion in a
tableau succeeds, and it undoes Schensted insertion: it returns a tableau `t'` and a
letter `l` such that inserting `l` in `t'` gives back `t`, creating a box in row `i`. -/
theorem invInsTab_spec {t : List (List T)} (h : IsTableau t) {i : ℕ}
    (hc : IsRemCorner (shape t) i) :
    ∃ (t' : List (List T)) (l : T), invInsTab t i = some (t', l) ∧ IsTableau t' ∧
      insTab t' l = t ∧ bumpRow t' l = i ∧ l ∈ t.headD [] := by
  induction t generalizing i with
  | nil => simp [IsRemCorner] at hc
  | cons t0 t ih =>
    obtain ⟨hne, hrow, hdom, htab⟩ := h
    have hhead : (shape t).getD 0 0 = (t.headD []).length := by cases t <;> rfl
    cases i with
    | zero =>
      rw [IsRemCorner] at hc
      simp only [shape_cons, List.getD_cons_succ, List.getD_cons_zero] at hc
      rw [hhead] at hc
      cases hlast : t0.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.1 hlast) hne
      | some b =>
        have ht0 : t0.dropLast ++ [b] = t0 := List.dropLast_append_getLast? b hlast
        have hlen : t0.dropLast.length + 1 = t0.length := by rw [← ht0]; simp
        have hble : ∀ y ∈ t0, y ≤ b := fun y hy =>
          le_getLast_of_pairwise_le (List.isChain_iff_pairwise.1 hrow) hlast hy
        have hbne : bumped t0.dropLast b = none :=
          bumped_eq_none_of_forall_le fun y hy =>
            hble y (by rw [← ht0]; exact List.mem_append_left _ hy)
        by_cases hdl : t0.dropLast = []
        · have h1 : t0.length = 1 := by rw [← hlen, hdl]; rfl
          have ht : t = [] := by
            cases t with
            | nil => rfl
            | cons t1 t2 =>
              exfalso
              have h2 : 0 < t1.length := List.length_pos_iff.2 htab.1
              simp only [List.headD_cons] at hc
              omega
          subst ht
          refine ⟨[], b, ?_, by simp, ?_, rfl, ?_⟩
          · rw [invInsTab_cons_zero, hlast]; simp [hdl]
          · rw [insTab_nil, ← ht0, hdl]; rfl
          · rw [List.headD_cons]; exact List.mem_of_getLast? hlast
        · refine ⟨t0.dropLast :: t, b, ?_, ⟨hdl, ?_, ?_, htab⟩, ?_, ?_, ?_⟩
          · rw [invInsTab_cons_zero, hlast]; simp [hdl]
          · exact List.IsChain.sublist hrow (List.dropLast_sublist t0)
          · refine dominate_of_getElem (by omega) ?_
            intro k hk
            rw [List.getElem_dropLast]
            exact hdom.getElem_lt k hk
          · rw [insTab_cons_of_bumped_none hbne, insRow_eq_append_of_bumped_none hbne, ht0]
          · exact bumpRow_cons_of_bumped_none hbne
          · rw [List.headD_cons]; exact List.mem_of_getLast? hlast
    | succ j =>
      have hcj : IsRemCorner (shape t) j := by
        rw [IsRemCorner] at hc ⊢
        simpa using hc
      obtain ⟨t'', b, hinv, htab'', hins, hbump, hmemb⟩ := ih htab hcj
      have hex : ∃ y ∈ t0, y < b := by
        obtain ⟨k, hk, hbk⟩ := List.getElem_of_mem hmemb
        refine ⟨t0[k]'(lt_of_lt_of_le hk hdom.length_le), List.getElem_mem _, ?_⟩
        rw [← hbk]
        exact hdom.getElem_lt k hk
      have hinvrow : invInsRow t0 b ≠ none := by
        intro hnone
        obtain ⟨y, hy, hlt⟩ := hex
        exact absurd (le_of_invInsRow_eq_none hnone y hy) (not_le.2 hlt)
      obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 hinvrow
      obtain ⟨r, l⟩ := p
      obtain ⟨hrrow, hrins, hrbump, hrmem, hrlt⟩ := insRow_invInsRow hrow hp
      refine ⟨r :: t'', l, ?_, ⟨?_, hrrow, ?_, htab''⟩, ?_, ?_, ?_⟩
      · rw [invInsTab_cons_succ, hinv]
        dsimp only
        rw [hp]
      · intro hr0
        rw [hr0] at hrbump
        simp [bumped] at hrbump
      · have hu : IsRow (t''.headD []) := by
          cases t'' with
          | nil => simp
          | cons u t3 => simpa using htab''.isRow_getD 0
        refine dominate_of_dominate_insRow hu hrrow hrbump ?_
        rw [hrins, ← headD_insTab, hins]
        exact hdom
      · rw [insTab_cons_of_bumped_some hrbump, hrins, hins]
      · rw [bumpRow_cons_of_bumped_some hrbump, hbump]
      · rw [List.headD_cons]
        exact hrmem

end Young
