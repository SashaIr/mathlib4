/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.RobinsonSchensted.InsertionTableau
public import Mathlib.Combinatorics.Young.Shape.Corners

/-!
# Reverse insertion and injectivity of the Robinson–Schensted map

A Lean 4 port of the reverse insertion part of `theories/LRrule/Schensted.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

Schensted insertion can be undone: knowing the tableau after insertion and the row in
which the new box appeared, one recovers both the previous tableau and the inserted
letter.  Recording the successive rows in which boxes appear therefore makes the
Robinson–Schensted map injective.

## Main definitions

* `Young.invInsRow r b` : reverse row insertion (Coq `invins`): the last entry of `r`
  smaller than `b` is replaced by `b` and returned.
* `Young.bumpRow t l` : the index of the row of `t` in which the insertion of `l` creates
  a new box (Coq `instabnrow`).
* `Young.invInsTab t i` : reverse insertion in a tableau (Coq `invinstabnrow`).
* `Young.RSmap w` : the insertion tableau of `w` together with the recording word of the
  rows in which the boxes appear (Coq `RSmap`).
* `Young.RSmapinv t rows` : the word reconstructed from such a pair (Coq `RSmapinv`).

## Main results

* `Young.invInsRow_insRow` : reverse row insertion undoes row insertion.
* `Young.invInsTab_insTab` : reverse insertion undoes insertion in a tableau
  (Coq `invinstabnrow_instabnrow`).
* `Young.RSmapinv_RSmap` : the word can be recovered from `Young.RSmap w`
  (Coq `RS_bij_1`).
* `Young.RSmap_injective` : the Robinson–Schensted map is injective.
-/

@[expose] public section

namespace Young

open List

variable {T : Type*} [LinearOrder T]

/-! ### Reverse row insertion -/

/-- Reverse row insertion: the last entry of `r` which is smaller than `b` is replaced by
`b`, and that entry is returned; `none` if there is no such entry (Coq `invins`). -/
def invInsRow : List T → T → Option (List T × T)
  | [], _ => none
  | x :: r, b =>
    match invInsRow r b with
    | some (r', l) => some (x :: r', l)
    | none => if x < b then some (b :: r, x) else none

@[simp] lemma invInsRow_nil (b : T) : invInsRow ([] : List T) b = none := rfl

lemma invInsRow_cons (x : T) (r : List T) (b : T) :
    invInsRow (x :: r) b =
      match invInsRow r b with
      | some (r', l) => some (x :: r', l)
      | none => if x < b then some (b :: r, x) else none := rfl

/-- If no entry of `r` is smaller than `b`, reverse insertion fails. -/
lemma invInsRow_eq_none {r : List T} {b : T} (h : ∀ y ∈ r, b ≤ y) : invInsRow r b = none := by
  induction r with
  | nil => rfl
  | cons x r ih =>
    rw [invInsRow_cons, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    simp only [ite_eq_right (not_lt.2 (h x (List.mem_cons_self)))]

/-- If nothing is bumped, insertion appends the letter at the end of the row. -/
lemma insRow_eq_append_of_bumped_none {r : List T} {l : T} (h : bumped r l = none) :
    insRow r l = r ++ [l] := by
  induction r with
  | nil => rfl
  | cons x r ih =>
    rw [bumped_cons] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hx
      rw [insRow_cons, ite_eq_right hx, ih h]
      rfl

/-- Coq `invinsE`: reverse row insertion undoes row insertion. -/
lemma invInsRow_insRow {r : List T} (hr : IsRow r) {l b : T} (hb : bumped r l = some b) :
    invInsRow (insRow r l) b = some (r, l) := by
  induction r with
  | nil => simp [bumped] at hb
  | cons x r ih =>
    rw [IsRow, List.isChain_iff_pairwise, List.pairwise_cons] at hr
    rw [bumped_cons] at hb
    split at hb
    · rename_i hx
      have hbx : b = x := (Option.some.inj hb).symm
      subst hbx
      rw [insRow_cons, ite_eq_left hx, invInsRow_cons,
        invInsRow_eq_none (fun y hy => hr.1 y hy), ite_eq_left hx]
    · rename_i hx
      have hrow : IsRow r := by
        rw [IsRow, List.isChain_iff_pairwise]
        exact hr.2
      rw [insRow_cons, ite_eq_right hx, invInsRow_cons, ih hrow hb]

/-! ### Reverse insertion in a tableau -/

/-- The index of the row of `t` in which the insertion of `l` creates a new box
(Coq `instabnrow`). -/
def bumpRow : List (List T) → T → ℕ
  | [], _ => 0
  | t0 :: t, l =>
    match bumped t0 l with
    | none => 0
    | some b => bumpRow t b + 1

@[simp] lemma bumpRow_nil (l : T) : bumpRow ([] : List (List T)) l = 0 := rfl

lemma bumpRow_cons_of_bumped_none {t0 : List T} {t : List (List T)} {l : T}
    (h : bumped t0 l = none) : bumpRow (t0 :: t) l = 0 := by
  rw [bumpRow, h]

lemma bumpRow_cons_of_bumped_some {t0 : List T} {t : List (List T)} {l b : T}
    (h : bumped t0 l = some b) : bumpRow (t0 :: t) l = bumpRow t b + 1 := by
  rw [bumpRow, h]

/-- Reverse insertion in a tableau: the last box of row `i` is removed and the reverse
row insertions are performed upwards (Coq `invinstabnrow`). -/
def invInsTab : List (List T) → ℕ → Option (List (List T) × T)
  | [], _ => none
  | t0 :: t, 0 =>
    match t0.getLast? with
    | none => none
    | some b => some (if t0.dropLast = [] then t else t0.dropLast :: t, b)
  | t0 :: t, (i + 1) =>
    match invInsTab t i with
    | none => none
    | some (t', b) =>
      match invInsRow t0 b with
      | none => none
      | some (r, l) => some (r :: t', l)

lemma invInsTab_cons_zero (t0 : List T) (t : List (List T)) :
    invInsTab (t0 :: t) 0 =
      match t0.getLast? with
      | none => none
      | some b => some (if t0.dropLast = [] then t else t0.dropLast :: t, b) := rfl

lemma invInsTab_cons_succ (t0 : List T) (t : List (List T)) (i : ℕ) :
    invInsTab (t0 :: t) (i + 1) =
      match invInsTab t i with
      | none => none
      | some (t', b) =>
        match invInsRow t0 b with
        | none => none
        | some (r, l) => some (r :: t', l) := rfl

/-- Coq `invinstabnrow_instabnrow`: reverse insertion undoes insertion in a tableau. -/
theorem invInsTab_insTab {t : List (List T)} (h : IsTableau t) (l : T) :
    invInsTab (insTab t l) (bumpRow t l) = some (t, l) := by
  induction t generalizing l with
  | nil => simp [insTab, bumpRow, invInsTab_cons_zero]
  | cons t0 t ih =>
    obtain ⟨hne, hrow, hdom, htab⟩ := h
    cases hb : bumped t0 l with
    | none =>
      rw [insTab_cons_of_bumped_none hb, bumpRow_cons_of_bumped_none hb,
        invInsTab_cons_zero, insRow_eq_append_of_bumped_none hb]
      simp [hne]
    | some b =>
      rw [insTab_cons_of_bumped_some hb, bumpRow_cons_of_bumped_some hb,
        invInsTab_cons_succ, ih htab b]
      dsimp only
      rw [invInsRow_insRow hrow hb]

/-! ### The Robinson–Schensted map and its inverse -/

/-- The insertion tableau of `w` together with the recording word of the rows in which
the successive boxes appear (Coq `RSmap`). -/
def RSmap (w : List T) : List (List T) × List ℕ :=
  w.foldl (fun p l => (insTab p.1 l, p.2 ++ [bumpRow p.1 l])) ([], [])

@[simp] lemma RSmap_nil : RSmap ([] : List T) = ([], []) := rfl

lemma RSmap_concat (w : List T) (l : T) :
    RSmap (w ++ [l]) = (insTab (RSmap w).1 l, (RSmap w).2 ++ [bumpRow (RSmap w).1 l]) := by
  simp [RSmap]

/-- The first component of `Young.RSmap` is the insertion tableau. -/
lemma RSmap_fst (w : List T) : (RSmap w).1 = RS w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w l ih => rw [RSmap_concat, RS_concat, ih]

/-- Reconstruction of a word from a tableau and a reversed recording word. -/
def RSmapinvAux : List (List T) → List ℕ → Option (List T)
  | _, [] => some []
  | t, i :: rows =>
    match invInsTab t i with
    | none => none
    | some (t', l) => (RSmapinvAux t' rows).map (fun w => w ++ [l])

/-- The word reconstructed from a tableau and a recording word (Coq `RSmapinv`). -/
def RSmapinv (t : List (List T)) (rows : List ℕ) : Option (List T) :=
  RSmapinvAux t rows.reverse

/-- Coq `RS_bij_1`: the word can be recovered from its image under `Young.RSmap`. -/
theorem RSmapinv_RSmap (w : List T) : RSmapinv (RSmap w).1 (RSmap w).2 = some w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w l ih =>
    rw [RSmap_concat]
    simp only [RSmapinv, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append] at ih ⊢
    rw [RSmapinvAux, RSmap_fst, invInsTab_insTab (isTableau_RS w) l]
    rw [RSmap_fst] at ih
    dsimp only
    rw [ih]
    rfl

/-- The Robinson–Schensted map, sending a word to its insertion tableau together with the
recording word of the rows, is injective. -/
theorem RSmap_injective : Function.Injective (RSmap : List T → List (List T) × List ℕ) := by
  intro w w' h
  have h1 := RSmapinv_RSmap w
  have h2 := RSmapinv_RSmap w'
  rw [h] at h1
  rw [h1] at h2
  exact Option.some.inj h2

/-! ### How the shape grows -/

lemma bumpRow_le_length (t : List (List T)) (l : T) : bumpRow t l ≤ t.length := by
  induction t generalizing l with
  | nil => simp
  | cons t0 t ih =>
    cases hb : bumped t0 l with
    | none => simp [bumpRow_cons_of_bumped_none hb]
    | some b =>
      rw [bumpRow_cons_of_bumped_some hb]
      simpa using ih b

/-- Coq `shape_instabnrow`: insertion adds one box at the end of row `bumpRow t l`. -/
lemma shape_insTab (t : List (List T)) (l : T) :
    shape (insTab t l) = incrNth (shape t) (bumpRow t l) := by
  induction t generalizing l with
  | nil => rfl
  | cons t0 t ih =>
    cases hb : bumped t0 l with
    | none =>
      rw [insTab_cons_of_bumped_none hb, bumpRow_cons_of_bumped_none hb, shape_cons, shape_cons,
        incrNth_cons_zero, insRow_length_of_bumped_none hb]
    | some b =>
      rw [insTab_cons_of_bumped_some hb, bumpRow_cons_of_bumped_some hb, shape_cons, shape_cons,
        incrNth_cons_succ, insRow_length_of_bumped hb, ih]

/-- A partition to which one box has been added at the end of row `i`, and which is still
a partition, has an addable corner at row `i`. -/
lemma isAddCorner_of_isPart_incrNth {sh : List ℕ} {i : ℕ} (h : IsPart sh)
    (h' : IsPart (incrNth sh i)) : IsAddCorner sh i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact Or.inl rfl
  refine Or.inr ?_
  by_contra hcon
  push Not at hcon
  have hanti : sh.getD i 0 ≤ sh.getD (i - 1) 0 := h.getD_antitone (by omega)
  have heq : sh.getD i 0 = sh.getD (i - 1) 0 := le_antisymm hanti hcon
  have h1 : (incrNth sh i).getD i 0 = sh.getD i 0 + 1 := by
    rw [getD_incrNth]; simp
  have h2 : (incrNth sh i).getD (i - 1) 0 = sh.getD (i - 1) 0 := by
    rw [getD_incrNth, ite_eq_right (by omega : ¬ i = i - 1)]
    omega
  have h3 : (incrNth sh i).getD i 0 ≤ (incrNth sh i).getD (i - 1) 0 :=
    h'.getD_antitone (by omega)
  omega

/-- The new box created by an insertion is added at an addable corner of the shape. -/
lemma isAddCorner_bumpRow {t : List (List T)} (h : IsTableau t) (l : T) :
    IsAddCorner (shape t) (bumpRow t l) := by
  refine isAddCorner_of_isPart_incrNth (isPart_shape h) ?_
  rw [← shape_insTab]
  exact isPart_shape (isTableau_insTab h l)

/-! ### Reverse row insertion is a two-sided inverse -/

/-- If reverse insertion fails, no entry of the row is smaller than the letter. -/
lemma le_of_invInsRow_eq_none {r : List T} {b : T} (h : invInsRow r b = none) :
    ∀ y ∈ r, b ≤ y := by
  induction r with
  | nil => simp
  | cons x r ih =>
    rw [invInsRow_cons] at h
    cases hr : invInsRow r b with
    | some p => rw [hr] at h; exact absurd h (by simp)
    | none =>
      rw [hr] at h
      simp only at h
      split at h
      · exact absurd h (by simp)
      · rename_i hx
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy'
        · exact not_lt.1 hx
        · exact ih hr y hy'

/-- The entries of the row produced by reverse insertion come from the original row, or
are the reinserted letter. -/
lemma mem_invInsRow {r : List T} {b : T} : ∀ {s : List T} {m y : T},
    invInsRow r b = some (s, m) → y ∈ s → y ∈ r ∨ y = b := by
  induction r with
  | nil => intro s m y h; simp at h
  | cons x r ih =>
    intro s m y h hy
    rw [invInsRow_cons] at h
    cases hrec : invInsRow r b with
    | some p =>
      obtain ⟨s₀, m₀⟩ := p
      rw [hrec] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hs, -⟩ := h
      subst hs
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact Or.inl List.mem_cons_self
      · rcases ih hrec hy' with h' | h'
        · exact Or.inl (List.mem_cons_of_mem _ h')
        · exact Or.inr h'
    | none =>
      rw [hrec] at h
      simp only at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hs, -⟩ := h
        subst hs
        rcases List.mem_cons.1 hy with rfl | hy'
        · exact Or.inr rfl
        · exact Or.inl (List.mem_cons_of_mem _ hy')
      · exact absurd h (by simp)

/-- Coq `invins_insE`: row insertion undoes reverse row insertion.  The recovered row is
again a row, re-inserting the recovered letter gives back the original row, and it bumps
out the letter one started with. -/
lemma insRow_invInsRow {r : List T} (hr : IsRow r) {b : T} : ∀ {r' : List T} {l : T},
    invInsRow r b = some (r', l) →
      IsRow r' ∧ insRow r' l = r ∧ bumped r' l = some b ∧ l ∈ r ∧ l < b := by
  induction r with
  | nil => intro r' l h; simp at h
  | cons x r ih =>
    intro r' l h
    have hrow : IsRow r := hr.of_cons
    have hx : ∀ y ∈ r, x ≤ y := by
      have hp := hr
      rw [IsRow, List.isChain_iff_pairwise, List.pairwise_cons] at hp
      exact hp.1
    rw [invInsRow_cons] at h
    cases hrec : invInsRow r b with
    | some p =>
      obtain ⟨s, m⟩ := p
      rw [hrec] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hs, hm⟩ := h
      subst hs
      subst hm
      obtain ⟨hsrow, hins, hbump, hmem, hlt⟩ := ih hrow hrec
      have hxm : x ≤ m := hx m hmem
      refine ⟨?_, ?_, ?_, List.mem_cons_of_mem _ hmem, hlt⟩
      · rw [IsRow, List.isChain_iff_pairwise, List.pairwise_cons]
        refine ⟨fun y hy => ?_, by rw [← List.isChain_iff_pairwise]; exact hsrow⟩
        rcases mem_invInsRow hrec hy with hy' | rfl
        · exact hx y hy'
        · exact le_trans hxm (le_of_lt hlt)
      · rw [insRow_cons, ite_eq_right (not_lt.2 hxm), hins]
      · rw [bumped_cons, ite_eq_right (not_lt.2 hxm), hbump]
    | none =>
      rw [hrec] at h
      simp only at h
      split at h
      · rename_i hxb
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hs, hm⟩ := h
        subst hs
        subst hm
        have hbr : ∀ y ∈ r, b ≤ y := le_of_invInsRow_eq_none hrec
        refine ⟨?_, ?_, ?_, List.mem_cons_self, hxb⟩
        · rw [IsRow, List.isChain_iff_pairwise, List.pairwise_cons]
          exact ⟨hbr, by rw [← List.isChain_iff_pairwise]; exact hrow⟩
        · rw [insRow_cons, ite_eq_left hxb]
        · rw [bumped_cons, ite_eq_left hxb]
      · exact absurd h (by simp)

end Young
