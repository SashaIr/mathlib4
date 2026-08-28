/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Tableau.Kostka
import Mathlib.Combinatorics.Young.Crystal.Plactic
import Mathlib.Combinatorics.Young.Crystal.Tableau
import Mathlib.Combinatorics.Young.Plactic.Monoid

/-!
# The crystal operators, tableaux and the Robinson–Schensted correspondence

The crystal operators preserve the set of reading words of tableaux of a given shape
(`List.exists_isTableau_crystalE`), and they commute with the Robinson–Schensted
insertion (`List.exists_RS_crystalE`), because they are compatible with the plactic
congruence.  Moreover a tableau on which no raising operator acts is the superstandard
tableau of its shape (`List.eq_superTab_of_crystalPhi_eq_zero`), so that every tableau
can be raised to the superstandard tableau of its shape
(`List.reflTransGen_tabRaise_superTab`).

These are the two ingredients of the crystal proof of the Littlewood–Richardson rule: the
crystal graph on tableaux of a fixed shape is connected, with the superstandard tableau as
its highest weight element.

## Main definitions

* `List.TabRaise` : one step of the crystal raising action on tableaux.

## Main results

* `List.exists_isTableau_crystalE`, `List.exists_isTableau_crystalF` : the crystal
  operators preserve reading words of tableaux of a given shape.
* `List.exists_RS_crystalE` : the crystal operators commute with `List.RS`.
* `List.eq_superTab_of_crystalPhi_eq_zero` : a highest weight tableau is superstandard.
* `List.reflTransGen_tabRaise_superTab` : every tableau is connected to the superstandard
  tableau of its shape by raising operators.
-/

namespace List

open List

/-! ### Letters of the reading word of a tableau -/

lemma mem_toWord {T : Type*} {t : List (List T)} {x : T} : x ∈ toWord t ↔ ∃ r ∈ t, x ∈ r := by
  rw [toWord, List.mem_flatten]
  constructor
  · rintro ⟨r, hr, hx⟩; exact ⟨r, (List.mem_reverse).1 hr, hx⟩
  · rintro ⟨r, hr, hx⟩; exact ⟨r, (List.mem_reverse).2 hr, hx⟩

/-- A lower bound on the top row of a tableau is a lower bound on all its letters. -/
lemma le_of_mem_toWord {t : List (List ℕ)} (ht : IsTableau t) {k : ℕ}
    (h0 : ∀ x ∈ t.headD [], k ≤ x) {x : ℕ} (hx : x ∈ toWord t) : k ≤ x := by
  induction t generalizing k with
  | nil => simp at hx
  | cons r0 t ih =>
    obtain ⟨-, -, hdom, ht'⟩ := ht
    rw [toWord_cons, List.mem_append] at hx
    simp only [List.headD_cons] at h0
    rcases hx with hx | hx
    · refine ih ht' (fun y hy => ?_) hx
      obtain ⟨c, hc, rfl⟩ := List.mem_iff_getElem.1 hy
      have hlt := hdom.getElem_lt c hc
      have := h0 _ (List.getElem_mem (lt_of_lt_of_le hc hdom.length_le))
      omega
    · exact h0 x hx

/-! ### Highest weight tableaux -/

/-- A tableau whose letters are at least `k` and whose reading word has no unmatched
letter `i + 1` for `i ≥ k` is the superstandard tableau with labels starting at `k`. -/
theorem eq_superTabFrom_of_crystalPhi_eq_zero {k : ℕ} {t : List (List ℕ)} (ht : IsTableau t)
    (hmem : ∀ x ∈ toWord t, k ≤ x) (h : ∀ i, k ≤ i → crystalPhi i (toWord t) = 0) :
    t = superTabFrom k (shape t) := by
  induction t generalizing k with
  | nil => simp
  | cons r0 t ih =>
    obtain ⟨hne, hrow0, hdom, ht'⟩ := ht
    have hword : toWord (r0 :: t) = toWord t ++ r0 := toWord_cons r0 t
    have hsplit : ∀ i, k ≤ i →
        crystalPhi i r0 = 0 ∧ crystalPhi i (toWord t) ≤ crystalEps i r0 := by
      intro i hi
      have := h i hi
      rw [hword, crystalPhi_append] at this
      omega
    have hr0 : r0 = List.replicate r0.length k := by
      refine List.eq_replicate_iff.2 ⟨rfl, fun x hx => ?_⟩
      have h1 : k ≤ x := hmem x (by rw [hword]; exact List.mem_append_right _ hx)
      by_contra hne'
      have hx1 : x = (x - 1) + 1 := by omega
      have h2 : crystalPhi (x - 1) r0 = 0 := (hsplit (x - 1) (by omega)).1
      rw [hrow0.crystalPhi_eq_count] at h2
      have : 0 < r0.count x := List.count_pos_iff.2 hx
      rw [← hx1] at h2
      omega
    have hall : ∀ y ∈ r0, y = k := fun y hy => List.eq_of_mem_replicate (hr0 ▸ hy)
    have hcount : ∀ i, k + 1 ≤ i → r0.count i = 0 := by
      intro i hi
      refine List.count_eq_zero.2 (fun hmemi => ?_)
      have := hall i hmemi
      omega
    have hmem' : ∀ x ∈ toWord t, k + 1 ≤ x := by
      refine fun x hx => le_of_mem_toWord ht' (fun y hy => ?_) hx
      obtain ⟨c, hc, rfl⟩ := List.mem_iff_getElem.1 hy
      have hlt := hdom.getElem_lt c hc
      have := hall _ (List.getElem_mem (lt_of_lt_of_le hc hdom.length_le))
      omega
    have hphi' : ∀ i, k + 1 ≤ i → crystalPhi i (toWord t) = 0 := by
      intro i hi
      have h2 := (hsplit i (by omega)).2
      rw [hrow0.crystalEps_eq_count, hcount i hi] at h2
      omega
    rw [shape_cons, superTabFrom_cons, ← hr0]
    congr 1
    exact ih ht' hmem' hphi'

/-- A tableau whose reading word has no unmatched letter is the superstandard tableau of
its shape: it is the highest weight element of its crystal. -/
theorem eq_superTab_of_crystalPhi_eq_zero {t : List (List ℕ)} (ht : IsTableau t)
    (h : ∀ i, crystalPhi i (toWord t) = 0) : t = superTab (shape t) :=
  eq_superTabFrom_of_crystalPhi_eq_zero ht (fun _ _ => Nat.zero_le _) (fun i _ => h i)

/-! ### The crystal operators on tableaux -/

lemma sum_set_add_getElem (l : List ℕ) {j : ℕ} (h : j < l.length) (a : ℕ) :
    (l.set j a).sum + l[j] = l.sum + a := by
  induction l generalizing j with
  | nil => simp at h
  | cons x l ih =>
    cases j with
    | zero => simp; omega
    | succ m =>
      have := ih (j := m) (by simpa using h)
      simp only [List.set_cons_succ, List.sum_cons, List.getElem_cons_succ]
      omega

/-- The raising operator decreases the sum of the letters by one. -/
lemma sum_crystalE {i : ℕ} {w w' : List ℕ} (h : crystalE i w = some w') : w'.sum + 1 = w.sum := by
  obtain ⟨j, hj, hval, rfl⟩ := crystalE_eq_set h
  have hs := sum_set_add_getElem w hj i
  rw [hval] at hs
  omega

/-- The raising operator sends the reading word of a tableau to the reading word of a
tableau of the same shape. -/
theorem exists_isTableau_crystalE {i : ℕ} {t : List (List ℕ)} (ht : IsTableau t) {w : List ℕ}
    (hw : crystalE i (toWord t) = some w) :
    ∃ t', toWord t' = w ∧ IsTableau t' ∧ shape t' = shape t := by
  obtain ⟨t', hword, hskew, hshape, -⟩ :=
    exists_isSkewTableau_crystalE (isSkewTableau_nil_iff_isTableau.2 ht) hw
  exact ⟨t', hword, isSkewTableau_nil_iff_isTableau.1 hskew, hshape⟩

/-- The lowering operator sends the reading word of a tableau to the reading word of a
tableau of the same shape. -/
theorem exists_isTableau_crystalF {i : ℕ} {t : List (List ℕ)} (ht : IsTableau t) {w : List ℕ}
    (hw : crystalF i (toWord t) = some w) :
    ∃ t', toWord t' = w ∧ IsTableau t' ∧ shape t' = shape t := by
  obtain ⟨t', hword, hskew, hshape, -⟩ :=
    exists_isSkewTableau_crystalF (isSkewTableau_nil_iff_isTableau.2 ht) hw
  exact ⟨t', hword, isSkewTableau_nil_iff_isTableau.1 hskew, hshape⟩

/-- The insertion tableau intertwines the crystal operators on words with the crystal
operators on tableaux. -/
theorem exists_RS_crystalE {i : ℕ} {w w' : List ℕ} (h : crystalE i w = some w') :
    ∃ V', IsTableau V' ∧ shape V' = shape (RS w) ∧ RS w' = V' ∧
      crystalE i (toWord (RS w)) = some (toWord V') := by
  obtain ⟨v', hv', hpl⟩ := crystalE_of_placticEquiv i (plactic_toWord_RS w).symm h
  obtain ⟨V', hword, hV', hshape⟩ := exists_isTableau_crystalE (isTableau_RS w) hv'
  refine ⟨V', hV', hshape, ?_, by rw [hword, hv']⟩
  rw [RS_eq_of_placticEquiv hpl, ← hword, RS_toWord hV']

/-! ### Connectedness of the crystal of tableaux of a given shape -/

/-- One step of the crystal raising action on tableaux. -/
def TabRaise (a b : List (List ℕ)) : Prop :=
  IsTableau a ∧ IsTableau b ∧ ∃ i, crystalE i (toWord a) = some (toWord b)

/-- Every tableau is connected to the superstandard tableau of its shape by a sequence of
raising operators. -/
theorem reflTransGen_tabRaise_superTab : ∀ n (t : List (List ℕ)), IsTableau t →
    (toWord t).sum = n → Relation.ReflTransGen TabRaise t (superTab (shape t)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t ht hsum
    by_cases hzero : ∀ i, crystalPhi i (toWord t) = 0
    · rw [← eq_superTab_of_crystalPhi_eq_zero ht hzero]
    · push_neg at hzero
      obtain ⟨i, hi⟩ := hzero
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((crystalE_isSome_iff i (toWord t)).2 hi)
      obtain ⟨t', hword, ht', hshape⟩ := exists_isTableau_crystalE ht hw
      have hlt : (toWord t').sum < n := by
        rw [hword]; have := sum_crystalE hw; omega
      have hrec := ih _ hlt t' ht' rfl
      rw [hshape] at hrec
      exact Relation.ReflTransGen.head ⟨ht, ht', i, by rw [hword]; exact hw⟩ hrec

/-! ### The lowering operator and the plactic congruence -/

/-- Knuth equivalent words have Knuth equivalent images under the lowering operator. -/
theorem crystalF_of_placticEquiv (i : ℕ) {u v u' : List ℕ} (h : PlacticEquiv u v)
    (hu : crystalF i u = some u') : ∃ v', crystalF i v = some v' ∧ PlacticEquiv u' v' := by
  have heps : crystalEps i u = crystalEps i v := crystalEps_of_placticEquiv i h
  have hne : crystalF i v ≠ none := by
    intro hcon
    have h0 : crystalEps i u = 0 := by rw [heps]; exact (crystalF_eq_none_iff i v).1 hcon
    rw [(crystalF_eq_none_iff i u).2 h0] at hu
    simp at hu
  obtain ⟨v', hv'⟩ := Option.ne_none_iff_exists'.1 hne
  refine ⟨v', hv', ?_⟩
  obtain ⟨V1, -, -, hRSu, hcu⟩ := exists_RS_crystalE (crystalE_crystalF hu)
  obtain ⟨V2, -, -, hRSv, hcv⟩ := exists_RS_crystalE (crystalE_crystalF hv')
  rw [← hRSu] at hcu
  rw [← hRSv] at hcv
  rw [placticEquiv_iff_RS_eq] at h ⊢
  rw [h] at hcu
  have hinj := crystalE_injective i hcu hcv
  rw [← RS_toWord_RS u', ← RS_toWord_RS v', hinj]

/-- The insertion tableau intertwines the lowering operators on words and on tableaux. -/
theorem exists_RS_crystalF {i : ℕ} {w w' : List ℕ} (h : crystalF i w = some w') :
    ∃ V', IsTableau V' ∧ shape V' = shape (RS w) ∧ RS w' = V' ∧
      crystalF i (toWord (RS w)) = some (toWord V') := by
  obtain ⟨v', hv', hpl⟩ := crystalF_of_placticEquiv i (plactic_toWord_RS w).symm h
  obtain ⟨V', hword, hV', hshape⟩ := exists_isTableau_crystalF (isTableau_RS w) hv'
  refine ⟨V', hV', hshape, ?_, by rw [hword, hv']⟩
  rw [RS_eq_of_placticEquiv hpl, ← hword, RS_toWord hV']

/-! ### Superstandard tableaux are of highest weight -/

lemma crystalPhi_le_count (i : ℕ) (w : List ℕ) : crystalPhi i w ≤ w.count (i + 1) := by
  induction w with
  | nil => simp
  | cons x w ih =>
    rcases eq_or_ne x (i + 1) with rfl | hne
    · rw [crystalPhi_cons_succ, List.count_cons_self]
      split <;> omega
    · rw [crystalPhi_cons_of_ne hne, List.count_cons_of_ne hne]
      exact ih

lemma crystalPhi_toWord_superTabFrom {lam : List ℕ} (h : IsPart lam) (k : ℕ) :
    ∀ i, k ≤ i → crystalPhi i (toWord (superTabFrom k lam)) = 0 := by
  induction lam generalizing k with
  | nil => simp
  | cons n lam ih =>
    intro i hi
    have hpart : IsPart lam := h.2
    have hle : lam.getD 0 0 ≤ n := by
      cases lam with
      | nil => simp
      | cons a l => simpa using h.1
    rw [superTabFrom_cons, toWord_cons, crystalPhi_append]
    have hrow : IsRow (List.replicate n k) := isRow_replicate n k
    have hphi : crystalPhi i (List.replicate n k) = 0 := by
      rw [hrow.crystalPhi_eq_count, List.count_replicate]
      simp only [beq_iff_eq]
      split <;> omega
    rw [hphi]
    rcases eq_or_lt_of_le hi with rfl | hlt
    · have heps : crystalEps k (List.replicate n k) = n := by
        rw [hrow.crystalEps_eq_count, List.count_replicate]
        simp
      have hcount := crystalPhi_le_count k (toWord (superTabFrom (k + 1) lam))
      rw [count_toWord_superTabFrom, if_pos (show k + 1 ≤ k + 1 by omega), Nat.sub_self] at hcount
      rw [heps]
      omega
    · rw [ih hpart (k + 1) i (by omega)]
      omega

/-- The reading word of a superstandard tableau has no unmatched letter: it is the highest
weight element of its crystal. -/
lemma crystalPhi_toWord_superTab {lam : List ℕ} (h : IsPart lam) (i : ℕ) :
    crystalPhi i (toWord (superTab lam)) = 0 :=
  crystalPhi_toWord_superTabFrom h 0 i (Nat.zero_le _)

end List
