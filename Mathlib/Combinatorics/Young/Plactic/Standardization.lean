/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Tableau.Standardize

/-!
# Standardization and the plactic monoid

A Lean 4 port of `theories/LRrule/stdplact.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

The standardization of a word is compatible with Knuth (plactic) equivalence: if two words
are Knuth equivalent, so are their standardizations.  As a consequence, the insertion
tableau of the standardization of a word has the same shape as the insertion tableau of
the word.

## Main results

* `List.eq_of_isStd_of_lt_iff` : a standard word is determined by the relative order of
  its letters.
* `List.std_swap_eq` : standardizing commutes with exchanging two adjacent distinct
  letters.
* `List.std_placticStep`, `List.std_placticEquiv` : standardization preserves Knuth
  equivalence (Coq `std_plact`).
* `List.shape_RS_std` : `shape (RS (std w)) = shape (RS w)` (Coq `shape_RS_std`).
-/

namespace List

open List

/-! ### A standard word is determined by the relative order of its letters -/

lemma isStd_of_nodup_of_lt {v : List ℕ} (hnd : v.Nodup) (hlt : ∀ x ∈ v, x < v.length) :
    IsStd v := by
  have hsub : v.Subperm (List.range v.length) :=
    List.subperm_of_subset hnd (fun x hx => by simpa using hlt x hx)
  exact hsub.perm_of_length_le (by simp)

/-- In a standard word, the letter at position `i` is the number of positions carrying a
smaller letter. -/
lemma getD_eq_card_filter_of_isStd {u : List ℕ} (hu : IsStd u) {i : ℕ} (hi : i < u.length) :
    u.getD i 0 = ((Finset.range u.length).filter (fun j => u.getD j 0 < u.getD i 0)).card := by
  have hlt : u.getD i 0 < u.length := hu.getD_lt hi
  have hcard : ((Finset.range u.length).filter (fun j => u.getD j 0 < u.getD i 0)).card
      = ((Finset.range u.length).filter (fun m => m < u.getD i 0)).card := by
    refine Finset.card_bij (fun j _ => u.getD j 0) ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨hu.getD_lt hj.1, hj.2⟩
    · intro j hj j' hj' hjj
      simp only [Finset.mem_filter, Finset.mem_range] at hj hj'
      rw [List.getD_eq_getElem _ _ hj.1, List.getD_eq_getElem _ _ hj'.1] at hjj
      exact (Nodup.getElem_inj_iff hu.nodup).mp hjj
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_range] at hm
      have hmem : m ∈ u := hu.mem_iff.2 (by simpa using hm.1)
      obtain ⟨j, hj, hju⟩ := List.mem_iff_getElem.1 hmem
      have hval : u.getD j 0 = m := by rw [List.getD_eq_getElem _ _ hj, hju]
      refine ⟨j, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range, hval]
        exact ⟨hj, hm.2⟩
      · exact hval
  rw [hcard]
  have : (Finset.range u.length).filter (fun m => m < u.getD i 0)
      = Finset.range (u.getD i 0) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, Finset.card_range]

/-- A standard word is determined by the relative order of its letters. -/
theorem eq_of_isStd_of_lt_iff {u v : List ℕ} (hu : IsStd u) (hv : IsStd v)
    (hlen : u.length = v.length)
    (h : ∀ i j, i < u.length → j < u.length →
      (u.getD i 0 < u.getD j 0 ↔ v.getD i 0 < v.getD j 0)) :
    u = v := by
  refine List.ext_getElem hlen ?_
  intro i h1 h2
  rw [← List.getD_eq_getElem _ 0 h1, ← List.getD_eq_getElem _ 0 h2,
    getD_eq_card_filter_of_isStd hu h1, getD_eq_card_filter_of_isStd hv h2, ← hlen]
  congr 1
  refine Finset.filter_congr ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  simpa using h j i hj h1

/-! ### Standardization and swapping two adjacent letters -/

variable {T : Type*} [LinearOrder T]

lemma getD_std_lt_getD_std_iff (w : List T) (d : T) {i j : ℕ} (hi : i < w.length)
    (hj : j < w.length) :
    (std w).getD i 0 < (std w).getD j 0 ↔
      (w.getD i d < w.getD j d ∨ (w.getD i d = w.getD j d ∧ i < j)) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hj),
    List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
  exact getElem_std_lt_getElem_std_iff w hi hj

/-- The transposition exchanging `k` and `k + 1`. -/
def swp (k i : ℕ) : ℕ := if i = k then k + 1 else if i = k + 1 then k else i

lemma swp_lt {k i n : ℕ} (hk : k + 1 < n) (hi : i < n) : swp k i < n := by
  unfold swp; split_ifs <;> omega

lemma swp_lt_swp_iff {k i j : ℕ} (h1 : i = k → j ≠ k + 1) (h2 : i = k + 1 → j ≠ k) :
    swp k i < swp k j ↔ i < j := by
  unfold swp; split_ifs <;> omega

variable {α : Type*}

/-- Exchanging two adjacent letters of a word amounts to composing with the transposition
`List.swp`. -/
lemma getD_swap_adj (p s : List α) (a b d : α) (i : ℕ) :
    (p ++ b :: a :: s).getD i d = (p ++ a :: b :: s).getD (swp p.length i) d := by
  rcases lt_trichotomy i p.length with h | h | h
  · rw [List.getD_append _ _ _ _ h]
    have : swp p.length i = i := by unfold swp; split_ifs <;> omega
    rw [this, List.getD_append _ _ _ _ h]
  · subst h
    have : swp p.length p.length = p.length + 1 := by unfold swp; simp
    rw [this, List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega)]
    simp
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
    · have hi : i = p.length + 1 := by omega
      subst hi
      have : swp p.length (p.length + 1) = p.length := by unfold swp; simp
      rw [this, List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega)]
      simp
    · have hs : swp p.length i = i := by unfold swp; split_ifs <;> omega
      rw [hs, List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega)]
      have : i - p.length = (i - p.length - 2) + 2 := by omega
      rw [this]
      simp

/-- Standardization commutes with the exchange of two adjacent distinct letters. -/
theorem std_swap_eq {p s : List T} {a b : T} (hab : a ≠ b) {P S : List ℕ} {A B : ℕ}
    (hU : std (p ++ a :: b :: s) = P ++ A :: B :: S) (hP : P.length = p.length) :
    std (p ++ b :: a :: s) = P ++ B :: A :: S := by
  set u : List T := p ++ a :: b :: s with hu
  set w : List T := p ++ b :: a :: s with hw
  have hlenu : u.length = p.length + 2 + s.length := by simp [hu]; omega
  have hlenw : w.length = p.length + 2 + s.length := by simp [hw]; omega
  have hlenS : S.length = s.length := by
    have := congrArg List.length hU
    simp only [length_std, hlenu, List.length_append, List.length_cons] at this
    omega
  have hstdU : IsStd (P ++ A :: B :: S) := hU ▸ std_isStd u
  have hVstd : IsStd (P ++ B :: A :: S) :=
    hstdU.of_perm (List.Perm.append_left P (List.Perm.swap _ _ _)).symm
  have hlenV : (P ++ B :: A :: S).length = w.length := by
    simp [hlenw, hP, hlenS]; omega
  refine (eq_of_isStd_of_lt_iff hVstd (std_isStd w) (by simp [hlenV]) ?_).symm ▸ rfl
  intro i j hi hj
  rw [hlenV] at hi hj
  -- rewrite both sides through the transposition
  have hVget : ∀ n, (P ++ B :: A :: S).getD n 0 = (std u).getD (swp p.length n) 0 := by
    intro n
    rw [hU, ← hP]
    exact getD_swap_adj P S A B 0 n
  have hwget : ∀ n, w.getD n a = u.getD (swp p.length n) a := getD_swap_adj p s a b a
  have hswplt : ∀ n, n < w.length → swp p.length n < u.length := by
    intro n hn
    exact swp_lt (by omega) (by omega)
  rw [hVget i, hVget j,
    getD_std_lt_getD_std_iff u a (hswplt i hi) (hswplt j hj),
    getD_std_lt_getD_std_iff w a hi hj, hwget i, hwget j]
  have hUa : u.getD p.length a = a := by
    rw [hu, List.getD_append_right _ _ _ _ (by omega)]
    simp
  have hUb : u.getD (p.length + 1) a = b := by
    rw [hu, List.getD_append_right _ _ _ _ (by omega)]
    simp
  have key : ∀ m n : ℕ, u.getD (swp p.length m) a = u.getD (swp p.length n) a →
      (swp p.length m < swp p.length n ↔ m < n) := by
    intro m n hmn
    refine swp_lt_swp_iff ?_ ?_
    · rintro rfl rfl
      refine absurd ?_ hab
      have h1 : swp p.length p.length = p.length + 1 := by unfold swp; simp
      have h2 : swp p.length (p.length + 1) = p.length := by unfold swp; simp
      rw [h1, h2, hUa, hUb] at hmn
      exact hmn.symm
    · rintro rfl h''
      refine absurd ?_ hab
      have h1 : swp p.length (p.length + 1) = p.length := by unfold swp; simp
      have h2 : swp p.length p.length = p.length + 1 := by unfold swp; simp
      rw [h'', h1, h2, hUa, hUb] at hmn
      exact hmn
  constructor
  · rintro (h | ⟨h, h'⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h, (key i j h).1 h'⟩
  · rintro (h | ⟨h, h'⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h, (key i j h).2 h'⟩

/-! ### Standardization preserves Knuth equivalence -/

lemma split_three_getElem {α : Type*} (L : List α) (k : ℕ) (h : k + 3 ≤ L.length) :
    L = L.take k ++ L[k]'(by omega) :: L[k+1]'(by omega) :: L[k+2]'(by omega) ::
      L.drop (k + 3) := by
  conv_lhs => rw [← List.take_append_drop k L]
  congr 1
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega)]

lemma split_three_getD {α : Type*} (L : List α) (k : ℕ) (d : α) (h : k + 3 ≤ L.length) :
    L = L.take k ++ L.getD k d :: L.getD (k+1) d :: L.getD (k+2) d :: L.drop (k + 3) := by
  rw [List.getD_eq_getElem _ _ (show k < L.length by omega),
    List.getD_eq_getElem _ _ (show k + 1 < L.length by omega),
    List.getD_eq_getElem _ _ (show k + 2 < L.length by omega)]
  exact split_three_getElem L k h

/-- Coq `std_plact`: standardization preserves the elementary Knuth transformations. -/
theorem std_placticStep {u v : List T} (h : PlacticStep u v) :
    PlacticStep (std u) (std v) := by
  cases h with
  | @knuthAC x y z hxy hyz p s =>
    have hlen : (p ++ x :: z :: y :: s).length = p.length + 3 + s.length := by
      simp only [List.length_append, List.length_cons]; omega
    have h3 : p.length + 3 ≤ (std (p ++ x :: z :: y :: s)).length := by
      rw [length_std, hlen]; omega
    have hx : (p ++ x :: z :: y :: s).getD p.length x = x := by
      rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp
    have hz : (p ++ x :: z :: y :: s).getD (p.length + 1) x = z := by
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp
    have hy : (p ++ x :: z :: y :: s).getD (p.length + 2) x = y := by
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp
    have hXY : (std (p ++ x :: z :: y :: s)).getD p.length 0
        < (std (p ++ x :: z :: y :: s)).getD (p.length + 2) 0 := by
      rw [getD_std_lt_getD_std_iff _ x (by omega) (by omega), hx, hy]
      rcases eq_or_lt_of_le hxy with h' | h'
      · exact Or.inr ⟨h', by omega⟩
      · exact Or.inl h'
    have hYZ : (std (p ++ x :: z :: y :: s)).getD (p.length + 2) 0
        < (std (p ++ x :: z :: y :: s)).getD (p.length + 1) 0 := by
      rw [getD_std_lt_getD_std_iff _ x (by omega) (by omega), hy, hz]
      exact Or.inl hyz
    have hsplit := split_three_getD (std (p ++ x :: z :: y :: s)) p.length 0 h3
    have hPlen : ((std (p ++ x :: z :: y :: s)).take p.length).length = p.length := by
      simp only [List.length_take]; omega
    have hswap := std_swap_eq (ne_of_lt (lt_of_le_of_lt hxy hyz)) hsplit hPlen
    rw [hswap]
    conv_lhs => rw [hsplit]
    exact PlacticStep.knuthAC (le_of_lt hXY) hYZ _ _
  | @knuthCA x y z hxy hyz p s =>
    have hlen : (p ++ y :: x :: z :: s).length = p.length + 3 + s.length := by
      simp only [List.length_append, List.length_cons]; omega
    have h3 : p.length + 3 ≤ (std (p ++ y :: x :: z :: s)).length := by
      rw [length_std, hlen]; omega
    have hy : (p ++ y :: x :: z :: s).getD p.length x = y := by
      rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp
    have hx : (p ++ y :: x :: z :: s).getD (p.length + 1) x = x := by
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp
    have hz : (p ++ y :: x :: z :: s).getD (p.length + 2) x = z := by
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp
    have hXY : (std (p ++ y :: x :: z :: s)).getD (p.length + 1) 0
        < (std (p ++ y :: x :: z :: s)).getD p.length 0 := by
      rw [getD_std_lt_getD_std_iff _ x (by omega) (by omega), hx, hy]
      exact Or.inl hxy
    have hYZ : (std (p ++ y :: x :: z :: s)).getD p.length 0
        < (std (p ++ y :: x :: z :: s)).getD (p.length + 2) 0 := by
      rw [getD_std_lt_getD_std_iff _ x (by omega) (by omega), hy, hz]
      rcases eq_or_lt_of_le hyz with h' | h'
      · exact Or.inr ⟨h', by omega⟩
      · exact Or.inl h'
    have hsplit := split_three_getD (std (p ++ y :: x :: z :: s)) p.length 0 h3
    have hPlen : ((std (p ++ y :: x :: z :: s)).take p.length).length = p.length := by
      simp only [List.length_take]; omega
    have hU' : std ((p ++ [y]) ++ x :: z :: s)
        = ((std (p ++ y :: x :: z :: s)).take p.length ++
            [(std (p ++ y :: x :: z :: s)).getD p.length 0]) ++
          (std (p ++ y :: x :: z :: s)).getD (p.length + 1) 0 ::
          (std (p ++ y :: x :: z :: s)).getD (p.length + 2) 0 ::
          (std (p ++ y :: x :: z :: s)).drop (p.length + 3) := by
      rw [List.append_assoc, List.append_assoc]
      exact hsplit
    have hPlen' : ((std (p ++ y :: x :: z :: s)).take p.length ++
        [(std (p ++ y :: x :: z :: s)).getD p.length 0]).length = (p ++ [y]).length := by
      simp only [List.length_append, List.length_take, List.length_cons, List.length_nil]
      omega
    have hswap := std_swap_eq (ne_of_lt (lt_of_lt_of_le hxy hyz)) hU' hPlen'
    simp only [List.singleton_append, List.append_assoc] at hswap
    rw [hswap]
    conv_lhs => rw [hsplit]
    exact PlacticStep.knuthCA hXY (le_of_lt hYZ) _ _

/-- Coq `std_plact`: standardization preserves Knuth equivalence. -/
theorem std_placticEquiv {u v : List T} (h : PlacticEquiv u v) :
    PlacticEquiv (std u) (std v) := by
  induction h with
  | rel a b hab => exact (std_placticStep hab).plactic
  | refl a => exact PlacticEquiv.refl _
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

/-- Coq `shape_RS_std`: the insertion tableau of the standardization of a word has the
same shape as the insertion tableau of the word. -/
theorem shape_RS_std (w : List T) : shape (RS (std w)) = shape (RS w) := by
  have h1 : PlacticEquiv (std w) (std (toWord (RS w))) :=
    std_placticEquiv (plactic_toWord_RS w).symm
  have h2 : RS (std w) = RS (std (toWord (RS w))) :=
    placticEquiv_iff_RS_eq.1 h1
  rw [h2]
  exact shape_RS_std_toWord (isTableau_RS w)

end List
