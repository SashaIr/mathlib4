/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Greene.ColumnTheorem
public import Mathlib.Combinatorics.Young.Greene.Theorem

/-!
# Reversing a word with distinct letters

Reversing a word exchanges its nondecreasing and its strictly decreasing subsequences, as
soon as its letters are distinct: a nondecreasing subsequence of the reversed word is a
strictly decreasing subsequence of the word, and conversely.  Consequently the Greene row
invariants of the reversed word are the Greene column invariants of the word (Coq
`Greene_rel_rev` and `Greene_rel_uniq` of `theories/LRrule/Greene_inv.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi)), and, by the two Greene theorems, the
shape of the insertion tableau of the reversed word is the conjugate of the shape of the
insertion tableau of the word.

## Main definitions

* `List.revCol n c` : the colouring `c` of a word of length `n`, read backwards.

## Main results

* `List.greeneRow_reverse_of_nodup` : `greeneRow w.reverse k = greeneCol w k` for a word `w`
  with distinct letters.
* `List.shape_RS_reverse_of_nodup` : the shape of the insertion tableau of `w.reverse` is
  the conjugate of the shape of the insertion tableau of `w`.
-/

@[expose] public section

namespace List

variable {T : Type*} [LinearOrder T]

/-! ### Reversing a colouring -/

/-- The colouring of a word of length `n` obtained by reading the colouring `c` backwards. -/
def revCol (n : ℕ) (c : ℕ → Option ℕ) : ℕ → Option ℕ := fun i => c (n - 1 - i)

omit [LinearOrder T] in
@[simp] lemma greeneSize_reverse (w : List T) (c : ℕ → Option ℕ) :
    greeneSize w.reverse c = greeneSize w c := by
  simp [greeneSize]

omit [LinearOrder T] in
lemma greeneSize_revCol (w : List T) (c : ℕ → Option ℕ) :
    greeneSize w (revCol w.length c) = greeneSize w c := by
  rw [greeneSize, greeneSize]
  refine Finset.card_bij' (fun i _ => w.length - 1 - i) (fun i _ => w.length - 1 - i)
    ?_ ?_ ?_ ?_ <;> intro i hi
  · rcases Finset.mem_filter.1 hi with ⟨hi_range, hi_color⟩
    have hi_range := Finset.mem_range.1 hi_range
    have hn : 0 < w.length := by omega
    have hpred : w.length - 1 < w.length := Nat.sub_lt hn (by omega)
    apply Finset.mem_filter.2
    exact ⟨Finset.mem_range.2 (lt_of_le_of_lt (Nat.sub_le _ _) hpred), hi_color⟩
  · rcases Finset.mem_filter.1 hi with ⟨hi_range, hi_color⟩
    have hi_range := Finset.mem_range.1 hi_range
    have hn : 0 < w.length := by omega
    have hpred : w.length - 1 < w.length := Nat.sub_lt hn (by omega)
    apply Finset.mem_filter.2
    exact ⟨Finset.mem_range.2 (lt_of_le_of_lt (Nat.sub_le _ _) hpred),
      by simp only [revCol]
         rw [show w.length - 1 - (w.length - 1 - i) = i by omega]
         exact hi_color⟩
  · have hi_range := Finset.mem_range.1 (Finset.mem_filter.1 hi).1
    simp only [revCol] at hi ⊢
    omega
  · have hi_range := Finset.mem_range.1 (Finset.mem_filter.1 hi).1
    omega

/-! ### Exchanging nondecreasing and strictly decreasing colourings -/

/-- A strictly decreasing colouring of `w` is a nondecreasing colouring of `w.reverse`. -/
lemma IsGreeneDecCol.isGreeneCol_reverse {w : List T} {k : ℕ} {c : ℕ → Option ℕ}
    (h : IsGreeneDecCol w k c) : IsGreeneCol w.reverse k (revCol w.length c) := by
  refine ⟨fun i x hx => h.1 _ x hx, fun i j x hij hj hi hjc => ?_⟩
  have hjw : j < w.length := by simpa using hj
  rw [List.getElem_reverse, List.getElem_reverse]
  exact le_of_lt (h.2 (w.length - 1 - j) (w.length - 1 - i) x (by omega) (by omega) hjc hi)

/-- A nondecreasing colouring of `w.reverse` is a strictly decreasing colouring of `w`, as
soon as the letters of `w` are distinct. -/
lemma IsGreeneCol.isGreeneDecCol_reverse {w : List T} {k : ℕ} {c : ℕ → Option ℕ}
    (hnd : w.Nodup) (h : IsGreeneCol w.reverse k c) : IsGreeneDecCol w k (revCol w.length c) := by
  refine ⟨fun i x hx => h.1 _ x hx, fun i j x hij hj hi hjc => ?_⟩
  have hlen : w.length - 1 - i < w.reverse.length := by simp; omega
  have hle := h.2 (w.length - 1 - j) (w.length - 1 - i) x (by omega) hlen hjc hi
  have e1 : w.length - 1 - (w.length - 1 - j) = j := by omega
  have e2 : w.length - 1 - (w.length - 1 - i) = i := by omega
  simp only [List.getElem_reverse, e1, e2] at hle
  refine lt_of_le_of_ne hle fun heq => ?_
  exact absurd (hnd.getElem_inj_iff.1 heq) (by omega)

/-! ### The Greene invariants of a reversed word -/

/-- **The Greene row invariants of the reversed word are the Greene column invariants of the
word**, for a word with distinct letters. -/
theorem greeneRow_reverse_of_nodup {w : List T} (hnd : w.Nodup) (k : ℕ) :
    greeneRow w.reverse k = greeneCol w k := by
  refine le_antisymm (greeneRow_le fun c hc => ?_) (greeneCol_le fun c hc => ?_)
  · have h := le_greeneCol (hc.isGreeneDecCol_reverse hnd)
    rwa [greeneSize_revCol, ← greeneSize_reverse w c] at h
  · have h := le_greeneRow hc.isGreeneCol_reverse
    rwa [greeneSize_reverse, greeneSize_revCol] at h

/-- **The shape of the insertion tableau of a reversed word with distinct letters is the
conjugate shape.** -/
theorem shape_RS_reverse_of_nodup {w : List T} (hnd : w.Nodup) :
    shape (RS w.reverse) = conjPart (shape (RS w)) := by
  refine sum_take_inj (isPart_shape (isTableau_RS _))
    (isPart_conjPart (isPart_shape (isTableau_RS _))) fun k => ?_
  rw [← greeneRow_eq_sum_take_shape, ← greeneCol_eq_sum_take_conjPart,
    greeneRow_reverse_of_nodup hnd]

end List
