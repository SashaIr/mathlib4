/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Word.Standardization

/-!
# Words with the same relative order have the same standardization

The standardization of a word only depends on the relative order of its letters, that is on
the truth of `w[i] ≤ w[j]` for `i < j` (Coq `eq_inv` and `eq_inv_std` in
`theories/Combi/std.v` of [Coq-Combi](https://github.com/math-comp/Coq-Combi)).

## Main results

* `List.std_eq_std_of_le_iff` : two words of the same length whose letters compare in the
  same way have the same standardization.
* `List.std_take_std` : standardizing a prefix of a standardized word is the same as
  standardizing the corresponding prefix of the original word.
-/

namespace List

variable {T T' : Type*} [LinearOrder T] [LinearOrder T']

/-- For two positions in increasing order, the standardization order is the weak order of
the letters. -/
private lemma stdLt_iff_le {w : List T} {i j : Fin w.length} (hij : (i : ℕ) < (j : ℕ)) :
    stdLt w i j ↔ w[(i : ℕ)] ≤ w[(j : ℕ)] := by
  simp only [stdLt, hij, and_true]
  exact le_iff_lt_or_eq.symm

/-- For two positions in decreasing order, the standardization order is the strict order of
the letters. -/
private lemma stdLt_iff_not_le {w : List T} {i j : Fin w.length} (hij : (j : ℕ) < (i : ℕ)) :
    stdLt w i j ↔ ¬ (w[(j : ℕ)] ≤ w[(i : ℕ)]) := by
  have hne : ¬ ((i : ℕ) < (j : ℕ)) := by omega
  simp only [stdLt, hne, and_false, or_false, not_le]

/-- Two words of the same length whose letters compare in the same way have the same
standardization. -/
theorem std_eq_std_of_le_iff {w : List T} {w' : List T'} (hlen : w.length = w'.length)
    (h : ∀ (i j : ℕ) (hi : i < w.length) (hj : j < w.length), i < j →
      (w[i] ≤ w[j] ↔ w'[i]'(by omega) ≤ w'[j]'(by omega))) :
    std w = std w' := by
  have hstdLt : ∀ i j : Fin w.length,
      stdLt w i j ↔ stdLt w' (Fin.cast hlen i) (Fin.cast hlen j) := by
    intro i j
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with hij | hij | hij
    · have hij' : ((Fin.cast hlen i : Fin w'.length) : ℕ)
          < ((Fin.cast hlen j : Fin w'.length) : ℕ) := by simpa using hij
      rw [stdLt_iff_le hij, stdLt_iff_le hij']
      exact h i j i.isLt j.isLt hij
    · have : i = j := Fin.ext hij
      subst this
      exact iff_of_false (stdLt_irrefl w i) (stdLt_irrefl w' _)
    · have hij' : ((Fin.cast hlen j : Fin w'.length) : ℕ)
          < ((Fin.cast hlen i : Fin w'.length) : ℕ) := by simpa using hij
      rw [stdLt_iff_not_le hij, stdLt_iff_not_le hij']
      exact not_congr (h j i j.isLt i.isLt hij)
  have hrank : ∀ i : Fin w.length, stdRank w i = stdRank w' (Fin.cast hlen i) := by
    intro i
    refine Finset.card_bij (fun a _ => Fin.cast hlen a) ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact (hstdLt a i).1 ha
    · intro a _ b _ hab
      simpa [Fin.ext_iff] using hab
    · intro b hb
      refine ⟨Fin.cast hlen.symm b, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact (hstdLt (Fin.cast hlen.symm b) i).2 (by simpa using hb)
  refine List.ext_getElem (by simp [hlen]) fun i h1 h2 => ?_
  have hi : i < w.length := by simpa using h1
  rw [getElem_std, getElem_std]
  exact hrank ⟨i, hi⟩

/-- Standardizing a prefix of a standardized word is the same as standardizing the
corresponding prefix of the original word. -/
theorem std_take_std (w : List T) (k : ℕ) : std ((std w).take k) = std (w.take k) := by
  have hlen : ((std w).take k).length = (w.take k).length := by simp
  refine std_eq_std_of_le_iff hlen fun i j hi hj hij => ?_
  have hi' : i < min k w.length := by simpa using hi
  have hj' : j < min k w.length := by simpa using hj
  rw [List.getElem_take, List.getElem_take, List.getElem_take, List.getElem_take]
  exact getElem_std_le_iff (by omega) (by omega) hij

end List
