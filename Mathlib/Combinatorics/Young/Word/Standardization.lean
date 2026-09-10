/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.RobinsonSchensted.Insertion
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.GetD
public import Mathlib.Order.Bounds.Basic

/-!
# Standardization of a word

A Lean 4 port of the basic part of `theories/Combi/std.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

The *standardization* of a word `w` of length `n` over a linearly ordered alphabet is the
word `std w` over `{0, …, n-1}` obtained by replacing each letter by its rank, where
equal letters are ordered from left to right.  It is a standard word, that is, a
permutation of `0, …, n-1`, and it has the same pattern of relative order as `w`.

## Main definitions

* `Young.IsStd u` : the word `u` is standard, i.e. a permutation of `0, …, n-1`
  (Coq `is_std`).
* `Young.stdLt w i j` : position `i` comes before position `j` in the order used for
  standardization: either the letter at `i` is smaller, or the letters are equal and
  `i < j`.
* `Young.stdRank w i` : the rank of position `i` for this order.
* `Young.std w` : the standardized word (Coq `std`).

## Main results

* `Young.std_isStd` : `Young.std w` is a standard word (Coq `std_is_std`).
* `Young.getElem_std_lt_getElem_std_iff` : standardization preserves the relative order
  of the letters.
* `Young.length_schensted_std` : `w` and `Young.std w` have nondecreasing subsequences of
  the same lengths, so their Schensted rows have the same length.
-/

@[expose] public section

namespace Young

open List

variable {T : Type*} [LinearOrder T]

/-! ### Standard words -/

/-- A word is standard when it is a permutation of `0, …, n-1` (Coq `is_std`). -/
def IsStd (u : List ℕ) : Prop := u.Perm (List.range u.length)

instance decidableIsStd (u : List ℕ) : Decidable (IsStd u) :=
  inferInstanceAs (Decidable (u.Perm (List.range u.length)))

/-- A standard word has no repeated letter. -/
lemma IsStd.nodup {u : List ℕ} (hu : IsStd u) : u.Nodup := hu.nodup_iff.2 nodup_range

/-- The letters of a standard word are smaller than its length. -/
lemma IsStd.getD_lt {u : List ℕ} (hu : IsStd u) {i : ℕ} (hi : i < u.length) :
    u.getD i 0 < u.length := by
  have hmem : u.getD i 0 ∈ u := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  simpa using hu.mem_iff.1 hmem

/-! ### The standardization order on positions -/

/-- Position `i` precedes position `j` for the standardization order when the letter at
`i` is smaller than the letter at `j`, or both letters are equal and `i < j`. -/
def stdLt (w : List T) (i j : Fin w.length) : Prop :=
  w[(i : ℕ)] < w[(j : ℕ)] ∨ (w[(i : ℕ)] = w[(j : ℕ)] ∧ (i : ℕ) < (j : ℕ))

instance decidableStdLt (w : List T) (i j : Fin w.length) : Decidable (stdLt w i j) := by
  unfold stdLt
  infer_instance

lemma stdLt_irrefl (w : List T) (i : Fin w.length) : ¬ stdLt w i i := by
  rintro (h | ⟨-, h⟩) <;> exact absurd h (Std.not_gt_of_lt h)

lemma stdLt_trans {w : List T} {i j k : Fin w.length} (hij : stdLt w i j)
    (hjk : stdLt w j k) : stdLt w i k := by
  rcases hij with h1 | ⟨h1, h1'⟩ <;> rcases hjk with h2 | ⟨h2, h2'⟩
  · exact Or.inl (lt_trans h1 h2)
  · exact Or.inl (h2 ▸ h1)
  · exact Or.inl (h1 ▸ h2)
  · exact Or.inr ⟨h1.trans h2, Nat.lt_trans h1' h2'⟩

lemma stdLt_total {w : List T} {i j : Fin w.length} (hij : i ≠ j) :
    stdLt w i j ∨ stdLt w j i := by
  rcases lt_trichotomy w[(i : ℕ)] w[(j : ℕ)] with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases Nat.lt_trichotomy (i : ℕ) (j : ℕ) with h' | h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact absurd (Fin.ext h') hij
    · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
  · exact Or.inr (Or.inl h)

/-! ### The standardized word -/

/-- The rank of the position `i` of `w` for the standardization order. -/
def stdRank (w : List T) (i : Fin w.length) : ℕ :=
  (Finset.univ.filter (fun j => stdLt w j i)).card

/-- The standardization of the word `w` (Coq `std`). -/
def std (w : List T) : List ℕ := (List.finRange w.length).map (stdRank w)

@[simp] lemma length_std (w : List T) : (std w).length = w.length := by
  simp [std]

lemma getElem_std (w : List T) {i : ℕ} (hi : i < (std w).length) :
    (std w)[i] = stdRank w ⟨i, by simpa using hi⟩ := by
  simp [std]

lemma stdRank_lt_length (w : List T) (i : Fin w.length) : stdRank w i < w.length := by
  have hsub : (Finset.univ.filter (fun j => stdLt w j i))
      ⊂ (Finset.univ : Finset (Fin w.length)) := by
    refine Finset.ssubset_iff_of_subset (Finset.filter_subset _ _) |>.2 ⟨i, Finset.mem_univ i, ?_⟩
    simp [stdLt_irrefl w i]
  have := Finset.card_lt_card hsub
  simpa [stdRank] using this

lemma stdRank_lt_stdRank_of_stdLt {w : List T} {i j : Fin w.length} (h : stdLt w i j) :
    stdRank w i < stdRank w j := by
  refine Finset.card_lt_card ?_
  refine Finset.ssubset_iff_of_subset ?_ |>.2 ⟨i, ?_, ?_⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact stdLt_trans hk h
  · simp [h]
  · simp [stdLt_irrefl w i]

lemma stdRank_lt_stdRank_iff {w : List T} {i j : Fin w.length} :
    stdRank w i < stdRank w j ↔ stdLt w i j := by
  refine ⟨fun h => ?_, stdRank_lt_stdRank_of_stdLt⟩
  by_cases hij : i = j
  · subst hij; exact absurd h (lt_irrefl _)
  · rcases stdLt_total hij with h' | h'
    · exact h'
    · exact absurd (stdRank_lt_stdRank_of_stdLt h') (by omega)

lemma stdRank_injective (w : List T) : Function.Injective (stdRank w) := by
  intro i j hij
  by_contra hne
  rcases stdLt_total hne with h | h
  · exact absurd (stdRank_lt_stdRank_of_stdLt h) (by omega)
  · exact absurd (stdRank_lt_stdRank_of_stdLt h) (by omega)

/-- Coq `std_is_std`: the standardization of a word is a standard word. -/
theorem std_isStd (w : List T) : IsStd (std w) := by
  have hnodup : (std w).Nodup :=
    (List.nodup_finRange _).map (stdRank_injective w)
  have hsub : ∀ x ∈ std w, x ∈ List.range (std w).length := by
    intro x hx
    rw [std, List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    simpa using stdRank_lt_length w i
  have hsubperm : (std w).Subperm (List.range (std w).length) :=
    List.subperm_of_subset hnodup hsub
  exact hsubperm.perm_of_length_le (by simp)

/-- Standardization preserves the relative order of the letters. -/
theorem getElem_std_lt_getElem_std_iff (w : List T) {i j : ℕ} (hi : i < w.length)
    (hj : j < w.length) :
    (std w)[i]'(by simpa using hi) < (std w)[j]'(by simpa using hj) ↔
      (w[i] < w[j] ∨ (w[i] = w[j] ∧ i < j)) := by
  rw [getElem_std, getElem_std]
  exact stdRank_lt_stdRank_iff

/-- For two positions in increasing order, the letters of `w` are weakly increasing iff
those of `Young.std w` are. -/
lemma getElem_std_le_iff {w : List T} {i j : ℕ} (hi : i < w.length) (hj : j < w.length)
    (hij : i < j) :
    ((std w)[i]'(by simpa using hi) ≤ (std w)[j]'(by simpa using hj)) ↔ w[i] ≤ w[j] := by
  constructor
  · intro h
    rcases eq_or_lt_of_le h with heq | hlt
    · exfalso
      rw [getElem_std, getElem_std] at heq
      have hfin := stdRank_injective w heq
      have : i = j := congrArg Fin.val hfin
      omega
    · rcases (getElem_std_lt_getElem_std_iff w hi hj).1 hlt with h' | ⟨h', -⟩
      · exact le_of_lt h'
      · exact le_of_eq h'
  · intro h
    rcases eq_or_lt_of_le h with heq | hlt
    · exact le_of_lt ((getElem_std_lt_getElem_std_iff w hi hj).2 (Or.inr ⟨heq, hij⟩))
    · exact le_of_lt ((getElem_std_lt_getElem_std_iff w hi hj).2 (Or.inl hlt))

/-! ### Transfer of nondecreasing subsequences -/

/-- If two words of the same length have the same pattern of relative order, then a
nondecreasing subsequence of the first gives one of the same length of the second. -/
lemma exists_sublist_of_mono {α β : Type*} [LinearOrder α] [LinearOrder β] {w : List α}
    {v : List β} (hlen : w.length = v.length)
    (hmono : ∀ i j, (hi : i < w.length) → (hj : j < w.length) → i < j →
      w[i] ≤ w[j] → v[i]'(hlen ▸ hi) ≤ v[j]'(hlen ▸ hj))
    {s : List α} (hsub : s.Sublist w) (hs : s.Pairwise (· ≤ ·)) :
    ∃ t : List β, t.Sublist v ∧ t.Pairwise (· ≤ ·) ∧ t.length = s.length := by
  obtain ⟨is, rfl, hpair⟩ := List.sublist_eq_map_getElem hsub
  have hle : is.Pairwise (fun (a b : Fin w.length) => w[(a : ℕ)] ≤ w[(b : ℕ)]) := by
    rw [List.pairwise_map] at hs
    simpa [Fin.getElem_fin] using hs
  have key : is.Pairwise
      (fun (a b : Fin w.length) => v[(a : ℕ)]'(hlen ▸ a.isLt) ≤ v[(b : ℕ)]'(hlen ▸ b.isLt)) := by
    refine List.Pairwise.imp₂ ?_ hpair hle
    intro a b hab hwab
    exact hmono (a : ℕ) (b : ℕ) a.isLt b.isLt hab hwab
  have hpair' : (is.map (Fin.cast hlen)).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact hpair.imp (fun {a b} h => h)
  refine ⟨(is.map (Fin.cast hlen)).map (fun x => v[x]), List.map_getElem_sublist hpair', ?_,
    by simp only [List.length_map]⟩
  rw [List.map_map, List.pairwise_map]
  exact key

/-- Coq `size_RS_std`: a word and its standardization have nondecreasing subsequences of
the same lengths, hence Schensted rows of the same length. -/
theorem length_schensted_std (w : List T) :
    (schensted (std w)).length = (schensted w).length := by
  have hmono1 : ∀ i j, (hi : i < (std w).length) → (hj : j < (std w).length) → i < j →
      (std w)[i] ≤ (std w)[j] → w[i]'(by simpa using hi) ≤ w[j]'(by simpa using hj) := by
    intro i j hi hj hij h
    exact (getElem_std_le_iff (by simpa using hi) (by simpa using hj) hij).1 h
  have hmono2 : ∀ i j, (hi : i < w.length) → (hj : j < w.length) → i < j →
      w[i] ≤ w[j] → (std w)[i]'(by simpa using hi) ≤ (std w)[j]'(by simpa using hj) := by
    intro i j hi hj hij h
    exact (getElem_std_le_iff hi hj hij).2 h
  have hset : {n : ℕ | ∃ s : List ℕ, s.Sublist (std w) ∧ s.Pairwise (· ≤ ·) ∧ s.length = n} =
      {n : ℕ | ∃ s : List T, s.Sublist w ∧ s.Pairwise (· ≤ ·) ∧ s.length = n} := by
    ext n
    constructor
    · rintro ⟨s, hsub, hs, rfl⟩
      obtain ⟨t, htsub, ht, htlen⟩ :=
        exists_sublist_of_mono (w := std w) (v := w) (by simp) hmono1 hsub hs
      exact ⟨t, htsub, ht, htlen⟩
    · rintro ⟨s, hsub, hs, rfl⟩
      obtain ⟨t, htsub, ht, htlen⟩ :=
        exists_sublist_of_mono (w := w) (v := std w) (by simp) hmono2 hsub hs
      exact ⟨t, htsub, ht, htlen⟩
  have h1 := schensted_isGreatest (std w)
  rw [hset] at h1
  exact h1.unique (schensted_isGreatest w)

end Young
