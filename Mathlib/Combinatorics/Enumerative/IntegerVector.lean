/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Data.List.Nodup
import Mathlib.Combinatorics.Young.Tableau.Basic

/-!
# Integer vectors of given sum and length, and cuttings of a list

This file ports `theories/Combi/vectNK.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi).  We enumerate the lists of natural
numbers of a given sum and a given length, and use them to enumerate the ways of cutting a
list into a given number of consecutive slices.

## Main definitions

* `List.vectNK n k` : the list of the lists of natural numbers of sum `n` and length `k`
  (Coq `vect_n_k`).
* `List.reshape sh s` : the list `s` cut into consecutive slices of lengths the entries of
  `sh` (Coq `reshape`).
* `List.cutK k s` : the list of the cuttings of `s` into `k` consecutive slices (Coq
  `cut_k`).
* `List.cut3 s` : the list of the cuttings of `s` into three consecutive slices (Coq
  `cut3`).

## Main results

* `List.mem_vectNK` : `s ∈ vectNK n k` if and only if `s` has sum `n` and length `k` (Coq
  `vect_n_kP`).
* `List.nodup_vectNK` : the enumeration has no repetition (Coq `uniq_vect_n_k`).
* `List.mem_cutK_iff` : `ss` is a cutting of `s` into `ss.length` slices if and only if
  `s` is the concatenation of `ss` (Coq `flatten_equiv_cut_k`).
* `List.mem_cut3_iff` : `(a, b, c) ∈ cut3 s` if and only if `s = a ++ b ++ c` (Coq
  `cat3_equiv_cut3`).
-/

namespace List

/-! ### Integer vectors of given sum and length -/

/-- The list of the lists of natural numbers of sum `n` and length `k` (Coq
`vect_n_k`). -/
def vectNK : ℕ → ℕ → List (List ℕ)
  | n, 0 => if n = 0 then [[]] else []
  | n, k + 1 => ((List.range (n + 1)).map fun i => (vectNK (n - i) k).map (i :: ·)).flatten

@[simp] lemma vectNK_zero_length (n : ℕ) : vectNK n 0 = if n = 0 then [[]] else [] := rfl

lemma vectNK_succ (n k : ℕ) :
    vectNK n (k + 1) =
      ((List.range (n + 1)).map fun i => (vectNK (n - i) k).map (i :: ·)).flatten := rfl

/-- **The enumeration of the integer vectors of given sum and length** (Coq
`vect_n_kP`). -/
theorem mem_vectNK : ∀ {k n : ℕ} {s : List ℕ}, s ∈ vectNK n k ↔ s.sum = n ∧ s.length = k
  | 0, n, s => by
    rw [vectNK_zero_length]
    constructor
    · intro h
      by_cases hn : n = 0
      · rw [ite_eq_left hn, List.mem_singleton] at h
        subst h
        exact ⟨hn.symm, rfl⟩
      · rw [ite_eq_right hn] at h
        exact absurd h List.not_mem_nil
    · rintro ⟨hsum, hlen⟩
      rw [List.length_eq_zero_iff] at hlen
      subst hlen
      simp at hsum
      rw [ite_eq_left hsum.symm, List.mem_singleton]
  | k + 1, n, s => by
    rw [vectNK_succ]
    constructor
    · intro h
      obtain ⟨l, hl, hs⟩ := List.mem_flatten.1 h
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hl
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
      obtain ⟨hsum, hlen⟩ := mem_vectNK.1 ht
      rw [List.mem_range] at hi
      refine ⟨?_, by rw [List.length_cons, hlen]⟩
      rw [List.sum_cons, hsum]
      omega
    · rintro ⟨hsum, hlen⟩
      cases s with
      | nil => simp at hlen
      | cons i t =>
        rw [List.sum_cons] at hsum
        rw [List.length_cons] at hlen
        refine List.mem_flatten.2 ⟨(vectNK (n - i) k).map (i :: ·),
          List.mem_map.2 ⟨i, List.mem_range.2 (by omega), rfl⟩,
          List.mem_map.2 ⟨t, mem_vectNK.2 ⟨by omega, by omega⟩, rfl⟩⟩

/-- The only vector of sum zero is the zero vector (Coq `vect_0_k`). -/
lemma vectNK_zero (k : ℕ) : vectNK 0 k = [List.replicate k 0] := by
  induction k with
  | zero => rw [vectNK_zero_length, ite_eq_left rfl, List.replicate_zero]
  | succ k ih =>
    rw [vectNK_succ, List.range_one, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, Nat.zero_sub, ih, List.map_cons, List.map_nil,
      List.replicate_succ]

/-- The enumeration of the integer vectors of given sum and length has no repetition (Coq
`uniq_vect_n_k`). -/
theorem nodup_vectNK : ∀ (n k : ℕ), (vectNK n k).Nodup
  | n, 0 => by
    rw [vectNK_zero_length]
    by_cases hn : n = 0
    · rw [ite_eq_left hn]
      simp
    · rw [ite_eq_right hn]
      simp
  | n, k + 1 => by
    rw [vectNK_succ, List.nodup_flatten]
    constructor
    · intro l hl
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hl
      exact (nodup_vectNK (n - i) k).map fun a b h => (List.cons.injEq .. ▸ h).2
    · rw [List.pairwise_map]
      refine List.Pairwise.imp_of_mem ?_ (List.nodup_range (n := n + 1))
      intro i j hi hj hij u hu hu'
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 hu
      obtain ⟨b, _, hb⟩ := List.mem_map.1 hu'
      exact hij (List.cons.injEq .. ▸ hb).1.symm

/-! ### Cutting a list into slices -/

variable {α : Type*}

/-- The list `s` cut into consecutive slices of lengths the entries of `sh` (Coq
`reshape`). -/
def reshape : List ℕ → List α → List (List α)
  | [], _ => []
  | n :: sh, s => s.take n :: reshape sh (s.drop n)

@[simp] lemma reshape_nil (s : List α) : reshape [] s = [] := rfl

@[simp] lemma reshape_cons (n : ℕ) (sh : List ℕ) (s : List α) :
    reshape (n :: sh) s = s.take n :: reshape sh (s.drop n) := rfl

/-- Concatenating the slices of a cutting gives back the list (Coq `reshapeKr`). -/
lemma flatten_reshape : ∀ (sh : List ℕ) (s : List α), s.length ≤ sh.sum →
    (reshape sh s).flatten = s
  | [], s, h => by
    rw [reshape_nil, List.flatten_nil, eq_comm, ← List.length_eq_zero_iff]
    simpa using h
  | n :: sh, s, h => by
    rw [reshape_cons, List.flatten_cons,
      flatten_reshape sh (s.drop n) (by rw [List.length_drop]; simp at h; omega),
      List.take_append_drop]

/-- The shape of a cutting is the given list of lengths (Coq `reshapeKl`). -/
lemma shape_reshape : ∀ (sh : List ℕ) (s : List α), sh.sum ≤ s.length →
    shape (reshape sh s) = sh
  | [], s, _ => rfl
  | n :: sh, s, h => by
    rw [List.sum_cons] at h
    rw [reshape_cons, shape, List.map_cons, ← shape,
      shape_reshape sh (s.drop n) (by rw [List.length_drop]; omega),
      List.length_take, min_eq_left (by omega)]

/-- Cutting a concatenation along its shape gives back the slices (Coq `flattenK`). -/
lemma reshape_shape : ∀ ss : List (List α), reshape (shape ss) ss.flatten = ss
  | [] => rfl
  | a :: ss => by
    rw [shape, List.map_cons, ← shape, List.flatten_cons, reshape_cons,
      List.take_left' rfl, List.drop_left' rfl, reshape_shape ss]

/-- The list of the cuttings of `s` into `k` consecutive slices (Coq `cut_k`). -/
def cutK (k : ℕ) (s : List α) : List (List (List α)) :=
  (vectNK s.length k).map fun sh => reshape sh s

/-- A list of slices is a cutting of its concatenation (Coq `cut_k_flatten`). -/
lemma mem_cutK_flatten (ss : List (List α)) : ss ∈ cutK ss.length ss.flatten :=
  List.mem_map.2 ⟨shape ss, mem_vectNK.2 ⟨by
    rw [shape, ← List.length_flatten], by rw [shape, List.length_map]⟩, reshape_shape ss⟩

/-- The length of a cutting is the number of slices (Coq `size_cut_k`). -/
lemma length_of_mem_cutK {k : ℕ} {s : List α} {ss : List (List α)} (h : ss ∈ cutK k s) :
    ss.length = k := by
  obtain ⟨sh, hsh, rfl⟩ := List.mem_map.1 h
  obtain ⟨hsum, hlen⟩ := mem_vectNK.1 hsh
  have hs : shape (reshape sh s) = sh := shape_reshape sh s (by omega)
  have hlm : (reshape sh s).length = (shape (reshape sh s)).length := by
    rw [shape, List.length_map]
  rw [hlm, hs, hlen]

/-- **The cuttings of a list into a given number of slices are exactly the ways of writing
it as a concatenation** (Coq `flatten_equiv_cut_k`). -/
theorem mem_cutK_iff {s : List α} {ss : List (List α)} :
    s = ss.flatten ↔ ss ∈ cutK ss.length s := by
  constructor
  · rintro rfl
    exact mem_cutK_flatten ss
  · intro h
    obtain ⟨sh, hsh, hss⟩ := List.mem_map.1 h
    obtain ⟨hsum, -⟩ := mem_vectNK.1 hsh
    rw [← hss, flatten_reshape sh s (by omega)]

/-! ### Cutting a list into three slices -/

/-- The list of the cuttings of `s` into three consecutive slices (Coq `cut3`). -/
def cut3 (s : List α) : List (List α × List α × List α) :=
  (cutK 3 s).map fun ss =>
    match ss with
    | [a, b, c] => (a, b, c)
    | _ => ([], [], [])

/-- **The cuttings of a list into three slices are exactly the ways of writing it as a
concatenation of three lists** (Coq `cat3_equiv_cut3`). -/
theorem mem_cut3_iff {s a b c : List α} : s = a ++ b ++ c ↔ (a, b, c) ∈ cut3 s := by
  have hflat : ([a, b, c] : List (List α)).flatten = a ++ b ++ c := by
    simp
  constructor
  · intro h
    refine List.mem_map.2 ⟨[a, b, c], ?_, rfl⟩
    have := mem_cutK_flatten [a, b, c]
    rwa [hflat, ← h, show ([a, b, c] : List (List α)).length = 3 from rfl] at this
  · intro h
    obtain ⟨ss, hss, heq⟩ := List.mem_map.1 h
    have hlen := length_of_mem_cutK hss
    obtain ⟨x, y, z, rfl⟩ : ∃ x y z, ss = [x, y, z] := by
      match ss, hlen with
      | [x, y, z], _ => exact ⟨x, y, z, rfl⟩
    obtain ⟨rfl, rfl, rfl⟩ : x = a ∧ y = b ∧ z = c := by
      simpa [Prod.ext_iff] using heq
    rw [← hflat]
    exact mem_cutK_iff.2 (by rwa [hlen])

end List
