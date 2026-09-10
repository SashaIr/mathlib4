/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.GetD
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Young.Shape.Conjugate

/-!
# The dominance order on partitions

A Lean 4 port of the dominance order part of `theories/Combi/partition.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

## Main definitions

* `Young.Partdom s t` : all the partial sums of `s` are at most those of `t`
  (Coq `partdom`).

## Main results

* `Young.Partdom.refl`, `Young.Partdom.trans`, `Young.Partdom.antisymm` : dominance
  is a partial order on partitions.
* `Young.sum_map_min` (Coq `sum_conj`) : `∑ min (μ i) k` is the sum of the first
  `k` parts of the conjugate partition.
* `Young.partdom_conjPart_iff` (Coq `partdom_conj_intpartn`) : conjugation is an
  order-reversing involution for the dominance order on partitions of a given size.
-/

@[expose] public section

namespace Young

open List Finset

/-! ### Partial sums of a list -/

lemma getD_map_of_zero {f : ℕ → ℕ} (hf : f 0 = 0) (l : List ℕ) (i : ℕ) :
    (l.map f).getD i 0 = f (l.getD i 0) := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using hi), List.getD_eq_default _ _ hi, hf]

lemma sum_map_eq_sum_range {f : ℕ → ℕ} (hf : f 0 = 0) (l : List ℕ) {n : ℕ} (hn : l.length ≤ n) :
    (l.map f).sum = ∑ i ∈ Finset.range n, f (l.getD i 0) := by
  have h1 : (l.map f).take n = l.map f := List.take_of_length_le (by simpa using hn)
  calc (l.map f).sum = ((l.map f).take n).sum := by rw [h1]
    _ = ∑ i ∈ Finset.range n, (l.map f).getD i 0 := sum_take_eq_sum_range _ _
    _ = ∑ i ∈ Finset.range n, f (l.getD i 0) :=
        Finset.sum_congr rfl fun i _ => getD_map_of_zero hf l i

lemma sum_eq_sum_range (l : List ℕ) {n : ℕ} (hn : l.length ≤ n) :
    l.sum = ∑ i ∈ Finset.range n, l.getD i 0 := by
  have := sum_map_eq_sum_range (f := id) rfl l hn
  simpa using this

/-! ### The dominance order -/

/-- `Partdom s t` : every partial sum of `s` is at most the corresponding partial
sum of `t` (Coq `partdom`). -/
def Partdom (s t : List ℕ) : Prop := ∀ i, (s.take i).sum ≤ (t.take i).sum

@[simp] lemma partdom_nil (s : List ℕ) : Partdom [] s := fun _ => by simp

@[refl] lemma Partdom.refl (s : List ℕ) : Partdom s s := fun _ => le_refl _

lemma Partdom.trans {s t u : List ℕ} (h1 : Partdom s t) (h2 : Partdom t u) : Partdom s u :=
  fun i => le_trans (h1 i) (h2 i)

/-- Coq `sumn_take_inj`. -/
lemma sum_take_inj {s t : List ℕ} (hs : IsPart s) (ht : IsPart t)
    (h : ∀ k, (s.take k).sum = (t.take k).sum) : s = t := by
  refine IsPart.ext_getD hs ht fun i => ?_
  have h1 := h i
  have h2 := h (i + 1)
  rw [sum_take_succ_getD, sum_take_succ_getD] at h2
  omega

/-- Coq `partdom_anti`. -/
lemma Partdom.antisymm {s t : List ℕ} (hs : IsPart s) (ht : IsPart t)
    (h1 : Partdom s t) (h2 : Partdom t s) : s = t :=
  sum_take_inj hs ht fun k => le_antisymm (h1 k) (h2 k)

/-! ### Conjugation reverses the dominance order -/

/-- The partial sums of `incrFirstN c n`. -/
lemma sum_take_incrFirstN (c : List ℕ) (n k : ℕ) :
    ((incrFirstN c n).take k).sum = (c.take k).sum + min k n := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [sum_take_succ_getD, ih, getD_incrFirstN, sum_take_succ_getD]
    by_cases hm : m < n
    · rw [ite_eq_left hm]
      have : min (m + 1) n = min m n + 1 := by omega
      omega
    · rw [ite_eq_right hm]
      have : min (m + 1) n = min m n := by omega
      omega

/-- Coq `sum_conj`: `∑_{l ∈ μ} min l k` is the sum of the `k` first parts of the
conjugate of `μ`. -/
lemma sum_map_min (μ : List ℕ) (k : ℕ) :
    (μ.map (fun l => min l k)).sum = ((conjPart μ).take k).sum := by
  induction μ with
  | nil => simp
  | cons a s ih =>
    rw [conjPart_cons, sum_take_incrFirstN]
    simp only [List.map_cons, List.sum_cons, ih]
    omega

/-- Splitting a part into its truncation at `k` and its excess over `k`. -/
lemma sum_map_min_add_sum_map_sub (l : List ℕ) (k : ℕ) :
    (l.map (fun x => min x k)).sum + (l.map (fun x => x - k)).sum = l.sum := by
  induction l with
  | nil => simp
  | cons a s ih =>
    simp only [List.map_cons, List.sum_cons]
    omega

/-- The key inequality: dominance implies the reverse inequality for the sums of
the excesses over `k` of the parts. -/
lemma sum_map_sub_le_of_partdom {s t : List ℕ} (hs : IsPart s) (hdom : Partdom s t) (k : ℕ) :
    (s.map (fun x => x - k)).sum ≤ (t.map (fun x => x - k)).sum := by
  set m := (conjPart s).getD k 0 with hm
  set N := s.length + t.length + m + 1 with hN
  have hsN : s.length ≤ N := by omega
  have htN : t.length ≤ N := by omega
  have hmN : m ≤ N := by omega
  have hzero : ∀ i, m ≤ i → s.getD i 0 - k = 0 := by
    intro i hi
    have : s.getD i 0 ≤ k := (getD_le_conjPart_iff hs i k).2 (by omega)
    omega
  have hpos : ∀ i, i < m → k < s.getD i 0 := by
    intro i hi
    by_contra hc
    have : m ≤ i := (getD_le_conjPart_iff hs i k).1 (by omega)
    omega
  -- rewrite both sides as sums over `range N`
  have hS : (s.map (fun x => x - k)).sum = ∑ i ∈ Finset.range N, (s.getD i 0 - k) :=
    sum_map_eq_sum_range (by simp) s hsN
  have hT : (t.map (fun x => x - k)).sum = ∑ i ∈ Finset.range N, (t.getD i 0 - k) :=
    sum_map_eq_sum_range (by simp) t htN
  -- the sum for `s` only involves the first `m` parts
  have hS' : ∑ i ∈ Finset.range N, (s.getD i 0 - k) = ∑ i ∈ Finset.range m, (s.getD i 0 - k) := by
    refine (Finset.sum_subset (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_).symm
    intro i _ hi
    exact hzero i (by simpa using hi)
  -- and it is exactly the partial sum minus `m * k`
  have hSm : (∑ i ∈ Finset.range m, (s.getD i 0 - k)) + m * k = (s.take m).sum := by
    rw [sum_take_eq_sum_range]
    have : ∑ i ∈ Finset.range m, ((s.getD i 0 - k) + k) = ∑ i ∈ Finset.range m, s.getD i 0 :=
      Finset.sum_congr rfl fun i hi => by
        have := hpos i (Finset.mem_range.1 hi); omega
    rw [Finset.sum_add_distrib] at this
    simpa [Finset.sum_const, mul_comm] using this
  -- for `t`, the partial sum is at most the sum of the excesses plus `m * k`
  have hTm : (t.take m).sum ≤ (∑ i ∈ Finset.range m, (t.getD i 0 - k)) + m * k := by
    rw [sum_take_eq_sum_range]
    have : ∑ i ∈ Finset.range m, t.getD i 0 ≤ ∑ i ∈ Finset.range m, ((t.getD i 0 - k) + k) :=
      Finset.sum_le_sum fun i _ => by omega
    rw [Finset.sum_add_distrib] at this
    simpa [Finset.sum_const, mul_comm] using this
  have hTsub : ∑ i ∈ Finset.range m, (t.getD i 0 - k) ≤ ∑ i ∈ Finset.range N, (t.getD i 0 - k) :=
    Finset.sum_le_sum_of_subset (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
  have hdm := hdom m
  omega

/-- Coq `partdom_conj_intpartn`, one direction. -/
lemma partdom_conjPart {s t : List ℕ} (hs : IsPart s) (hsum : s.sum = t.sum)
    (hdom : Partdom s t) : Partdom (conjPart t) (conjPart s) := by
  intro k
  rw [← sum_map_min t k, ← sum_map_min s k]
  have h1 := sum_map_min_add_sum_map_sub s k
  have h2 := sum_map_min_add_sum_map_sub t k
  have h3 := sum_map_sub_le_of_partdom hs hdom k
  omega

/-- Coq `partdom_conj_intpartn`: on partitions of a fixed size, conjugation reverses
the dominance order. -/
lemma partdom_conjPart_iff {s t : List ℕ} (hs : IsPart s) (ht : IsPart t) (hsum : s.sum = t.sum) :
    Partdom (conjPart t) (conjPart s) ↔ Partdom s t := by
  refine ⟨fun h => ?_, partdom_conjPart hs hsum⟩
  have hc := partdom_conjPart (isPart_conjPart ht) (by simp [hsum]) h
  rwa [conjPart_conjPart hs, conjPart_conjPart ht] at hc

/-! ### Extremal partitions for the dominance order -/

/-- Coq `partdom_rowpartn`: the one-row partition `[n]` dominates every partition of `n`. -/
lemma partdom_row {s : List ℕ} {n : ℕ} (hsum : s.sum = n) : Partdom s [n] := by
  intro i
  cases i with
  | zero => simp
  | succ j =>
    have htake : ([n] : List ℕ).take (j + 1) = [n] := by simp
    rw [htake]
    simpa [hsum] using sum_take_le_sum s (j + 1)

/-- Coq `partdom_colpartn`: the one-column partition `1^n` is dominated by every
partition of `n`. -/
lemma partdom_col {s : List ℕ} (hs : IsPart s) {n : ℕ} (hsum : s.sum = n) :
    Partdom (List.replicate n 1) s := by
  intro i
  rw [List.take_replicate, List.sum_replicate, smul_eq_mul, mul_one]
  rcases Nat.lt_or_ge s.length i with hi | hi
  · rw [List.take_of_length_le hi.le, hsum]
    exact Nat.min_le_right _ _
  · have hlen : s.length ≤ n := hsum ▸ hs.length_le_sum
    have hmin : min i n = i := by omega
    rw [hmin, sum_take_eq_sum_range]
    calc i = ∑ _j ∈ Finset.range i, 1 := by simp
    _ ≤ ∑ j ∈ Finset.range i, s.getD j 0 :=
      Finset.sum_le_sum fun j hj => hs.getD_pos (lt_of_lt_of_le (Finset.mem_range.1 hj) hi)

end Young
