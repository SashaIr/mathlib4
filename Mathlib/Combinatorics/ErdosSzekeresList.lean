/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Interval.Finset.Nat

/-!
# The Erdős–Szekeres theorem

A Lean 4 port of `theories/Erdos_Szekeres/Erdos_Szekeres.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

The Coq statement reads: if a sequence `s` has more than `m * n` entries, then it
contains a weakly increasing subsequence of length more than `m`, or a strictly
decreasing subsequence of length more than `n`.  Here subsequences are `List.Sublist`s
and being sorted is `List.IsChain`.

Unlike the version for sequences of *distinct* values, this statement holds for an
arbitrary list, thanks to the asymmetry between the weak and the strict order.

The proof is the classical pigeonhole argument: label each position by the maximal
length of a weakly increasing (resp. strictly decreasing) subsequence ending there,
and check that the pair of labels determines the position.

## Main results

* `List.erdos_szekeres` : the theorem above.
-/

namespace List

open Finset

variable {T : Type*} [LinearOrder T]

/-! ### Extracting a subsequence from a set of positions -/

omit [LinearOrder T] in
/-- A set `u` of positions of `s` along which the entries are `R`-increasing gives a
sublist of `s` which is an `R`-chain of length `#u`. -/
lemma exists_sublist_isChain (s : List T) (u : Finset (Fin s.length)) (R : T → T → Prop)
    [Trans R R R] (h : ∀ a ∈ u, ∀ b ∈ u, a < b → R (s.get a) (s.get b)) :
    ∃ t : List T, t.Sublist s ∧ List.IsChain R t ∧ t.length = u.card := by
  refine ⟨List.ofFn (fun i : Fin u.card => s.get ((u.orderIsoOfFin rfl i) : Fin s.length)),
    ?_, ?_, by simp⟩
  · set t := List.ofFn (fun i : Fin u.card => s.get ((u.orderIsoOfFin rfl i) : Fin s.length))
      with ht
    have hlen : t.length = u.card := by simp [ht]
    rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
    refine ⟨((Fin.castOrderIso hlen).toOrderEmbedding).trans
      (((u.orderIsoOfFin rfl).toOrderEmbedding).trans (OrderEmbedding.subtype (· ∈ u))), ?_⟩
    intro ix
    simp only [ht, List.get_eq_getElem, List.getElem_ofFn]
    rfl
  · rw [List.isChain_iff_pairwise, List.pairwise_ofFn]
    intro i j hij
    refine h _ (u.orderIsoOfFin rfl i).2 _ (u.orderIsoOfFin rfl j).2 ?_
    exact_mod_cast (u.orderIsoOfFin rfl).lt_iff_lt.2 hij

/-! ### The maximal length of an `R`-increasing subsequence ending at a position -/

open Classical in
/-- The sets of positions of `s`, all at most `i` and containing `i`, along which the
entries of `s` are `R`-increasing. -/
noncomputable def chainsEndingAt (s : List T) (R : T → T → Prop) (i : Fin s.length) :
    Finset (Finset (Fin s.length)) :=
  Finset.univ.filter fun u => i ∈ u ∧ (∀ x ∈ u, x ≤ i) ∧
    ∀ a ∈ u, ∀ b ∈ u, a < b → R (s.get a) (s.get b)

omit [LinearOrder T] in
lemma mem_chainsEndingAt {s : List T} {R : T → T → Prop} {i : Fin s.length}
    {u : Finset (Fin s.length)} :
    u ∈ chainsEndingAt s R i ↔ i ∈ u ∧ (∀ x ∈ u, x ≤ i) ∧
      ∀ a ∈ u, ∀ b ∈ u, a < b → R (s.get a) (s.get b) := by
  classical
  simp [chainsEndingAt]

omit [LinearOrder T] in
lemma singleton_mem_chainsEndingAt (s : List T) (R : T → T → Prop) (i : Fin s.length) :
    ({i} : Finset (Fin s.length)) ∈ chainsEndingAt s R i := by
  rw [mem_chainsEndingAt]
  refine ⟨by simp, by simp, ?_⟩
  intro a ha b hb hab
  simp only [Finset.mem_singleton] at ha hb
  subst ha
  subst hb
  exact absurd hab (lt_irrefl _)

open Classical in
/-- The maximal length of an `R`-increasing subsequence of `s` ending at position `i`. -/
noncomputable def maxChainEndingAt (s : List T) (R : T → T → Prop) (i : Fin s.length) : ℕ :=
  ((chainsEndingAt s R i).image Finset.card).max' ⟨1, by
    refine Finset.mem_image.2 ⟨{i}, singleton_mem_chainsEndingAt s R i, by simp⟩⟩

omit [LinearOrder T] in
lemma one_le_maxChainEndingAt (s : List T) (R : T → T → Prop) (i : Fin s.length) :
    1 ≤ maxChainEndingAt s R i := by
  classical
  refine Finset.le_max' _ _ ?_
  exact Finset.mem_image.2 ⟨{i}, singleton_mem_chainsEndingAt s R i, by simp⟩

omit [LinearOrder T] in
lemma exists_chain_card_eq_maxChainEndingAt (s : List T) (R : T → T → Prop) (i : Fin s.length) :
    ∃ u ∈ chainsEndingAt s R i, u.card = maxChainEndingAt s R i := by
  classical
  have := Finset.max'_mem ((chainsEndingAt s R i).image Finset.card)
    ⟨1, Finset.mem_image.2 ⟨{i}, singleton_mem_chainsEndingAt s R i, by simp⟩⟩
  rw [Finset.mem_image] at this
  obtain ⟨u, hu, hcard⟩ := this
  exact ⟨u, hu, hcard⟩

omit [LinearOrder T] in
/-- If the entry at `i` is `R`-below the entry at a later position `j`, then the maximal
`R`-increasing subsequence ending at `j` is strictly longer. -/
lemma maxChainEndingAt_lt {s : List T} {R : T → T → Prop} [Trans R R R] {i j : Fin s.length}
    (hij : i < j) (hR : R (s.get i) (s.get j)) :
    maxChainEndingAt s R i < maxChainEndingAt s R j := by
  classical
  obtain ⟨u, hu, hcard⟩ := exists_chain_card_eq_maxChainEndingAt s R i
  rw [mem_chainsEndingAt] at hu
  obtain ⟨hiu, hle, hchain⟩ := hu
  have hj : j ∉ u := fun hc => absurd (hle j hc) (not_le.2 hij)
  have hmem : insert j u ∈ chainsEndingAt s R j := by
    rw [mem_chainsEndingAt]
    refine ⟨Finset.mem_insert_self _ _, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact le_refl _
      · exact le_trans (hle x hx) hij.le
    · have hbj : ∀ x ∈ insert j u, x ≤ j := by
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact le_refl _
        · exact le_trans (hle x hx) hij.le
      intro a ha b hb hab
      rcases Finset.mem_insert.1 ha with haj | hau
      · exact absurd hab (not_lt.2 (by rw [haj]; exact hbj b hb))
      · rcases Finset.mem_insert.1 hb with hbj' | hbu
        · subst hbj'
          rcases eq_or_lt_of_le (hle a hau) with heq | hai
          · rw [heq]; exact hR
          · exact Trans.trans (hchain a hau i hiu hai) hR
        · exact hchain a hau b hbu hab
  have hcard' : (insert j u).card = u.card + 1 := Finset.card_insert_of_notMem hj
  have : u.card + 1 ≤ maxChainEndingAt s R j := by
    rw [← hcard']
    exact Finset.le_max' _ _ (Finset.mem_image.2 ⟨insert j u, hmem, rfl⟩)
  omega

/-! ### The theorem -/

/-- **Erdős–Szekeres theorem** (Coq-Combi `Erdos_Szekeres`): a list with more than
`m * n` entries contains a weakly increasing sublist of length more than `m`, or a
strictly decreasing sublist of length more than `n`. -/
theorem erdos_szekeres (m n : ℕ) (s : List T) (hs : m * n < s.length) :
    (∃ t : List T, t.Sublist s ∧ List.IsChain (· ≤ ·) t ∧ m < t.length) ∨
      (∃ t : List T, t.Sublist s ∧ List.IsChain (· > ·) t ∧ n < t.length) := by
  classical
  set A : Fin s.length → ℕ := fun i => maxChainEndingAt s (· ≤ ·) i with hA
  set B : Fin s.length → ℕ := fun i => maxChainEndingAt s (· > ·) i with hB
  by_cases hex : ∃ i : Fin s.length, m < A i ∨ n < B i
  · obtain ⟨i, hi⟩ := hex
    rcases hi with hi | hi
    · left
      obtain ⟨u, hu, hcard⟩ := exists_chain_card_eq_maxChainEndingAt s (· ≤ ·) i
      rw [mem_chainsEndingAt] at hu
      obtain ⟨t, hsub, hchain, hlen⟩ := exists_sublist_isChain s u (· ≤ ·) hu.2.2
      refine ⟨t, hsub, hchain, ?_⟩
      rw [hlen, hcard]
      exact hi
    · right
      obtain ⟨u, hu, hcard⟩ := exists_chain_card_eq_maxChainEndingAt s (· > ·) i
      rw [mem_chainsEndingAt] at hu
      obtain ⟨t, hsub, hchain, hlen⟩ := exists_sublist_isChain s u (· > ·) hu.2.2
      refine ⟨t, hsub, hchain, ?_⟩
      rw [hlen, hcard]
      exact hi
  · exfalso
    push Not at hex
    -- the pair of labels is injective, so there are at most `m * n` positions
    have hinj : Set.InjOn (fun i : Fin s.length => (A i, B i))
        (↑(Finset.univ : Finset (Fin s.length)) : Set (Fin s.length)) := by
      intro i _ j _ hij
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · rcases le_or_gt (s.get i) (s.get j) with hle | hlt
        · exact absurd congr(($hij).1) (maxChainEndingAt_lt h hle).ne
        · exact absurd congr(($hij).2) (maxChainEndingAt_lt (R := (· > ·)) h hlt).ne
      · rcases le_or_gt (s.get j) (s.get i) with hle | hlt
        · exact absurd congr(($hij).1) (maxChainEndingAt_lt h hle).ne'
        · exact absurd congr(($hij).2) (maxChainEndingAt_lt (R := (· > ·)) h hlt).ne'
    have hmaps : Set.MapsTo (fun i : Fin s.length => (A i, B i))
        (↑(Finset.univ : Finset (Fin s.length)) : Set (Fin s.length))
        (↑(Finset.Icc 1 m ×ˢ Finset.Icc 1 n) : Set (ℕ × ℕ)) := by
      intro i _
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Icc]
      exact ⟨⟨one_le_maxChainEndingAt s (· ≤ ·) i, (hex i).1⟩,
        ⟨one_le_maxChainEndingAt s (· > ·) i, (hex i).2⟩⟩
    have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
    simp only [Finset.card_univ, Fintype.card_fin, Finset.card_product, Nat.card_Icc,
      Nat.add_sub_cancel] at hcard
    omega

end List
