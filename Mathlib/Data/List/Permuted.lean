/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.Data.Fintype.List
import Mathlib.Data.List.Multinomial

/-!
# Rearrangements of a word and the multinomial coefficient

This is a port of `theories/Combi/permuted.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi): the rearrangements of a word `w`, that
is the words having the same letters with the same multiplicities, are counted by a
multinomial coefficient (Coq `card_permuted_multinomial`).

The finset of the rearrangements of a multiset `m` of letters is `List.rearrangements m`;
its cardinality times the product of the factorials of the multiplicities is `(m.card)!`.

## Main definitions and results

* `List.rearrangements m` : the finset of the words whose multiset of letters is `m` (Coq
  `permuted`).
* `List.card_rearrangements_mul_prod_factorial` : `|rearrangements m| * ∏ (count a)! =
  (m.card)!`.
* `List.card_rearrangements` : `|rearrangements m| = m.multinomial`.
* `List.card_rearrangements_eq_multinomialList` : the Coq statement
  `card_permuted_multinomial`, with the multinomial coefficient `List.multinomialList` of
  the list of the multiplicities.
* `List.card_permutations_toFinset` : the number of distinct rearrangements of a word.
-/

namespace List

open Nat

variable {α : Type*} [DecidableEq α]

/-- The finset of the words whose multiset of letters is `m`, that is the rearrangements of
any word with letters `m` (Coq `permuted`). -/
def rearrangements (m : Multiset α) : Finset (List α) := m.lists.toFinset

@[simp] lemma mem_rearrangements {m : Multiset α} {l : List α} :
    l ∈ rearrangements m ↔ (l : Multiset α) = m := by
  simp [rearrangements, Multiset.mem_lists_iff, eq_comm]

@[simp] lemma rearrangements_zero : rearrangements (0 : Multiset α) = {[]} := by
  ext l
  simp [Multiset.coe_eq_zero]

/-- The rearrangements of a nonempty multiset of letters, split according to their first
letter. -/
lemma rearrangements_eq_biUnion (m : Multiset α) (hm : m ≠ 0) :
    rearrangements m
      = m.toFinset.biUnion fun a => (rearrangements (m.erase a)).image (a :: ·) := by
  ext l
  simp only [mem_rearrangements, Finset.mem_biUnion, Finset.mem_image, Multiset.mem_toFinset]
  constructor
  · intro h
    match l with
    | [] => exact absurd h.symm hm
    | b :: t =>
      have hb : b ∈ m := by
        rw [← h]
        simp
      refine ⟨b, hb, t, ?_, rfl⟩
      rw [← h, ← Multiset.cons_coe, Multiset.erase_cons_head]
  · rintro ⟨a, ha, t, ht, rfl⟩
    rw [← Multiset.cons_coe, ht, Multiset.cons_erase ha]

/-- The number of rearrangements of a multiset of letters is the sum over the letters of
the numbers of rearrangements of the multiset with that letter removed. -/
lemma card_rearrangements_eq_sum (m : Multiset α) (hm : m ≠ 0) :
    (rearrangements m).card = ∑ a ∈ m.toFinset, (rearrangements (m.erase a)).card := by
  rw [rearrangements_eq_biUnion m hm, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun a _ => ?_
    exact Finset.card_image_of_injective _ (fun _ _ h => (List.cons_inj_right a).1 h)
  · intro a _ b _ hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro l hl hl'
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hl
    obtain ⟨t', -, ht'⟩ := Finset.mem_image.1 hl'
    rw [List.cons.injEq] at ht'
    exact hab ht'.1.symm

/-- The product of the factorials of the multiplicities, after removing one occurrence of a
letter. -/
lemma prod_factorial_count_erase {m : Multiset α} {a : α} (ha : a ∈ m) :
    ∏ b ∈ m.toFinset, Nat.factorial (m.count b)
      = m.count a * ∏ b ∈ (m.erase a).toFinset, Nat.factorial ((m.erase a).count b) := by
  have hsub : (m.erase a).toFinset ⊆ m.toFinset := by
    intro b hb
    simp only [Multiset.mem_toFinset] at hb ⊢
    exact Multiset.mem_of_mem_erase hb
  have hext : ∏ b ∈ (m.erase a).toFinset, Nat.factorial ((m.erase a).count b)
      = ∏ b ∈ m.toFinset, Nat.factorial ((m.erase a).count b) := by
    refine Finset.prod_subset hsub fun b _ hb => ?_
    simp only [Multiset.mem_toFinset] at hb
    rw [Multiset.count_eq_zero_of_notMem hb, Nat.factorial_zero]
  have haf : a ∈ m.toFinset := by simpa using ha
  rw [hext, ← Finset.mul_prod_erase _ _ haf, ← Finset.mul_prod_erase _ _ haf]
  have hcount : (m.erase a).count a = m.count a - 1 := by
    rw [Multiset.count_erase_self]
  have hpos : 0 < m.count a := Multiset.count_pos.2 ha
  have hfact : Nat.factorial (m.count a) = m.count a * Nat.factorial ((m.erase a).count a) := by
    rw [hcount, Nat.mul_factorial_pred hpos.ne']
  rw [hfact, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun b hb => ?_
  have hne : b ≠ a := Finset.ne_of_mem_erase hb
  rw [Multiset.count_erase_of_ne hne]

/-- **The rearrangements of a word are counted by a multinomial coefficient**: the number
of words with multiset of letters `m` times the product of the factorials of the
multiplicities is the factorial of the length. -/
theorem card_rearrangements_mul_prod_factorial (m : Multiset α) :
    (rearrangements m).card * ∏ a ∈ m.toFinset, Nat.factorial (m.count a)
      = Nat.factorial m.card := by
  generalize hn : m.card = n
  induction n using Nat.strong_induction_on generalizing m with
  | _ n ih =>
    rcases eq_or_ne m 0 with rfl | hm
    · simp [← hn]
    · have hcard : 0 < m.card := Multiset.card_pos.2 hm
      rw [card_rearrangements_eq_sum m hm, Finset.sum_mul]
      have hstep : ∀ a ∈ m.toFinset,
          (rearrangements (m.erase a)).card * ∏ b ∈ m.toFinset, Nat.factorial (m.count b)
            = m.count a * Nat.factorial (m.card - 1) := by
        intro a ha
        have ha' : a ∈ m := by simpa using ha
        have hce : (m.erase a).card = m.card - 1 := by
          rw [Multiset.card_erase_of_mem ha']
          rfl
        have hlt : (m.erase a).card < n := by
          rw [hce, ← hn]
          omega
        have := ih _ hlt (m.erase a) rfl
        rw [prod_factorial_count_erase ha']
        calc (rearrangements (m.erase a)).card *
              (m.count a * ∏ b ∈ (m.erase a).toFinset, Nat.factorial ((m.erase a).count b))
            = m.count a * ((rearrangements (m.erase a)).card *
                ∏ b ∈ (m.erase a).toFinset, Nat.factorial ((m.erase a).count b)) := by ring
          _ = m.count a * Nat.factorial (m.erase a).card := by rw [this]
          _ = m.count a * Nat.factorial (m.card - 1) := by rw [hce]
      rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul, Multiset.toFinset_sum_count_eq]
      obtain ⟨k, hk⟩ : ∃ k, m.card = k + 1 := ⟨m.card - 1, by omega⟩
      rw [← hn, hk, Nat.factorial_succ, Nat.add_sub_cancel, Nat.mul_comm]

/-- The factorial identity satisfied by Mathlib's `Multiset.multinomial`. -/
lemma prod_factorial_count_mul_multinomial (m : Multiset α) :
    (∏ a ∈ m.toFinset, Nat.factorial (m.count a)) * m.multinomial = Nat.factorial m.card := by
  rw [Multiset.multinomial, Finsupp.multinomial_eq]
  have h1 : m.toFinsupp.support = m.toFinset := by simp
  have h2 : Nat.multinomial m.toFinsupp.support ⇑(Multiset.toFinsupp m)
      = Nat.multinomial m.toFinset (fun a => m.count a) := by
    rw [h1]
    exact Nat.multinomial_congr (by intro a _; simp)
  rw [h2, Nat.multinomial_spec m.toFinset (fun a => m.count a),
    Multiset.toFinset_sum_count_eq m]

/-- **The number of rearrangements of a word** is the multinomial coefficient of the
multiplicities of its letters. -/
theorem card_rearrangements (m : Multiset α) :
    (rearrangements m).card = m.multinomial := by
  have hpos : 0 < ∏ a ∈ m.toFinset, Nat.factorial (m.count a) :=
    Finset.prod_pos fun a _ => Nat.factorial_pos _
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [card_rearrangements_mul_prod_factorial, mul_comm,
    prod_factorial_count_mul_multinomial]

/-- **The Coq statement `card_permuted_multinomial`**: the number of rearrangements of a
word is the multinomial coefficient of the list of the multiplicities of its letters. -/
theorem card_rearrangements_eq_multinomialList (m : Multiset α) :
    (rearrangements m).card = multinomialList (m.toFinset.toList.map fun a => m.count a) := by
  have hprod : ((m.toFinset.toList.map fun a => m.count a).map Nat.factorial).prod
      = ∏ a ∈ m.toFinset, Nat.factorial (m.count a) := by
    rw [List.map_map, Finset.prod_eq_multiset_prod, ← Finset.coe_toList]
    rfl
  have hsum : (m.toFinset.toList.map fun a => m.count a).sum = m.card := by
    rw [show (m.toFinset.toList.map fun a => m.count a).sum = ∑ a ∈ m.toFinset, m.count a by
      rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList]; rfl,
      Multiset.toFinset_sum_count_eq]
  have hpos : 0 < ∏ a ∈ m.toFinset, Nat.factorial (m.count a) :=
    Finset.prod_pos fun a _ => Nat.factorial_pos _
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [card_rearrangements_mul_prod_factorial, ← hprod,
    multinomialList_mul_prod_factorial, hprod, hsum] at *

/-- The number of distinct rearrangements of a word `w`. -/
theorem card_permutations_toFinset (w : List α) :
    w.permutations.toFinset.card = Multiset.multinomial (w : Multiset α) := by
  have : w.permutations.toFinset = rearrangements (w : Multiset α) := by
    ext l
    simp [rearrangements, List.mem_permutations]
  rw [this, card_rearrangements]

end List
