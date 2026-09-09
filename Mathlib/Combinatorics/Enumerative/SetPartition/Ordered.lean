/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Ring

/-!
# Ordered set partitions with prescribed block sizes

Ported from the Coq-Combi development (`Combi/set_partition.v`), which counts the
set partitions of a finite set whose blocks have prescribed cardinalities.  This file
contains the *ordered* version, which is the combinatorial engine of that count: the
lists `[B₁, …, B_r]` of pairwise disjoint blocks covering a finite set `s`, with
`|B_i|` prescribed by a list `l` of natural numbers.

## Main definitions

* `Finpartition.listUnion` : the union of a list of finsets.
* `Finpartition.orderedParts s l` : the finset of the ordered set partitions of `s` whose
  block sizes are prescribed by `l`.

## Main results

* `Finpartition.mem_orderedParts` : membership in `orderedParts s l`.
* `Finpartition.card_orderedParts_mul_prod_factorial` : the multinomial count
  `(orderedParts s l).card * (l.map (·!)).prod = s.card !`.
-/

@[expose] public section

namespace Finpartition

open Finset

variable {α : Type*} [DecidableEq α]

/-! ### The union of a list of finsets -/

/-- The union of a list of finsets. -/
def listUnion (L : List (Finset α)) : Finset α := L.foldr (· ∪ ·) ∅

@[simp] lemma listUnion_nil : listUnion ([] : List (Finset α)) = ∅ := rfl

@[simp] lemma listUnion_cons (B : Finset α) (L : List (Finset α)) :
    listUnion (B :: L) = B ∪ listUnion L := rfl

@[simp] lemma mem_listUnion {a : α} {L : List (Finset α)} :
    a ∈ listUnion L ↔ ∃ B ∈ L, a ∈ B := by
  induction L with
  | nil => simp
  | cons B L ih => simp [ih]

lemma subset_listUnion {B : Finset α} {L : List (Finset α)} (hB : B ∈ L) :
    B ⊆ listUnion L := fun _ ha => mem_listUnion.2 ⟨B, hB, ha⟩

/-! ### Ordered set partitions -/

/-- `orderedParts s l` is the finset of lists `[B₁, …, B_r]` of pairwise disjoint
subsets of `s` whose union is `s` and whose cardinalities are the entries of `l`. -/
def orderedParts : Finset α → List ℕ → Finset (List (Finset α))
  | s, [] => if s = ∅ then {[]} else ∅
  | s, (k :: t) => (s.powersetCard k).biUnion fun B => (orderedParts (s \ B) t).image (B :: ·)

lemma orderedParts_nil (s : Finset α) :
    orderedParts s [] = if s = ∅ then {[]} else ∅ := rfl

lemma orderedParts_cons (s : Finset α) (k : ℕ) (t : List ℕ) :
    orderedParts s (k :: t) =
      (s.powersetCard k).biUnion fun B => (orderedParts (s \ B) t).image (B :: ·) := rfl

/-- Membership in `orderedParts`: a list of blocks of the prescribed sizes, pairwise
disjoint, with union `s`. -/
theorem mem_orderedParts {s : Finset α} {l : List ℕ} {L : List (Finset α)} :
    L ∈ orderedParts s l ↔
      L.map Finset.card = l ∧ L.Pairwise Disjoint ∧ listUnion L = s := by
  induction l generalizing s L with
  | nil =>
    rw [orderedParts_nil]
    constructor
    · intro hL
      by_cases hs : s = ∅
      · rw [ite_eq_left hs] at hL
        simp only [Finset.mem_singleton] at hL
        subst hL
        simp [hs]
      · rw [ite_eq_right hs] at hL
        simp at hL
    · rintro ⟨hmap, -, hun⟩
      obtain rfl : L = [] := List.map_eq_nil_iff.1 hmap
      simp only [listUnion_nil] at hun
      rw [ite_eq_left hun.symm]
      simp
  | cons k t ih =>
    rw [orderedParts_cons]
    simp only [Finset.mem_biUnion, Finset.mem_powersetCard, Finset.mem_image]
    constructor
    · rintro ⟨B, ⟨hBs, hBk⟩, L', hL', rfl⟩
      rw [ih] at hL'
      obtain ⟨hmap, hpw, hun⟩ := hL'
      refine ⟨by simp [hmap, hBk], ?_, ?_⟩
      · refine List.pairwise_cons.2 ⟨fun x hx => ?_, hpw⟩
        have hxsub : x ⊆ s \ B := hun ▸ subset_listUnion hx
        exact Finset.disjoint_left.2 fun a haB hax =>
          (Finset.mem_sdiff.1 (hxsub hax)).2 haB
      · simp only [listUnion_cons, hun]
        exact Finset.union_sdiff_of_subset hBs
    · rintro ⟨hmap, hpw, hun⟩
      obtain ⟨B, L', rfl⟩ : ∃ B L', L = B :: L' := by
        cases L with
        | nil => simp at hmap
        | cons B L' => exact ⟨B, L', rfl⟩
      simp only [List.map_cons, List.cons.injEq] at hmap
      obtain ⟨hBk, hmap⟩ := hmap
      obtain ⟨hdisj, hpw⟩ := List.pairwise_cons.1 hpw
      simp only [listUnion_cons] at hun
      have hBs : B ⊆ s := hun ▸ Finset.subset_union_left
      have hL'eq : listUnion L' = s \ B := by
        ext a
        simp only [Finset.mem_sdiff, ← hun, Finset.mem_union]
        constructor
        · intro ha
          obtain ⟨C, hC, haC⟩ := mem_listUnion.1 ha
          exact ⟨Or.inr ha, fun haB => (Finset.disjoint_left.1 (hdisj C hC)) haB haC⟩
        · rintro ⟨h | h, hnB⟩
          · exact absurd h hnB
          · exact h
      exact ⟨B, ⟨hBs, hBk⟩, L', (ih).2 ⟨hmap, hpw, hL'eq⟩, rfl⟩

/-- **The multinomial count of ordered set partitions.** -/
theorem card_orderedParts_mul_prod_factorial (s : Finset α) (l : List ℕ) (h : l.sum = s.card) :
    (orderedParts s l).card * (l.map Nat.factorial).prod = Nat.factorial s.card := by
  induction l generalizing s with
  | nil =>
    simp only [List.sum_nil] at h
    have hs : s = ∅ := Finset.card_eq_zero.1 h.symm
    subst hs
    simp [orderedParts_nil]
  | cons k t ih =>
    have hk : k ≤ s.card := by
      simp only [List.sum_cons] at h
      omega
    have hcard : (orderedParts s (k :: t)).card
        = ∑ B ∈ s.powersetCard k, (orderedParts (s \ B) t).card := by
      rw [orderedParts_cons, Finset.card_biUnion]
      · exact Finset.sum_congr rfl fun B _ =>
          Finset.card_image_of_injective _ (fun _ _ h => (List.cons.injEq _ _ _ _ ▸ h).2)
      · intro B _ C _ hBC
        refine Finset.disjoint_left.2 ?_
        rintro L hL hL'
        simp only [Finset.mem_image] at hL hL'
        obtain ⟨L1, -, rfl⟩ := hL
        obtain ⟨L2, -, h2⟩ := hL'
        exact hBC (List.cons.injEq _ _ _ _ ▸ h2).1.symm
    have hsub : ∀ B ∈ s.powersetCard k,
        (orderedParts (s \ B) t).card * (t.map Nat.factorial).prod
          = Nat.factorial (s.card - k) := by
      intro B hB
      obtain ⟨hBs, hBk⟩ := Finset.mem_powersetCard.1 hB
      have hcd : (s \ B).card = s.card - k := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.2 hBs, hBk]
      rw [ih (s \ B) (by simp only [List.sum_cons] at h; omega), hcd]
    calc (orderedParts s (k :: t)).card * ((k :: t).map Nat.factorial).prod
        = (∑ B ∈ s.powersetCard k, (orderedParts (s \ B) t).card
            * (t.map Nat.factorial).prod) * Nat.factorial k := by
          rw [hcard, ← Finset.sum_mul]
          simp only [List.map_cons, List.prod_cons]
          ring
      _ = (s.card.choose k * Nat.factorial (s.card - k)) * Nat.factorial k := by
          rw [Finset.sum_congr rfl hsub, Finset.sum_const, Finset.card_powersetCard,
            smul_eq_mul]
      _ = Nat.factorial s.card := by
          rw [← Nat.choose_mul_factorial_mul_factorial hk]
          ring

end Finpartition
