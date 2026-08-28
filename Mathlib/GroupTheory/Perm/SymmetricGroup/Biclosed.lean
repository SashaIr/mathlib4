/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.GroupTheory.Perm.SymmetricGroup.Inversions

/-!
# Inversion sets are the biclosed sets of pairs

Following `theories/SymGroup/weak_order.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we characterise the sets of pairs
which arise as the set of inversions of a permutation of `Fin N`: they are the *biclosed*
sets, that is the sets `A` of pairs `a < b` such that, for `a < b < c`,

* if `(a, b) ∈ A` and `(b, c) ∈ A` then `(a, c) ∈ A` (`A` is closed), and
* if `(a, c) ∈ A` then `(a, b) ∈ A` or `(b, c) ∈ A` (the complement of `A` is closed).

Given a biclosed set `A`, the relation `Equiv.Perm.Before A`, "`x` comes before `y`", which
holds for `x < y` when `(x, y) ∉ A` and for `y < x` when `(y, x) ∈ A`, is a strict linear
order, and the permutation `Equiv.Perm.permOfBiclosed A` sending each letter to its rank
for that order has `A` as its set of inversions.

We also show that the transitive closure of a union of two biclosed sets is biclosed; this
is what produces the join of two permutations for the weak order.

## Main definitions and results

* `Equiv.Perm.IsBiclosed A` : the set of pairs `A` is biclosed.
* `Equiv.Perm.isBiclosed_invSet` : the set of inversions of a permutation is biclosed.
* `Equiv.Perm.permOfBiclosed` and `Equiv.Perm.invSet_permOfBiclosed` : the permutation
  attached to a biclosed set, whose inversion set is that set.
* `Equiv.Perm.isBiclosed_iff_exists_invSet` : a set of pairs is biclosed if and only if it
  is the set of inversions of a permutation.
* `Equiv.Perm.closurePairs` : the transitive closure of a set of pairs, and
  `Equiv.Perm.isBiclosed_closurePairs_union` : **the closure of the union of two biclosed
  sets is biclosed**.
-/

open Equiv Finset

namespace Equiv.Perm

variable {N : ℕ}

/-! ### Biclosed sets of pairs -/

/-- A set `A` of pairs of `Fin N` is *biclosed* if it consists of increasing pairs, and,
for `a < b < c`, it is closed (`(a, b), (b, c) ∈ A` implies `(a, c) ∈ A`) and its
complement is closed (`(a, c) ∈ A` implies `(a, b) ∈ A` or `(b, c) ∈ A`). -/
structure IsBiclosed (A : Finset (Fin N × Fin N)) : Prop where
  /-- The elements of `A` are increasing pairs. -/
  lt : ∀ p ∈ A, p.1 < p.2
  /-- `A` is closed. -/
  closed : ∀ {a b c : Fin N}, a < b → b < c → (a, b) ∈ A → (b, c) ∈ A → (a, c) ∈ A
  /-- The complement of `A` is closed. -/
  coclosed : ∀ {a b c : Fin N}, a < b → b < c → (a, c) ∈ A → (a, b) ∈ A ∨ (b, c) ∈ A

/-- **The set of inversions of a permutation is biclosed.** -/
theorem isBiclosed_invSet (σ : Equiv.Perm (Fin N)) : IsBiclosed (invSet σ) where
  lt p hp := by
    simp only [invSet, Finset.mem_filter] at hp
    exact hp.2.1
  closed {a b c} hab hbc hAab hAbc := by
    simp only [invSet, Finset.mem_filter, Finset.mem_univ, true_and] at hAab hAbc ⊢
    exact ⟨hab.trans hbc, hAbc.2.trans hAab.2⟩
  coclosed {a b c} hab hbc hAac := by
    simp only [invSet, Finset.mem_filter, Finset.mem_univ, true_and] at hAac ⊢
    rcases lt_or_gt_of_ne (fun h : σ b = σ a => absurd (σ.injective h) hab.ne') with h | h
    · exact Or.inl ⟨hab, h⟩
    · exact Or.inr ⟨hbc, hAac.2.trans h⟩

/-! ### The linear order attached to a biclosed set -/

/-- The relation "`x` comes before `y`" attached to a set of pairs `A`: for `x < y` this
means that the pair `(x, y)` is not inverted, that is not in `A`, and for `y < x` that the
pair `(y, x)` is inverted. -/
def Before (A : Finset (Fin N × Fin N)) (x y : Fin N) : Prop :=
  (x < y ∧ (x, y) ∉ A) ∨ (y < x ∧ (y, x) ∈ A)

instance (A : Finset (Fin N × Fin N)) (x y : Fin N) : Decidable (Before A x y) :=
  inferInstanceAs (Decidable ((x < y ∧ (x, y) ∉ A) ∨ (y < x ∧ (y, x) ∈ A)))

variable {A : Finset (Fin N × Fin N)}

lemma ne_of_before {x y : Fin N} (h : Before A x y) : x ≠ y := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> exact fun he => absurd (he ▸ h) (lt_irrefl _)

lemma before_irrefl (x : Fin N) : ¬ Before A x x := fun h => ne_of_before h rfl

lemma before_or_before {x y : Fin N} (hxy : x ≠ y) : Before A x y ∨ Before A y x := by
  rcases lt_or_gt_of_ne hxy with h | h
  · by_cases hA : (x, y) ∈ A
    · exact Or.inr (Or.inr ⟨h, hA⟩)
    · exact Or.inl (Or.inl ⟨h, hA⟩)
  · by_cases hA : (y, x) ∈ A
    · exact Or.inl (Or.inr ⟨h, hA⟩)
    · exact Or.inr (Or.inl ⟨h, hA⟩)

lemma not_before_of_before {x y : Fin N} (h : Before A x y) : ¬ Before A y x := by
  rcases h with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact absurd h1 (asymm h3)
  · exact h4 h2
  · exact h2 h4
  · exact absurd h1 (asymm h3)

/-- The relation `Before A` is transitive when `A` is biclosed. -/
lemma before_trans (hA : IsBiclosed A) {x y z : Fin N} (hxy : Before A x y)
    (hyz : Before A y z) : Before A x z := by
  have hxz : x ≠ z := by
    rintro rfl
    exact not_before_of_before hxy hyz
  rcases hxy with ⟨hxy, hAxy⟩ | ⟨hyx, hAyx⟩
  · rcases hyz with ⟨hyz, hAyz⟩ | ⟨hzy, hAzy⟩
    · refine Or.inl ⟨hxy.trans hyz, fun hAxz => ?_⟩
      rcases hA.coclosed hxy hyz hAxz with h | h
      · exact hAxy h
      · exact hAyz h
    · rcases lt_or_gt_of_ne hxz with h | h
      · exact Or.inl ⟨h, fun hAxz => hAxy (hA.closed h hzy hAxz hAzy)⟩
      · refine Or.inr ⟨h, ?_⟩
        rcases hA.coclosed h hxy hAzy with h' | h'
        · exact h'
        · exact absurd h' hAxy
  · rcases hyz with ⟨hyz, hAyz⟩ | ⟨hzy, hAzy⟩
    · rcases lt_or_gt_of_ne hxz with h | h
      · exact Or.inl ⟨h, fun hAxz => hAyz (hA.closed hyx h hAyx hAxz)⟩
      · refine Or.inr ⟨h, ?_⟩
        rcases hA.coclosed hyz h hAyx with h' | h'
        · exact absurd h' hAyz
        · exact h'
    · exact Or.inr ⟨hzy.trans hyx, hA.closed hzy hyx hAzy hAyx⟩

/-! ### The permutation attached to a biclosed set -/

/-- The rank of `i` for the order `Before A`: the number of letters coming before `i`. -/
def rankOf (A : Finset (Fin N × Fin N)) (i : Fin N) : ℕ :=
  (Finset.univ.filter fun k => Before A k i).card

lemma rankOf_lt (A : Finset (Fin N × Fin N)) (i : Fin N) : rankOf A i < N := by
  have hsub : (Finset.univ.filter fun k => Before A k i) ⊆ Finset.univ.erase i := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact Finset.mem_erase.2 ⟨ne_of_before hk, Finset.mem_univ k⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin] at hcard
  have hN : 0 < N := i.pos
  exact lt_of_le_of_lt hcard (by omega)

lemma rankOf_lt_rankOf (hA : IsBiclosed A) {x y : Fin N} (h : Before A x y) :
    rankOf A x < rankOf A y := by
  refine Finset.card_lt_card ⟨fun k hk => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact before_trans hA hk h
  · have hx : x ∈ Finset.univ.filter fun k => Before A k y := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h
    have hx' := hsub hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx'
    exact before_irrefl x hx'

lemma rankOf_lt_rankOf_iff (hA : IsBiclosed A) {x y : Fin N} :
    rankOf A x < rankOf A y ↔ Before A x y := by
  refine ⟨fun h => ?_, rankOf_lt_rankOf hA⟩
  by_cases hxy : x = y
  · exact absurd (hxy ▸ h) (lt_irrefl _)
  · rcases before_or_before hxy with h' | h'
    · exact h'
    · exact absurd (rankOf_lt_rankOf hA h') (by omega)

/-- The permutation attached to a biclosed set: it sends each letter to its rank for the
order `Before A`. -/
noncomputable def permOfBiclosed (hA : IsBiclosed A) : Equiv.Perm (Fin N) :=
  Equiv.ofBijective (fun i => (⟨rankOf A i, rankOf_lt A i⟩ : Fin N))
    (Finite.injective_iff_bijective.1 fun x y hxy => by
      simp only [Fin.mk.injEq] at hxy
      by_contra hne
      rcases before_or_before hne with h | h <;>
        exact absurd (rankOf_lt_rankOf hA h) (by omega))

lemma permOfBiclosed_apply (hA : IsBiclosed A) (i : Fin N) :
    (permOfBiclosed hA i : ℕ) = rankOf A i := rfl

/-- **The inversion set of the permutation attached to a biclosed set is that set.** -/
theorem invSet_permOfBiclosed (hA : IsBiclosed A) : invSet (permOfBiclosed hA) = A := by
  ext p
  obtain ⟨i, j⟩ := p
  simp only [invSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hij, hlt⟩
    have hr : rankOf A j < rankOf A i := by
      simpa only [Fin.lt_def, permOfBiclosed_apply] using hlt
    rcases (rankOf_lt_rankOf_iff hA).1 hr with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd hij (asymm h1)
    · exact h2
  · intro hmem
    have hij : i < j := hA.lt _ hmem
    refine ⟨hij, ?_⟩
    have hb : Before A j i := Or.inr ⟨hij, hmem⟩
    simpa only [Fin.lt_def, permOfBiclosed_apply] using rankOf_lt_rankOf hA hb

/-- **A set of pairs is biclosed if and only if it is the inversion set of a
permutation.** -/
theorem isBiclosed_iff_exists_invSet {A : Finset (Fin N × Fin N)} :
    IsBiclosed A ↔ ∃ σ : Equiv.Perm (Fin N), invSet σ = A :=
  ⟨fun hA => ⟨permOfBiclosed hA, invSet_permOfBiclosed hA⟩,
    fun ⟨_, hσ⟩ => hσ ▸ isBiclosed_invSet _⟩

/-! ### The closure of a union of two biclosed sets -/

open scoped Classical in
/-- The transitive closure of a set of pairs. -/
noncomputable def closurePairs (A : Finset (Fin N × Fin N)) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun p => Relation.TransGen (fun x y => (x, y) ∈ A) p.1 p.2

lemma mem_closurePairs {A : Finset (Fin N × Fin N)} {p : Fin N × Fin N} :
    p ∈ closurePairs A ↔ Relation.TransGen (fun x y => (x, y) ∈ A) p.1 p.2 := by
  classical
  simp [closurePairs]

lemma subset_closurePairs (A : Finset (Fin N × Fin N)) : A ⊆ closurePairs A := fun _ hp =>
  mem_closurePairs.2 (Relation.TransGen.single hp)

lemma closurePairs_trans {A : Finset (Fin N × Fin N)} {a b c : Fin N}
    (hab : (a, b) ∈ closurePairs A) (hbc : (b, c) ∈ closurePairs A) :
    (a, c) ∈ closurePairs A :=
  mem_closurePairs.2 ((mem_closurePairs.1 hab).trans (mem_closurePairs.1 hbc))

/-- If all pairs of `A` are increasing then so are all pairs of its closure. -/
lemma lt_of_mem_closurePairs {A : Finset (Fin N × Fin N)} (hA : ∀ p ∈ A, p.1 < p.2)
    {a b : Fin N} (hp : (a, b) ∈ closurePairs A) : a < b := by
  have h : Relation.TransGen (fun x y => (x, y) ∈ A) a b := mem_closurePairs.1 hp
  clear hp
  induction h with
  | single h => exact hA _ h
  | tail _ h ih => exact ih.trans (hA _ h)

/-- The closure of a set of pairs is contained in every closed set containing it. -/
lemma closurePairs_subset {A B : Finset (Fin N × Fin N)} (hAB : A ⊆ B)
    (hB : ∀ {a b c : Fin N}, (a, b) ∈ B → (b, c) ∈ B → (a, c) ∈ B)
    {a b : Fin N} (hp : (a, b) ∈ closurePairs A) : (a, b) ∈ B := by
  have h : Relation.TransGen (fun x y => (x, y) ∈ A) a b := mem_closurePairs.1 hp
  clear hp
  induction h with
  | single h => exact hAB h
  | tail _ h ih => exact hB ih (hAB h)

/-- In the union of two biclosed sets, all pairs are increasing. -/
lemma lt_of_mem_union {A B : Finset (Fin N × Fin N)} (hA : IsBiclosed A) (hB : IsBiclosed B) :
    ∀ p ∈ A ∪ B, p.1 < p.2 := by
  intro p hp
  rcases Finset.mem_union.1 hp with h | h
  · exact hA.lt p h
  · exact hB.lt p h

/-- **The transitive closure of the union of two biclosed sets is biclosed.** -/
theorem isBiclosed_closurePairs_union {A B : Finset (Fin N × Fin N)} (hA : IsBiclosed A)
    (hB : IsBiclosed B) : IsBiclosed (closurePairs (A ∪ B)) where
  lt := by
    rintro ⟨a, b⟩ hp
    exact lt_of_mem_closurePairs (lt_of_mem_union hA hB) hp
  closed _ _ hab hbc := closurePairs_trans hab hbc
  coclosed := by
    -- an induction on the length of a chain from `a` to `c`
    intro a b c hab hbc hac
    have hgen : Relation.TransGen (fun x y => (x, y) ∈ A ∪ B) a c := mem_closurePairs.1 hac
    clear hac
    revert b
    induction hgen with
    | single h =>
      intro b hab hbc
      rcases Finset.mem_union.1 h with h | h
      · rcases hA.coclosed hab hbc h with h' | h'
        · exact Or.inl (subset_closurePairs _ (Finset.mem_union_left _ h'))
        · exact Or.inr (subset_closurePairs _ (Finset.mem_union_left _ h'))
      · rcases hB.coclosed hab hbc h with h' | h'
        · exact Or.inl (subset_closurePairs _ (Finset.mem_union_right _ h'))
        · exact Or.inr (subset_closurePairs _ (Finset.mem_union_right _ h'))
    | @tail x c hax hxc ih =>
      intro b hab hbc
      have hxcmem : (x, c) ∈ closurePairs (A ∪ B) := subset_closurePairs _ hxc
      have haxmem : (a, x) ∈ closurePairs (A ∪ B) := mem_closurePairs.2 hax
      rcases lt_trichotomy b x with hbx | rfl | hxb
      · rcases ih hab hbx with h | h
        · exact Or.inl h
        · exact Or.inr (closurePairs_trans h hxcmem)
      · exact Or.inl haxmem
      · rcases Finset.mem_union.1 hxc with h | h
        · rcases hA.coclosed hxb hbc h with h' | h'
          · exact Or.inl (closurePairs_trans haxmem
              (subset_closurePairs _ (Finset.mem_union_left _ h')))
          · exact Or.inr (subset_closurePairs _ (Finset.mem_union_left _ h'))
        · rcases hB.coclosed hxb hbc h with h' | h'
          · exact Or.inl (closurePairs_trans haxmem
              (subset_closurePairs _ (Finset.mem_union_right _ h')))
          · exact Or.inr (subset_closurePairs _ (Finset.mem_union_right _ h'))

end Equiv.Perm
