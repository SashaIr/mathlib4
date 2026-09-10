/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.GetD
public import Mathlib.Combinatorics.Young.Shape.HorizontalStrip
public import Mathlib.Combinatorics.Young.Shape.MinMax

/-!
# The diamond identity for horizontal strips

Given two partitions `ρ` and `τ`, consider

* the shapes `η` of a given size containing both `ρ` and `τ` by horizontal strips
  (`Young.upDiamond`), and
* the shapes `σ` contained in both `ρ` and `τ` by horizontal strips, of size at
  least `|τ| - r` (`Young.downDiamondLe`).

The main result `Young.card_upDiamond_eq_card_downDiamondLe` is that, for `|η| = |ρ| + r`,
these two sets have the same cardinality.  This is the combinatorial heart of the Pieri
rule: it is exactly what makes the induction on the number of variables work.

The proof runs through the reflection of the box of the interpolating shapes already used
for `Young.card_midSet_symm`: the shapes `σ` below both `ρ` and `τ` are the shapes
interpolating between `partMax ρ.tail τ.tail` and `partMin ρ τ`, while the shapes
`η` above both are obtained from those by adding a first part.

## Main definitions

* `Young.upDiamond ρ τ N` : the partitions of `N` containing `ρ` and `τ` by
  horizontal strips.
* `Young.downDiamondLe ρ τ r` : the partitions contained in `ρ` and in `τ` by
  horizontal strips, of size at least `|τ| - r`.

## Main results

* `Young.card_upDiamond_eq_card_downDiamondLe` : the diamond identity.
-/

@[expose] public section

namespace Young

open List

/-! ### A small list lemma -/

/-! ### The two sides of the diamond -/

/-- The partitions of `N` obtained from both `ρ` and `τ` by adding a horizontal
strip. -/
def upDiamond (ρ τ : List ℕ) (N : ℕ) : Set (List ℕ) :=
  {η | IsPart η ∧ HorizStrip η ρ ∧ HorizStrip η τ ∧ η.sum = N}

/-- The partitions obtained from both `ρ` and `τ` by removing a horizontal strip, whose
size is at least `|τ| - r`. -/
def downDiamondLe (ρ τ : List ℕ) (r : ℕ) : Set (List ℕ) :=
  {σ | IsPart σ ∧ HorizStrip ρ σ ∧ HorizStrip τ σ ∧ τ.sum ≤ σ.sum + r}

/-! ### The box -/

variable {ρ τ : List ℕ}

/-- The upper bounds of the box: the componentwise minimum of `ρ` and `τ`. -/
def diamMax (ρ τ : List ℕ) : List ℕ := partMin ρ τ

/-- The lower bounds of the box: the componentwise maximum of the tails. -/
def diamMin (ρ τ : List ℕ) : List ℕ := partMax ρ.tail τ.tail

lemma getD_diamMax (ρ τ : List ℕ) (i : ℕ) :
    (diamMax ρ τ).getD i 0 = min (ρ.getD i 0) (τ.getD i 0) := getD_partMin ρ τ i

lemma getD_diamMin (ρ τ : List ℕ) (i : ℕ) :
    (diamMin ρ τ).getD i 0 = max (ρ.getD (i + 1) 0) (τ.getD (i + 1) 0) := by
  rw [diamMin, getD_partMax, getD_tail, getD_tail]

lemma isPart_diamMax (hρ : IsPart ρ) (hτ : IsPart τ) : IsPart (diamMax ρ τ) :=
  isPart_partMin hρ hτ

lemma isPart_diamMin (hρ : IsPart ρ) (hτ : IsPart τ) : IsPart (diamMin ρ τ) :=
  isPart_partMax hρ.tail hτ.tail

lemma loBd_diamond (ρ τ : List ℕ) (i : ℕ) :
    loBd (diamMax ρ τ) (diamMin ρ τ) i = (diamMin ρ τ).getD i 0 := by
  rw [loBd, getD_diamMin, getD_diamMax]
  omega

lemma hiBd_diamond (ρ τ : List ℕ) (i : ℕ) :
    hiBd (diamMax ρ τ) (diamMin ρ τ) i = (diamMax ρ τ).getD i 0 := by
  cases i with
  | zero => rfl
  | succ j =>
      rw [hiBd_succ, getD_diamMin, getD_diamMax]
      omega

/-- A shape lies below both `ρ` and `τ` by horizontal strips exactly when its parts lie
in the box. -/
lemma horizStrip_both_iff {σ : List ℕ} (hσ : IsPart σ) :
    (HorizStrip ρ σ ∧ HorizStrip τ σ) ↔
      ∀ i, (diamMin ρ τ).getD i 0 ≤ σ.getD i 0 ∧
        σ.getD i 0 ≤ (diamMax ρ τ).getD i 0 := by
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ i
    have e1 := h1.getD_le i
    have e2 := h2 i
    have e3 := h3.getD_le i
    have e4 := h4 i
    rw [getD_diamMin, getD_diamMax]
    omega
  · intro h
    have hle : ∀ i, σ.getD i 0 ≤ min (ρ.getD i 0) (τ.getD i 0) := by
      intro i; have := (h i).2; rwa [getD_diamMax] at this
    have hge : ∀ i, max (ρ.getD (i + 1) 0) (τ.getD (i + 1) 0) ≤ σ.getD i 0 := by
      intro i; have := (h i).1; rwa [getD_diamMin] at this
    refine ⟨⟨hσ.included_iff_getD.2 fun i => le_trans (hle i) (min_le_left _ _),
        fun i => le_trans (le_max_left _ _) (hge i)⟩,
      ⟨hσ.included_iff_getD.2 fun i => le_trans (hle i) (min_le_right _ _),
        fun i => le_trans (le_max_right _ _) (hge i)⟩⟩

/-- The shapes below both `ρ` and `τ` are exactly the shapes interpolating between the
two bounds of the box. -/
lemma midSet_diamond (hρ : IsPart ρ) (hτ : IsPart τ) (s : ℕ) :
    midSet (diamMax ρ τ) (diamMin ρ τ) s
      = {σ | IsPart σ ∧ HorizStrip ρ σ ∧ HorizStrip τ σ ∧ σ.sum = s} := by
  ext σ
  rw [mem_midSet_iff (isPart_diamMin hρ hτ)]
  simp only [Set.mem_ofPred_eq, loBd_diamond, hiBd_diamond]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, ((horizStrip_both_iff h1).2 h2).1, ((horizStrip_both_iff h1).2 h2).2, h3⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, (horizStrip_both_iff h1).1 ⟨h2, h3⟩, h4⟩

/-! ### Sums -/

/-- The first part of the componentwise maximum. -/
def diamHead (ρ τ : List ℕ) : ℕ := max (ρ.getD 0 0) (τ.getD 0 0)

lemma sum_diamond (ρ τ : List ℕ) :
    (diamMax ρ τ).sum + (diamMin ρ τ).sum + diamHead ρ τ = ρ.sum + τ.sum := by
  have hkey := sum_partMin_add_sum_partMax ρ τ
  by_cases h : ρ = [] ∧ τ = []
  · obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    simp [diamMax, diamMin, diamHead]
  · have hne : ρ ≠ [] ∨ τ ≠ [] := by tauto
    have hcons := partMax_eq_cons_tail ρ τ hne
    rw [diamMax, diamMin, diamHead, ← hkey, hcons, List.sum_cons]
    omega

/-! ### The degenerate case: the box is empty -/

lemma upDiamond_eq_empty_of_not_included (hρ : IsPart ρ) (hτ : IsPart τ)
    (h : ¬ Included (diamMin ρ τ) (diamMax ρ τ)) (N : ℕ) :
    upDiamond ρ τ N = ∅ := by
  ext η
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hpart, hs1, hs2, -⟩
  refine h ((isPart_diamMin hρ hτ).included_iff_getD.2 fun i => ?_)
  have e1 := hs1.included.getD_le (i + 1)
  have e2 := hs2.included.getD_le (i + 1)
  have e3 := hs1.getD_succ_le i
  have e4 := hs2.getD_succ_le i
  rw [getD_diamMin, getD_diamMax]
  omega

lemma downDiamondLe_eq_empty_of_not_included (hρ : IsPart ρ) (hτ : IsPart τ)
    (h : ¬ Included (diamMin ρ τ) (diamMax ρ τ)) (r : ℕ) :
    downDiamondLe ρ τ r = ∅ := by
  ext σ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hpart, hs1, hs2, -⟩
  refine h ((isPart_diamMin hρ hτ).included_iff_getD.2 fun i => ?_)
  have hbox := (horizStrip_both_iff (ρ := ρ) (τ := τ) hpart).1 ⟨hs1, hs2⟩
  exact le_trans (hbox i).1 (hbox i).2

/-! ### The degenerate case: both shapes are empty -/

lemma upDiamond_nil_nil (N : ℕ) :
    upDiamond [] [] N = {if N = 0 then [] else [N]} := by
  ext η
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hpart, hs1, -, hsum⟩
    have hlen : η.length ≤ 1 := by
      by_contra hlen
      have h1 : 0 < η.getD 1 0 := hpart.getD_pos (by omega)
      have h2 : η.getD 1 0 ≤ 0 := hs1.getD_succ_le 0
      omega
    match η, hlen with
    | [], _ => simp only [List.sum_nil] at hsum; simp [← hsum]
    | [a], _ =>
        simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hsum
        subst hsum
        have ha : 0 < a := hpart.headD_pos (by simp)
        rw [ite_eq_right (by omega)]
  · intro hη
    subst hη
    by_cases hN : N = 0
    · subst hN
      exact ⟨isPart_nil, ⟨Included.refl _, fun i => by simp⟩, ⟨Included.refl _, fun i => by simp⟩,
        rfl⟩
    · rw [ite_eq_right hN]
      refine ⟨⟨by simpa using Nat.one_le_iff_ne_zero.2 hN, isPart_nil⟩,
        ⟨included_nil _, fun i => ?_⟩, ⟨included_nil _, fun i => ?_⟩, by simp⟩
      · simp
      · simp

lemma downDiamondLe_nil_nil (r : ℕ) : downDiamondLe [] [] r = {[]} := by
  ext σ
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, hs1, -, -⟩
    cases σ with
    | nil => rfl
    | cons a l => exact absurd hs1.included (included_cons_nil a l)
  · rintro rfl
    exact ⟨isPart_nil, ⟨Included.refl _, fun i => by simp⟩, ⟨Included.refl _, fun i => by simp⟩,
      by simp⟩

/-! ### The tail of a shape above both -/

lemma eq_of_tail_eq_of_sum_eq : ∀ {l l' : List ℕ}, IsPart l → IsPart l' →
    l.tail = l'.tail → l.sum = l'.sum → l = l'
  | [], [], _, _, _, _ => rfl
  | [], a :: l', _, hp', htail, hsum => by
      exfalso
      have hpos := hp'.headD_pos (by simp)
      simp only [List.tail_nil, List.tail_cons] at htail
      subst htail
      simp only [List.sum_nil, List.sum_cons, List.headD_cons] at hsum hpos
      omega
  | a :: l, [], hp, _, htail, hsum => by
      exfalso
      have hpos := hp.headD_pos (by simp)
      simp only [List.tail_nil, List.tail_cons] at htail
      subst htail
      simp only [List.sum_nil, List.sum_cons, List.headD_cons] at hsum hpos
      omega
  | a :: l, a' :: l', _, _, htail, hsum => by
      simp only [List.tail_cons] at htail
      subst htail
      simp only [List.sum_cons] at hsum
      rw [show a = a' by omega]

lemma tail_mem_midSet_diamond (hρ : IsPart ρ) (hτ : IsPart τ) {η : List ℕ} {N : ℕ}
    (hη : η ∈ upDiamond ρ τ N) :
    η.tail ∈ midSet (diamMax ρ τ) (diamMin ρ τ) (N - η.getD 0 0) := by
  obtain ⟨hpart, hs1, hs2, hsum⟩ := hη
  have htailsum : η.tail.sum = N - η.getD 0 0 := by
    have := sum_tail_add_getD_zero η
    omega
  rw [midSet_diamond hρ hτ]
  refine ⟨hpart.tail, ⟨(hpart.tail.included_iff_getD).2 fun i => ?_, fun i => ?_⟩,
    ⟨(hpart.tail.included_iff_getD).2 fun i => ?_, fun i => ?_⟩, htailsum⟩
  · rw [getD_tail]; exact hs1.getD_succ_le i
  · rw [getD_tail]; exact hs1.included.getD_le (i + 1)
  · rw [getD_tail]; exact hs2.getD_succ_le i
  · rw [getD_tail]; exact hs2.included.getD_le (i + 1)

lemma diamHead_le_getD_zero {η : List ℕ} {N : ℕ} (hη : η ∈ upDiamond ρ τ N) :
    diamHead ρ τ ≤ η.getD 0 0 := by
  obtain ⟨-, hs1, hs2, -⟩ := hη
  have e1 := hs1.included.getD_le 0
  have e2 := hs2.included.getD_le 0
  rw [diamHead]
  omega

/-! ### The diamond identity -/

/-- **The diamond identity**: the partitions of `|ρ| + r` obtained from both `ρ` and
`τ` by adding a horizontal strip are as many as the partitions of size at least
`|τ| - r` obtained from both `ρ` and `τ` by removing a horizontal strip. -/
theorem card_upDiamond_eq_card_downDiamondLe (hρ : IsPart ρ) (hτ : IsPart τ) (r : ℕ) :
    Nat.card (upDiamond ρ τ (ρ.sum + r)) = Nat.card (downDiamondLe ρ τ r) := by
  classical
  by_cases hsub : Included (diamMin ρ τ) (diamMax ρ τ)
  swap
  · rw [upDiamond_eq_empty_of_not_included hρ hτ hsub,
      downDiamondLe_eq_empty_of_not_included hρ hτ hsub]
  by_cases hnil : ρ = [] ∧ τ = []
  · obtain ⟨h1, h2⟩ := hnil
    subst h1; subst h2
    rw [upDiamond_nil_nil, downDiamondLe_nil_nil]
    simp
  -- the main case
  have hBpart : IsPart (diamMin ρ τ) := isPart_diamMin hρ hτ
  have hS : (diamMax ρ τ).sum + (diamMin ρ τ).sum + diamHead ρ τ
      = ρ.sum + τ.sum := sum_diamond ρ τ
  have hcpos : 0 < diamHead ρ τ := by
    rcases (not_and_or.1 hnil) with h | h
    · have h1 := hρ.headD_pos h
      have h0 : ρ.getD 0 0 = ρ.headD 0 := by cases ρ <;> simp
      rw [diamHead]
      omega
    · have h1 := hτ.headD_pos h
      have h0 : τ.getD 0 0 = τ.headD 0 := by cases τ <;> simp
      rw [diamHead]
      omega
  have hA0 : (diamMax ρ τ).getD 0 0 ≤ diamHead ρ τ := by
    rw [getD_diamMax, diamHead]
    omega
  have hρ0 : ρ.getD 0 0 ≤ diamHead ρ τ := by rw [diamHead]; omega
  have hτ0 : τ.getD 0 0 ≤ diamHead ρ τ := by rw [diamHead]; omega
  -- the image of the map is in the right set
  have hmem : ∀ η ∈ upDiamond ρ τ (ρ.sum + r),
      pieriFlip (diamMax ρ τ) (diamMin ρ τ) η.tail ∈ downDiamondLe ρ τ r := by
    intro η hη
    have hmid := tail_mem_midSet_diamond hρ hτ hη
    have hle : η.tail.sum ≤ (diamMax ρ τ).sum := hmid.2.1.sum_le
    have hch := diamHead_le_getD_zero hη
    have hflip := pieriFlip_mem hBpart hsub hmid
    rw [midSet_diamond hρ hτ] at hflip
    obtain ⟨hp, hf1, hf2, hfsum⟩ := hflip
    refine ⟨hp, hf1, hf2, ?_⟩
    obtain ⟨-, -, -, hsum⟩ := hη
    have htails := sum_tail_add_getD_zero η
    omega
  refine Nat.card_congr (Equiv.ofBijective
    (fun η : upDiamond ρ τ (ρ.sum + r) =>
      (⟨pieriFlip (diamMax ρ τ) (diamMin ρ τ) η.1.tail, hmem η.1 η.2⟩ :
        downDiamondLe ρ τ r)) ⟨?_, ?_⟩)
  · -- injectivity
    rintro ⟨η, hη⟩ ⟨η', hη'⟩ heq
    have h1 : pieriFlip (diamMax ρ τ) (diamMin ρ τ) η.tail
        = pieriFlip (diamMax ρ τ) (diamMin ρ τ) η'.tail := congrArg Subtype.val heq
    have e1 := pieriFlip_pieriFlip hBpart hsub (tail_mem_midSet_diamond hρ hτ hη)
    have e2 := pieriFlip_pieriFlip hBpart hsub (tail_mem_midSet_diamond hρ hτ hη')
    rw [h1, e2] at e1
    have hs : η.sum = η'.sum := by rw [hη.2.2.2, hη'.2.2.2]
    exact Subtype.ext (eq_of_tail_eq_of_sum_eq hη.1 hη'.1 e1.symm hs)
  · -- surjectivity
    rintro ⟨σ, hσ⟩
    obtain ⟨hsp, hs1, hs2, hcond⟩ := hσ
    have hmid : σ ∈ midSet (diamMax ρ τ) (diamMin ρ τ) σ.sum := by
      rw [midSet_diamond hρ hτ]
      exact ⟨hsp, hs1, hs2, rfl⟩
    have hsigA : σ.sum ≤ (diamMax ρ τ).sum := hmid.2.1.sum_le
    have hνmem := pieriFlip_mem hBpart hsub hmid
    have hνA : (pieriFlip (diamMax ρ τ) (diamMin ρ τ) σ).sum
        ≤ (diamMax ρ τ).sum := hνmem.2.1.sum_le
    have hνd := hνmem
    rw [midSet_diamond hρ hτ] at hνd
    obtain ⟨hνp, hnr, hnt, hnsum⟩ := hνd
    set ν := pieriFlip (diamMax ρ τ) (diamMin ρ τ) σ with hνdef
    set h := ρ.sum + r - ν.sum with hhdef
    have hνN : ν.sum + diamHead ρ τ ≤ ρ.sum + r := by omega
    have hhc : diamHead ρ τ ≤ h := by omega
    have hν0 : ν.getD 0 0 ≤ (diamMax ρ τ).getD 0 0 := hνmem.2.1.included.getD_le 0
    have hηPart : IsPart (h :: ν) := by
      refine ⟨?_, hνp⟩
      have key : ∀ l : List ℕ, l = ν → l.headD 1 ≤ h := by
        rintro (_ | ⟨x, t⟩) hcase
        · simp only [List.headD_nil]
          omega
        · have hx : x = ν.getD 0 0 := by rw [← hcase]; rfl
          simp only [List.headD_cons]
          omega
      exact key ν rfl
    have hηup : (h :: ν) ∈ upDiamond ρ τ (ρ.sum + r) := by
      refine ⟨hηPart, ⟨hρ.included_iff_getD.2 fun i => ?_, fun i => ?_⟩,
        ⟨hτ.included_iff_getD.2 fun i => ?_, fun i => ?_⟩, ?_⟩
      · cases i with
        | zero => simpa using le_trans hρ0 hhc
        | succ j => simpa using hnr.2 j
      · simpa using hnr.included.getD_le i
      · cases i with
        | zero => simpa using le_trans hτ0 hhc
        | succ j => simpa using hnt.2 j
      · simpa using hnt.included.getD_le i
      · simp only [List.sum_cons]
        omega
    exact ⟨⟨h :: ν, hηup⟩, Subtype.ext (by
      simp only [List.tail_cons]
      exact pieriFlip_pieriFlip hBpart hsub hmid)⟩

end Young
