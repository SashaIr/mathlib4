/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Shape.HorizontalStrip
import Mathlib.Combinatorics.Young.Shape.MinMax

/-!
# The diamond identity for horizontal strips

Given two partitions `rho` and `tau`, consider

* the shapes `lam` of a given size containing both `rho` and `tau` by horizontal strips
  (`List.upDiamond`), and
* the shapes `sigma` contained in both `rho` and `tau` by horizontal strips, of size at
  least `|tau| - r` (`List.downDiamondLe`).

The main result `List.card_upDiamond_eq_card_downDiamondLe` is that, for `|lam| = |rho| + r`,
these two sets have the same cardinality.  This is the combinatorial heart of the Pieri
rule: it is exactly what makes the induction on the number of variables work.

The proof runs through the reflection of the box of the interpolating shapes already used
for `List.card_midSet_symm`: the shapes `sigma` below both `rho` and `tau` are the shapes
interpolating between `partMax rho.tail tau.tail` and `partMin rho tau`, while the shapes
`lam` above both are obtained from those by adding a first part.

## Main definitions

* `List.upDiamond rho tau N` : the partitions of `N` containing `rho` and `tau` by
  horizontal strips.
* `List.downDiamondLe rho tau r` : the partitions contained in `rho` and in `tau` by
  horizontal strips, of size at least `|tau| - r`.

## Main results

* `List.card_upDiamond_eq_card_downDiamondLe` : the diamond identity.
-/

namespace List

open List

/-! ### Two small list lemmas -/

lemma getD_tail (l : List ℕ) (i : ℕ) : l.tail.getD i 0 = l.getD (i + 1) 0 := by
  cases l <;> simp

lemma sum_tail_add_getD_zero (l : List ℕ) : l.tail.sum + l.getD 0 0 = l.sum := by
  cases l with
  | nil => simp
  | cons a s => simp [List.sum_cons]; omega

/-! ### The two sides of the diamond -/

/-- The partitions of `N` obtained from both `rho` and `tau` by adding a horizontal
strip. -/
def upDiamond (rho tau : List ℕ) (N : ℕ) : Set (List ℕ) :=
  {lam | IsPart lam ∧ HorizStrip lam rho ∧ HorizStrip lam tau ∧ lam.sum = N}

/-- The partitions obtained from both `rho` and `tau` by removing a horizontal strip, whose
size is at least `|tau| - r`. -/
def downDiamondLe (rho tau : List ℕ) (r : ℕ) : Set (List ℕ) :=
  {sigma | IsPart sigma ∧ HorizStrip rho sigma ∧ HorizStrip tau sigma ∧ tau.sum ≤ sigma.sum + r}

/-! ### The box -/

variable {rho tau : List ℕ}

/-- The upper bounds of the box: the componentwise minimum of `rho` and `tau`. -/
def diamMax (rho tau : List ℕ) : List ℕ := partMin rho tau

/-- The lower bounds of the box: the componentwise maximum of the tails. -/
def diamMin (rho tau : List ℕ) : List ℕ := partMax rho.tail tau.tail

lemma getD_diamMax (rho tau : List ℕ) (i : ℕ) :
    (diamMax rho tau).getD i 0 = min (rho.getD i 0) (tau.getD i 0) := getD_partMin rho tau i

lemma getD_diamMin (rho tau : List ℕ) (i : ℕ) :
    (diamMin rho tau).getD i 0 = max (rho.getD (i + 1) 0) (tau.getD (i + 1) 0) := by
  rw [diamMin, getD_partMax, getD_tail, getD_tail]

lemma isPart_diamMax (hrho : IsPart rho) (htau : IsPart tau) : IsPart (diamMax rho tau) :=
  isPart_partMin hrho htau

lemma isPart_diamMin (hrho : IsPart rho) (htau : IsPart tau) : IsPart (diamMin rho tau) :=
  isPart_partMax hrho.tail htau.tail

lemma loBd_diamond (rho tau : List ℕ) (i : ℕ) :
    loBd (diamMax rho tau) (diamMin rho tau) i = (diamMin rho tau).getD i 0 := by
  rw [loBd, getD_diamMin, getD_diamMax]
  omega

lemma hiBd_diamond (rho tau : List ℕ) (i : ℕ) :
    hiBd (diamMax rho tau) (diamMin rho tau) i = (diamMax rho tau).getD i 0 := by
  cases i with
  | zero => rfl
  | succ j =>
      rw [hiBd_succ, getD_diamMin, getD_diamMax]
      omega

/-- A shape lies below both `rho` and `tau` by horizontal strips exactly when its parts lie
in the box. -/
lemma horizStrip_both_iff {sigma : List ℕ} (hsigma : IsPart sigma) :
    (HorizStrip rho sigma ∧ HorizStrip tau sigma) ↔
      ∀ i, (diamMin rho tau).getD i 0 ≤ sigma.getD i 0 ∧
        sigma.getD i 0 ≤ (diamMax rho tau).getD i 0 := by
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ i
    have e1 := h1.getD_le i
    have e2 := h2 i
    have e3 := h3.getD_le i
    have e4 := h4 i
    rw [getD_diamMin, getD_diamMax]
    omega
  · intro h
    have hle : ∀ i, sigma.getD i 0 ≤ min (rho.getD i 0) (tau.getD i 0) := by
      intro i; have := (h i).2; rwa [getD_diamMax] at this
    have hge : ∀ i, max (rho.getD (i + 1) 0) (tau.getD (i + 1) 0) ≤ sigma.getD i 0 := by
      intro i; have := (h i).1; rwa [getD_diamMin] at this
    refine ⟨⟨hsigma.included_iff_getD.2 fun i => le_trans (hle i) (min_le_left _ _),
        fun i => le_trans (le_max_left _ _) (hge i)⟩,
      ⟨hsigma.included_iff_getD.2 fun i => le_trans (hle i) (min_le_right _ _),
        fun i => le_trans (le_max_right _ _) (hge i)⟩⟩

/-- The shapes below both `rho` and `tau` are exactly the shapes interpolating between the
two bounds of the box. -/
lemma midSet_diamond (hrho : IsPart rho) (htau : IsPart tau) (s : ℕ) :
    midSet (diamMax rho tau) (diamMin rho tau) s
      = {sigma | IsPart sigma ∧ HorizStrip rho sigma ∧ HorizStrip tau sigma ∧ sigma.sum = s} := by
  ext sigma
  rw [mem_midSet_iff (isPart_diamMin hrho htau)]
  simp only [Set.mem_setOf_eq, loBd_diamond, hiBd_diamond]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, ((horizStrip_both_iff h1).2 h2).1, ((horizStrip_both_iff h1).2 h2).2, h3⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, (horizStrip_both_iff h1).1 ⟨h2, h3⟩, h4⟩

/-! ### Sums -/

/-- The first part of the componentwise maximum. -/
def diamHead (rho tau : List ℕ) : ℕ := max (rho.getD 0 0) (tau.getD 0 0)

lemma sum_diamond (rho tau : List ℕ) :
    (diamMax rho tau).sum + (diamMin rho tau).sum + diamHead rho tau = rho.sum + tau.sum := by
  have hkey := sum_partMin_add_sum_partMax rho tau
  by_cases h : rho = [] ∧ tau = []
  · obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    simp [diamMax, diamMin, diamHead]
  · have hne : rho ≠ [] ∨ tau ≠ [] := by tauto
    have hcons := partMax_eq_cons_tail rho tau hne
    rw [diamMax, diamMin, diamHead, ← hkey, hcons, List.sum_cons]
    omega

/-! ### The degenerate case: the box is empty -/

lemma upDiamond_eq_empty_of_not_included (hrho : IsPart rho) (htau : IsPart tau)
    (h : ¬ Included (diamMin rho tau) (diamMax rho tau)) (N : ℕ) :
    upDiamond rho tau N = ∅ := by
  ext lam
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hpart, hs1, hs2, -⟩
  refine h ((isPart_diamMin hrho htau).included_iff_getD.2 fun i => ?_)
  have e1 := hs1.included.getD_le (i + 1)
  have e2 := hs2.included.getD_le (i + 1)
  have e3 := hs1.getD_succ_le i
  have e4 := hs2.getD_succ_le i
  rw [getD_diamMin, getD_diamMax]
  omega

lemma downDiamondLe_eq_empty_of_not_included (hrho : IsPart rho) (htau : IsPart tau)
    (h : ¬ Included (diamMin rho tau) (diamMax rho tau)) (r : ℕ) :
    downDiamondLe rho tau r = ∅ := by
  ext sigma
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hpart, hs1, hs2, -⟩
  refine h ((isPart_diamMin hrho htau).included_iff_getD.2 fun i => ?_)
  have hbox := (horizStrip_both_iff (rho := rho) (tau := tau) hpart).1 ⟨hs1, hs2⟩
  exact le_trans (hbox i).1 (hbox i).2

/-! ### The degenerate case: both shapes are empty -/

lemma upDiamond_nil_nil (N : ℕ) :
    upDiamond [] [] N = {if N = 0 then [] else [N]} := by
  ext lam
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hpart, hs1, -, hsum⟩
    have hlen : lam.length ≤ 1 := by
      by_contra hlen
      have h1 : 0 < lam.getD 1 0 := hpart.getD_pos (by omega)
      have h2 : lam.getD 1 0 ≤ 0 := hs1.getD_succ_le 0
      omega
    match lam, hlen with
    | [], _ => simp only [List.sum_nil] at hsum; simp [← hsum]
    | [a], _ =>
        simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hsum
        subst hsum
        have ha : 0 < a := hpart.headD_pos (by simp)
        rw [if_neg (by omega)]
  · intro hlam
    subst hlam
    by_cases hN : N = 0
    · subst hN
      exact ⟨isPart_nil, ⟨Included.refl _, fun i => by simp⟩, ⟨Included.refl _, fun i => by simp⟩,
        rfl⟩
    · rw [if_neg hN]
      refine ⟨⟨by simpa using Nat.one_le_iff_ne_zero.2 hN, isPart_nil⟩,
        ⟨included_nil _, fun i => ?_⟩, ⟨included_nil _, fun i => ?_⟩, by simp⟩
      · simp
      · simp

lemma downDiamondLe_nil_nil (r : ℕ) : downDiamondLe [] [] r = {[]} := by
  ext sigma
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, hs1, -, -⟩
    cases sigma with
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

lemma tail_mem_midSet_diamond (hrho : IsPart rho) (htau : IsPart tau) {lam : List ℕ} {N : ℕ}
    (hlam : lam ∈ upDiamond rho tau N) :
    lam.tail ∈ midSet (diamMax rho tau) (diamMin rho tau) (N - lam.getD 0 0) := by
  obtain ⟨hpart, hs1, hs2, hsum⟩ := hlam
  have htailsum : lam.tail.sum = N - lam.getD 0 0 := by
    have := sum_tail_add_getD_zero lam
    omega
  rw [midSet_diamond hrho htau]
  refine ⟨hpart.tail, ⟨(hpart.tail.included_iff_getD).2 fun i => ?_, fun i => ?_⟩,
    ⟨(hpart.tail.included_iff_getD).2 fun i => ?_, fun i => ?_⟩, htailsum⟩
  · rw [getD_tail]; exact hs1.getD_succ_le i
  · rw [getD_tail]; exact hs1.included.getD_le (i + 1)
  · rw [getD_tail]; exact hs2.getD_succ_le i
  · rw [getD_tail]; exact hs2.included.getD_le (i + 1)

lemma diamHead_le_getD_zero {lam : List ℕ} {N : ℕ} (hlam : lam ∈ upDiamond rho tau N) :
    diamHead rho tau ≤ lam.getD 0 0 := by
  obtain ⟨-, hs1, hs2, -⟩ := hlam
  have e1 := hs1.included.getD_le 0
  have e2 := hs2.included.getD_le 0
  rw [diamHead]
  omega

/-! ### The diamond identity -/

/-- **The diamond identity**: the partitions of `|rho| + r` obtained from both `rho` and
`tau` by adding a horizontal strip are as many as the partitions of size at least
`|tau| - r` obtained from both `rho` and `tau` by removing a horizontal strip. -/
theorem card_upDiamond_eq_card_downDiamondLe (hrho : IsPart rho) (htau : IsPart tau) (r : ℕ) :
    Nat.card (upDiamond rho tau (rho.sum + r)) = Nat.card (downDiamondLe rho tau r) := by
  classical
  by_cases hsub : Included (diamMin rho tau) (diamMax rho tau)
  swap
  · rw [upDiamond_eq_empty_of_not_included hrho htau hsub,
      downDiamondLe_eq_empty_of_not_included hrho htau hsub]
  by_cases hnil : rho = [] ∧ tau = []
  · obtain ⟨h1, h2⟩ := hnil
    subst h1; subst h2
    rw [upDiamond_nil_nil, downDiamondLe_nil_nil]
    simp
  -- the main case
  have hBpart : IsPart (diamMin rho tau) := isPart_diamMin hrho htau
  have hS : (diamMax rho tau).sum + (diamMin rho tau).sum + diamHead rho tau
      = rho.sum + tau.sum := sum_diamond rho tau
  have hcpos : 0 < diamHead rho tau := by
    rcases (not_and_or.1 hnil) with h | h
    · have h1 := hrho.headD_pos h
      have h0 : rho.getD 0 0 = rho.headD 0 := by cases rho <;> simp
      rw [diamHead]
      omega
    · have h1 := htau.headD_pos h
      have h0 : tau.getD 0 0 = tau.headD 0 := by cases tau <;> simp
      rw [diamHead]
      omega
  have hA0 : (diamMax rho tau).getD 0 0 ≤ diamHead rho tau := by
    rw [getD_diamMax, diamHead]
    omega
  have hrho0 : rho.getD 0 0 ≤ diamHead rho tau := by rw [diamHead]; omega
  have htau0 : tau.getD 0 0 ≤ diamHead rho tau := by rw [diamHead]; omega
  -- the image of the map is in the right set
  have hmem : ∀ lam ∈ upDiamond rho tau (rho.sum + r),
      pieriFlip (diamMax rho tau) (diamMin rho tau) lam.tail ∈ downDiamondLe rho tau r := by
    intro lam hlam
    have hmid := tail_mem_midSet_diamond hrho htau hlam
    have hle : lam.tail.sum ≤ (diamMax rho tau).sum := hmid.2.1.sum_le
    have hch := diamHead_le_getD_zero hlam
    have hflip := pieriFlip_mem hBpart hsub hmid
    rw [midSet_diamond hrho htau] at hflip
    obtain ⟨hp, hf1, hf2, hfsum⟩ := hflip
    refine ⟨hp, hf1, hf2, ?_⟩
    obtain ⟨-, -, -, hsum⟩ := hlam
    have htails := sum_tail_add_getD_zero lam
    omega
  refine Nat.card_congr (Equiv.ofBijective
    (fun lam : upDiamond rho tau (rho.sum + r) =>
      (⟨pieriFlip (diamMax rho tau) (diamMin rho tau) lam.1.tail, hmem lam.1 lam.2⟩ :
        downDiamondLe rho tau r)) ⟨?_, ?_⟩)
  · -- injectivity
    rintro ⟨lam, hlam⟩ ⟨lam', hlam'⟩ heq
    have h1 : pieriFlip (diamMax rho tau) (diamMin rho tau) lam.tail
        = pieriFlip (diamMax rho tau) (diamMin rho tau) lam'.tail := congrArg Subtype.val heq
    have e1 := pieriFlip_pieriFlip hBpart hsub (tail_mem_midSet_diamond hrho htau hlam)
    have e2 := pieriFlip_pieriFlip hBpart hsub (tail_mem_midSet_diamond hrho htau hlam')
    rw [h1, e2] at e1
    have hs : lam.sum = lam'.sum := by rw [hlam.2.2.2, hlam'.2.2.2]
    exact Subtype.ext (eq_of_tail_eq_of_sum_eq hlam.1 hlam'.1 e1.symm hs)
  · -- surjectivity
    rintro ⟨sigma, hsigma⟩
    obtain ⟨hsp, hs1, hs2, hcond⟩ := hsigma
    have hmid : sigma ∈ midSet (diamMax rho tau) (diamMin rho tau) sigma.sum := by
      rw [midSet_diamond hrho htau]
      exact ⟨hsp, hs1, hs2, rfl⟩
    have hsigA : sigma.sum ≤ (diamMax rho tau).sum := hmid.2.1.sum_le
    have hnumem := pieriFlip_mem hBpart hsub hmid
    have hnuA : (pieriFlip (diamMax rho tau) (diamMin rho tau) sigma).sum
        ≤ (diamMax rho tau).sum := hnumem.2.1.sum_le
    have hnud := hnumem
    rw [midSet_diamond hrho htau] at hnud
    obtain ⟨hnup, hnr, hnt, hnsum⟩ := hnud
    set nu := pieriFlip (diamMax rho tau) (diamMin rho tau) sigma with hnudef
    set h := rho.sum + r - nu.sum with hhdef
    have hnuN : nu.sum + diamHead rho tau ≤ rho.sum + r := by omega
    have hhc : diamHead rho tau ≤ h := by omega
    have hnu0 : nu.getD 0 0 ≤ (diamMax rho tau).getD 0 0 := hnumem.2.1.included.getD_le 0
    have hlamPart : IsPart (h :: nu) := by
      refine ⟨?_, hnup⟩
      have key : ∀ l : List ℕ, l = nu → l.headD 1 ≤ h := by
        rintro (_ | ⟨x, t⟩) hcase
        · simp only [List.headD_nil]
          omega
        · have hx : x = nu.getD 0 0 := by rw [← hcase]; rfl
          simp only [List.headD_cons]
          omega
      exact key nu rfl
    have hlamup : (h :: nu) ∈ upDiamond rho tau (rho.sum + r) := by
      refine ⟨hlamPart, ⟨hrho.included_iff_getD.2 fun i => ?_, fun i => ?_⟩,
        ⟨htau.included_iff_getD.2 fun i => ?_, fun i => ?_⟩, ?_⟩
      · cases i with
        | zero => simpa using le_trans hrho0 hhc
        | succ j => simpa using hnr.2 j
      · simpa using hnr.included.getD_le i
      · cases i with
        | zero => simpa using le_trans htau0 hhc
        | succ j => simpa using hnt.2 j
      · simpa using hnt.included.getD_le i
      · simp only [List.sum_cons]
        omega
    exact ⟨⟨h :: nu, hlamup⟩, Subtype.ext (by
      simp only [List.tail_cons]
      exact pieriFlip_pieriFlip hBpart hsub hmid)⟩

end List
