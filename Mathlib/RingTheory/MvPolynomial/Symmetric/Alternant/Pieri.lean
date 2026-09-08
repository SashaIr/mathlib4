/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.Alternant.Basic

/-!
# The Pieri rule for alternants

Following `theories/MPoly/Schur_altdef.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we show that in the expansion

`h_r * alt a = ∑_{|d| = r} alt (a + d)`

of `MvPolynomial.hsymm_mul_alt`, only the exponent vectors `a + d` obtained from `a` by adding a
*horizontal strip* contribute: all the other terms cancel in pairs, by the sign-reversing
involution exchanging two adjacent entries.

## Main definitions and results

* `MvPolynomial.IsAltStrip a c` : `c` is obtained from the strictly decreasing vector `a` by
  adding a horizontal strip, i.e. `a i ≤ c i` for all `i` and `c (i+1) < a i`.
* `MvPolynomial.isAltStrip_of_forall_not_free` : if no adjacent pair of `a` is "free" for `c`,
  then `c` is a horizontal strip above `a`.
* `MvPolynomial.hsymm_mul_alt_strip` : the Pieri rule for alternants.
-/

namespace MvPolynomial

open List MvPolynomial Finset

variable {m : ℕ} {R : Type*} [CommRing R]

/-! ### Horizontal strips of exponent vectors -/

/-- The vector `c` is obtained from `a` by adding a horizontal strip: `c` dominates `a`
entrywise, and the entry of `c` following the position `i` is smaller than `a i`. -/
def IsAltStrip (a c : Fin m → ℕ) : Prop :=
  (∀ i, a i ≤ c i) ∧ ∀ i j : Fin m, (j : ℕ) = (i : ℕ) + 1 → c j < a i

/-- The pair of adjacent positions `(i, j)` is *free* for `c` when no entry of `c` lies in
the interval `[a j, a i)`. -/
def FreeAt (a c : Fin m → ℕ) (i j : Fin m) : Prop := ∀ k, ¬ (a j ≤ c k ∧ c k < a i)

/-- The positions where `c` is at least `a i`. -/
def geSet (a c : Fin m → ℕ) (i : Fin m) : Finset (Fin m) :=
  univ.filter (fun k => a i ≤ c k)

@[simp] lemma mem_geSet {a c : Fin m → ℕ} {i k : Fin m} :
    k ∈ geSet a c i ↔ a i ≤ c k := by simp [geSet]

lemma geSet_subset_geSet {a c : Fin m → ℕ} (ha : Antitone a) {i j : Fin m} (hij : i ≤ j) :
    geSet a c i ⊆ geSet a c j := by
  intro k hk
  rw [mem_geSet] at hk ⊢
  exact le_trans (ha hij) hk

lemma le_mem_geSet {a c : Fin m → ℕ} (ha : Antitone a) (hac : ∀ i, a i ≤ c i) {i k : Fin m}
    (hki : k ≤ i) : k ∈ geSet a c i := by
  rw [mem_geSet]
  exact le_trans (ha hki) (hac k)

/-- If no adjacent pair is free, then the positions where `c` is at least `a i` are
exactly the positions `≤ i`. -/
lemma geSet_eq_of_forall_not_free {a c : Fin m → ℕ} (ha : Antitone a) (hac : ∀ i, a i ≤ c i)
    (hnofree : ∀ i j : Fin m, (j : ℕ) = (i : ℕ) + 1 → ¬ FreeAt a c i j) (i : Fin m) :
    geSet a c i = univ.filter (fun k => k ≤ i) := by
  suffices H : ∀ t : ℕ, ∀ i : Fin m, (i : ℕ) + t + 1 = m →
      geSet a c i = univ.filter (fun k => k ≤ i) by
    exact H (m - 1 - (i : ℕ)) i (by omega)
  intro t
  induction t with
  | zero =>
    intro i hi
    ext k
    simp only [mem_geSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun _ => ?_, fun hk => ?_⟩
    · have := k.isLt
      exact Fin.le_def.2 (by omega)
    · simpa using le_mem_geSet ha hac hk
  | succ t ih =>
    intro i hi
    have hjlt : (i : ℕ) + 1 < m := by omega
    set j : Fin m := ⟨(i : ℕ) + 1, hjlt⟩ with hjdef
    have hij : i ≤ j := Fin.le_def.2 (by simp [hjdef])
    have hjval : (j : ℕ) = (i : ℕ) + 1 := rfl
    have hgj : geSet a c j = univ.filter (fun k => k ≤ j) := ih j (by simp [hjdef]; omega)
    obtain ⟨k, hk1, hk2⟩ : ∃ k, a j ≤ c k ∧ c k < a i := by
      by_contra hcon
      exact hnofree i j hjval (fun k hk => hcon ⟨k, hk⟩)
    have hkj : k ∈ geSet a c j := mem_geSet.2 hk1
    have hki : k ∉ geSet a c i := by
      rw [mem_geSet]
      omega
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun hx => ?_, fun hx => by simpa using le_mem_geSet ha hac hx⟩
    by_contra hxi
    have hxj : x ≤ j := by
      have : x ∈ geSet a c j := geSet_subset_geSet ha hij hx
      rw [hgj] at this
      simpa using this
    have hxeq : x = j := by
      rw [Fin.le_def] at hxj
      rw [Fin.le_def] at hxi
      exact Fin.ext (by omega)
    subst hxeq
    have hsub : geSet a c j ⊆ geSet a c i := by
      intro y hy
      rw [hgj] at hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      rcases eq_or_lt_of_le hy with rfl | hlt
      · exact hx
      · refine le_mem_geSet ha hac ?_
        have h1 : (y : ℕ) < (j : ℕ) := Fin.lt_def.1 hlt
        exact Fin.le_def.2 (by omega)
    exact hki (hsub hkj)

/-- If no adjacent pair is free, then `c` is a horizontal strip above `a`. -/
theorem isAltStrip_of_forall_not_free {a c : Fin m → ℕ} (ha : Antitone a)
    (hac : ∀ i, a i ≤ c i)
    (hnofree : ∀ i j : Fin m, (j : ℕ) = (i : ℕ) + 1 → ¬ FreeAt a c i j) :
    IsAltStrip a c := by
  refine ⟨hac, fun i j hj => ?_⟩
  have hji : ¬ (j ≤ i) := by
    rw [Fin.le_def, hj]
    omega
  have : j ∉ geSet a c i := by
    rw [geSet_eq_of_forall_not_free ha hac hnofree i]
    simpa using hji
  rw [mem_geSet] at this
  omega

/-- A horizontal strip has no free adjacent pair. -/
lemma not_freeAt_of_isAltStrip {a c : Fin m → ℕ} (h : IsAltStrip a c) {i j : Fin m}
    (hj : (j : ℕ) = (i : ℕ) + 1) : ¬ FreeAt a c i j :=
  fun hfree => hfree j ⟨h.1 j, h.2 i j hj⟩

/-! ### The sign-reversing involution -/

/-- The set of positions `i` such that the adjacent pair `(i, i+1)` is free for `c`. -/
def freeSet (a c : Fin m → ℕ) : Set ℕ :=
  {i | ∃ h : i + 1 < m, FreeAt a c ⟨i, Nat.lt_of_succ_lt h⟩ ⟨i + 1, h⟩}

/-- The free positions only depend on the multiset of entries of `c`. -/
lemma freeSet_comp (a c : Fin m → ℕ) (w : Equiv.Perm (Fin m)) :
    freeSet a (c ∘ w) = freeSet a c := by
  ext i
  simp only [freeSet, Set.mem_ofPred_eq, FreeAt, Function.comp_apply]
  constructor
  · rintro ⟨h, hf⟩
    exact ⟨h, fun k hk => hf (w.symm k) (by simpa using hk)⟩
  · rintro ⟨h, hf⟩
    exact ⟨h, fun k hk => hf (w k) hk⟩

open scoped Classical in
/-- The transposition of the two positions `sInf S` and `sInf S + 1`, when `sInf S` lies
in the set `S` of free positions (and the identity otherwise). -/
noncomputable def flipOfSet (m : ℕ) (S : Set ℕ) : Equiv.Perm (Fin m) :=
  if h : sInf S + 1 < m ∧ sInf S ∈ S then
    Equiv.swap ⟨sInf S, Nat.lt_of_succ_lt h.1⟩ ⟨sInf S + 1, h.1⟩
  else 1

/-- The permutation exchanging the two entries at the least free position (the identity if
there is no free position). -/
noncomputable def flipPerm (a c : Fin m → ℕ) : Equiv.Perm (Fin m) := flipOfSet m (freeSet a c)

lemma flipPerm_comp (a c : Fin m → ℕ) (w : Equiv.Perm (Fin m)) :
    flipPerm a (c ∘ w) = flipPerm a c :=
  congrArg (flipOfSet m) (freeSet_comp a c w)

/-- When there is a free position, the flipping permutation is the transposition of the
two entries at the least free position. -/
lemma flipPerm_eq_swap {a c : Fin m → ℕ} (hne : (freeSet a c).Nonempty) :
    ∃ (i j : Fin m), (j : ℕ) = (i : ℕ) + 1 ∧ FreeAt a c i j ∧
      flipPerm a c = Equiv.swap i j := by
  have hmem : sInf (freeSet a c) ∈ freeSet a c := Nat.sInf_mem hne
  obtain ⟨hlt, hfree⟩ := hmem
  refine ⟨⟨sInf (freeSet a c), Nat.lt_of_succ_lt hlt⟩, ⟨sInf (freeSet a c) + 1, hlt⟩, rfl, hfree,
    ?_⟩
  rw [flipPerm, flipOfSet, dite_eq_left ⟨hlt, ⟨hlt, hfree⟩⟩]

/-- A vector which is not a horizontal strip above `a` has a free position. -/
lemma freeSet_nonempty {a c : Fin m → ℕ} (ha : Antitone a) (hac : ∀ i, a i ≤ c i)
    (h : ¬ IsAltStrip a c) : (freeSet a c).Nonempty := by
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  refine h (isAltStrip_of_forall_not_free ha hac fun i j hj hfree => ?_)
  have hlt : (i : ℕ) + 1 < m := by
    rw [← hj]
    exact j.isLt
  have hmem : (i : ℕ) ∈ freeSet a c := by
    refine ⟨hlt, ?_⟩
    have hi : (⟨(i : ℕ), Nat.lt_of_succ_lt hlt⟩ : Fin m) = i := Fin.ext rfl
    have hjj : (⟨(i : ℕ) + 1, hlt⟩ : Fin m) = j := Fin.ext hj.symm
    rw [hi, hjj]
    exact hfree
  rw [hemp] at hmem
  exact hmem

/-- If there is no free position, the flipping permutation is the identity. -/
lemma flipPerm_eq_one {a c : Fin m → ℕ} (hemp : ¬ (freeSet a c).Nonempty) :
    flipPerm a c = 1 := by
  rw [flipPerm, flipOfSet, dite_eq_right]
  rintro ⟨-, hmem⟩
  exact hemp ⟨_, hmem⟩

/-- Applying the flipping permutation keeps all the entries above `a`. -/
lemma le_comp_flipPerm {a c : Fin m → ℕ} (ha : Antitone a) (hac : ∀ i, a i ≤ c i) (k : Fin m) :
    a k ≤ c (flipPerm a c k) := by
  by_cases hne : (freeSet a c).Nonempty
  · obtain ⟨I, J, hJ, hfree, hswap⟩ := flipPerm_eq_swap hne
    rw [hswap]
    have hIJ : I ≠ J := by
      intro hcon
      rw [hcon] at hJ
      omega
    rcases eq_or_ne k I with hkIeq | hkI
    · subst hkIeq
      rw [Equiv.swap_apply_left]
      have h1 : a J ≤ c J := hac J
      have h2 := hfree J
      omega
    rcases eq_or_ne k J with hkJeq | hkJ
    · have hIJle : I ≤ J := Fin.le_def.2 (by omega)
      rw [hkJeq, Equiv.swap_apply_right]
      exact le_trans (ha hIJle) (hac I)
    · rw [Equiv.swap_apply_of_ne_of_ne hkI hkJ]
      exact hac k
  · rw [flipPerm_eq_one hne]
    exact hac k

/-- The exponent vector obtained by exchanging the two entries at the least free
position. -/
noncomputable def flipFinsupp (a : Fin m → ℕ) (d : Fin m →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun k => (a + ⇑d) (flipPerm a (a + ⇑d) k) - a k)

lemma add_flipFinsupp {a : Fin m → ℕ} (ha : Antitone a) (d : Fin m →₀ ℕ) :
    a + ⇑(flipFinsupp a d) = (a + ⇑d) ∘ (flipPerm a (a + ⇑d)) := by
  funext k
  have hle := le_comp_flipPerm (c := a + ⇑d) ha (fun i => Nat.le_add_right (a i) (d i)) k
  simp only [flipFinsupp, Pi.add_apply, Finsupp.equivFunOnFinite_symm_apply_apply,
    Function.comp_apply] at hle ⊢
  omega

/-- A vector with a free position is not a horizontal strip above `a`. -/
lemma not_isAltStrip_of_freeSet_nonempty {a c : Fin m → ℕ} (hne : (freeSet a c).Nonempty) :
    ¬ IsAltStrip a c := by
  obtain ⟨i, hlt, hfree⟩ := hne
  exact fun hstrip => not_freeAt_of_isAltStrip hstrip (i := ⟨i, Nat.lt_of_succ_lt hlt⟩)
    (j := ⟨i + 1, hlt⟩) rfl hfree

open scoped Classical in
/-- The exponent vectors of weight `r` above `a` which are not horizontal strips. -/
noncomputable def badSet (a : Fin m → ℕ) (r : ℕ) : Finset (Fin m →₀ ℕ) :=
  (Finset.finsuppAntidiag (univ : Finset (Fin m)) r).filter (fun d => ¬ IsAltStrip a (a + ⇑d))

/-- The flipping map preserves the weight and the failure of being a horizontal strip. -/
lemma flipFinsupp_mem_badSet {a : Fin m → ℕ} (ha : Antitone a) {r : ℕ} {d : Fin m →₀ ℕ}
    (hd : d ∈ badSet a r) : flipFinsupp a d ∈ badSet a r := by
  classical
  rw [badSet, Finset.mem_filter, Finset.mem_finsuppAntidiag] at hd ⊢
  obtain ⟨⟨hsum, -⟩, hbad⟩ := hd
  have hkey := add_flipFinsupp ha d
  have hsum' : ∑ k, (a k + (flipFinsupp a d) k) = ∑ k, (a k + d k) := by
    calc ∑ k, (a k + (flipFinsupp a d) k)
        = ∑ k, (a + ⇑d) ((flipPerm a (a + ⇑d)) k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          exact congrFun hkey k
      _ = ∑ k, (a + ⇑d) k := Equiv.sum_comp (flipPerm a (a + ⇑d)) _
      _ = ∑ k, (a k + d k) := rfl
  have hsumfl : ∑ k, (flipFinsupp a d) k = ∑ k, d k := by
    simp only [Finset.sum_add_distrib] at hsum'
    omega
  refine ⟨⟨?_, by simp⟩, ?_⟩
  · rw [show univ.sum ⇑(flipFinsupp a d) = ∑ k, (flipFinsupp a d) k from rfl, hsumfl]
    exact hsum
  · rw [hkey]
    refine not_isAltStrip_of_freeSet_nonempty ?_
    rw [freeSet_comp]
    exact freeSet_nonempty ha (fun i => Nat.le_add_right (a i) (d i)) hbad

/-- **The terms which are not horizontal strips cancel**: the sum of the alternants of the
exponent vectors of weight `r` above `a` which are not horizontal strips vanishes. -/
theorem sum_alt_badSet {a : Fin m → ℕ} (ha : Antitone a) (r : ℕ) :
    ∑ d ∈ badSet a r, alt m R (a + ⇑d) = 0 := by
  classical
  refine Finset.sum_involution (fun d _ => flipFinsupp a d) ?_ ?_
    (fun d hd => flipFinsupp_mem_badSet ha hd) ?_
  · intro d hd
    obtain ⟨-, hbad⟩ := Finset.mem_filter.1 hd
    have hne : (freeSet a (a + ⇑d)).Nonempty :=
      freeSet_nonempty ha (fun i => Nat.le_add_right (a i) (d i)) hbad
    obtain ⟨I, J, hJ, -, hswap⟩ := flipPerm_eq_swap hne
    have hIJ : I ≠ J := by
      intro hcon
      rw [hcon] at hJ
      omega
    rw [add_flipFinsupp ha d, alt_comp_perm, hswap, Equiv.Perm.sign_swap hIJ]
    push_cast
    simp
  · intro d hd hne0 hcon
    replace hcon : flipFinsupp a d = d := hcon
    obtain ⟨-, hbad⟩ := Finset.mem_filter.1 hd
    have hne : (freeSet a (a + ⇑d)).Nonempty :=
      freeSet_nonempty ha (fun i => Nat.le_add_right (a i) (d i)) hbad
    obtain ⟨I, J, hJ, -, hswap⟩ := flipPerm_eq_swap hne
    have hIJ : I ≠ J := by
      intro hcon'
      rw [hcon'] at hJ
      omega
    have hfix : (a + ⇑d) ∘ (flipPerm a (a + ⇑d)) = a + ⇑d := by
      rw [← add_flipFinsupp ha d, hcon]
    have hvalue : (a + ⇑d) I = (a + ⇑d) J := by
      have := congrFun hfix I
      rw [hswap] at this
      simp only [Function.comp_apply, Equiv.swap_apply_left] at this
      exact this.symm
    exact hne0 (alt_eq_zero_of_eq hIJ hvalue)
  · intro d hd
    change flipFinsupp a (flipFinsupp a d) = d
    have hfl := add_flipFinsupp ha (flipFinsupp a d)
    rw [add_flipFinsupp ha d, flipPerm_comp] at hfl
    have hsq : ((a + ⇑d) ∘ (flipPerm a (a + ⇑d))) ∘ (flipPerm a (a + ⇑d)) = a + ⇑d := by
      obtain ⟨-, hbad⟩ := Finset.mem_filter.1 hd
      have hne : (freeSet a (a + ⇑d)).Nonempty :=
        freeSet_nonempty ha (fun i => Nat.le_add_right (a i) (d i)) hbad
      obtain ⟨I, J, -, -, hswap⟩ := flipPerm_eq_swap hne
      funext k
      simp [hswap, Function.comp_apply]
    rw [hsq] at hfl
    refine Finsupp.ext fun k => ?_
    have := congrFun hfl k
    simp only [Pi.add_apply] at this
    omega

open scoped Classical in
/-- **The Pieri rule for alternants**: multiplying the alternant of a decreasing exponent
vector `a` by the complete homogeneous symmetric polynomial `h_r` gives the sum of the
alternants of the exponent vectors obtained from `a` by adding a horizontal strip of size
`r`. -/
theorem hsymm_mul_alt_strip {a : Fin m → ℕ} (ha : Antitone a) (r : ℕ) :
    hsymm (Fin m) R r * alt m R a
      = ∑ d ∈ (Finset.finsuppAntidiag (univ : Finset (Fin m)) r).filter
          (fun d : Fin m →₀ ℕ => IsAltStrip a (a + ⇑d)), alt m R (a + ⇑d) := by
  classical
  have hset : (Finset.finsuppAntidiag (univ : Finset (Fin m)) r).filter
      (fun d : Fin m →₀ ℕ => ¬ IsAltStrip a (a + ⇑d)) = badSet a r := by
    rw [badSet]
  rw [hsymm_mul_alt, ← Finset.sum_filter_add_sum_filter_not
    (Finset.finsuppAntidiag (univ : Finset (Fin m)) r)
    (fun d : Fin m →₀ ℕ => IsAltStrip a (a + ⇑d)),
    hset, sum_alt_badSet ha, add_zero]

end MvPolynomial
