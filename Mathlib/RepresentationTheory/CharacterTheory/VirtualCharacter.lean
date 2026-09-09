/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.RepresentationTheory.CharacterTheory.Decomposition

/-!
# Virtual characters of norm one

A *virtual character* of a finite group `G` is a difference of two characters.  The
classical criterion says that a virtual character of norm one is, up to sign, the
character of a simple representation.  This is the last general prerequisite for the
identification of the Schur class functions with the irreducible characters of the
symmetric group.

## Main definitions

* `FDRep.charBilin f h = ∑ g, f g * h g⁻¹` : the (unnormalised) scalar product of two
  class functions.

## Main results

* `FDRep.charBilin_isSimpleChar` : the simple characters are orthogonal, of norm the order
  of the group.
* `FDRep.exists_isSimpleChar_of_norm_one` : a difference of two characters whose norm is
  the order of the group is, up to sign, a simple character.
-/

namespace FDRep

open CategoryTheory Representation LinearMap Module

universe u

variable {k G : Type u} [Field k] [Group G]

/-! ### Virtual characters -/

/-- A *virtual character* of `G` is a difference of two sums of simple characters, that
is, an integral combination of the characters of the simple representations. -/
def IsVirtualChar (chi : G → k) : Prop :=
  ∃ la lb : Multiset (G → k), (∀ c ∈ la, IsSimpleChar c) ∧ (∀ c ∈ lb, IsSimpleChar c) ∧
    chi = la.sum - lb.sum

/-- A sum of virtual characters is a virtual character. -/
theorem IsVirtualChar.add {f h : G → k} (hf : IsVirtualChar f) (hh : IsVirtualChar h) :
    IsVirtualChar (f + h) := by
  obtain ⟨la, lb, hla, hlb, hfeq⟩ := hf
  obtain ⟨ma, mb, hma, hmb, hheq⟩ := hh
  refine ⟨la + ma, lb + mb, ?_, ?_, ?_⟩
  · intro c hc; rcases Multiset.mem_add.1 hc with h | h; exacts [hla c h, hma c h]
  · intro c hc; rcases Multiset.mem_add.1 hc with h | h; exacts [hlb c h, hmb c h]
  · rw [hfeq, hheq, Multiset.sum_add, Multiset.sum_add]; abel

/-- The opposite of a virtual character is a virtual character. -/
theorem IsVirtualChar.neg {f : G → k} (hf : IsVirtualChar f) : IsVirtualChar (-f) := by
  obtain ⟨la, lb, hla, hlb, hfeq⟩ := hf
  exact ⟨lb, la, hlb, hla, by rw [hfeq]; abel⟩

/-- The zero function is a virtual character. -/
theorem IsVirtualChar.zero : IsVirtualChar (0 : G → k) :=
  ⟨0, 0, by simp, by simp, by simp⟩

/-- A difference of virtual characters is a virtual character. -/
theorem IsVirtualChar.sub {f h : G → k} (hf : IsVirtualChar f) (hh : IsVirtualChar h) :
    IsVirtualChar (f - h) := by
  have := hf.add hh.neg
  rwa [← sub_eq_add_neg] at this

/-- A finite sum of virtual characters is a virtual character. -/
theorem IsVirtualChar.sum {ι : Type*} (s : Finset ι) {F : ι → G → k}
    (hF : ∀ i ∈ s, IsVirtualChar (F i)) : IsVirtualChar (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using IsVirtualChar.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

/-- An integral multiple of a virtual character is a virtual character. -/
theorem IsVirtualChar.zsmul {f : G → k} (hf : IsVirtualChar f) (c : ℤ) :
    IsVirtualChar (c • f) := by
  induction c using Int.induction_on with
  | zero => simpa using IsVirtualChar.zero
  | succ i ih => rw [add_smul, one_smul]; exact ih.add hf
  | pred i ih => rw [sub_smul, one_smul]; exact ih.sub hf

variable [Fintype G]

/-! ### The scalar product of class functions -/

/-- The unnormalised scalar product `∑ g, f g * h g⁻¹` of two class functions. -/
def charBilin (f h : G → k) : k := ∑ g : G, f g * h g⁻¹

lemma charBilin_sum_left {ι : Type*} (s : Finset ι) (F : ι → G → k) (h : G → k) :
    charBilin (fun g => ∑ i ∈ s, F i g) h = ∑ i ∈ s, charBilin (F i) h := by
  simp only [charBilin, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma charBilin_sum_right {ι : Type*} (s : Finset ι) (f : G → k) (F : ι → G → k) :
    charBilin f (fun g => ∑ i ∈ s, F i g) = ∑ i ∈ s, charBilin f (F i) := by
  simp only [charBilin, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma charBilin_smul_left (c : k) (f h : G → k) :
    charBilin (fun g => c * f g) h = c * charBilin f h := by
  simp only [charBilin, Finset.mul_sum, mul_assoc]

lemma charBilin_smul_right (c : k) (f h : G → k) :
    charBilin f (fun g => c * h g) = c * charBilin f h := by
  simp only [charBilin, Finset.mul_sum]
  exact Finset.sum_congr rfl fun g _ => by ring

variable [IsAlgClosed k] [CharZero k]

open scoped Classical in
/-- The characters of simple representations are orthogonal, and of norm the order of the
group. -/
theorem charBilin_isSimpleChar {c d : G → k} (hc : IsSimpleChar c) (hd : IsSimpleChar d) :
    charBilin c d = if c = d then (Fintype.card G : k) else 0 := by
  classical
  obtain ⟨V, hV, rfl⟩ := hc
  obtain ⟨W, hW, rfl⟩ := hd
  haveI := hV
  haveI := hW
  have hne : (Fintype.card G : k) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  letI : Invertible (Nat.card G : k) := invertibleOfNonzero
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos))
  have hkey := FDRep.char_orthonormal (k := k) V W
  have h2 : charBilin V.character W.character
      = (Fintype.card G : k) * (if Nonempty (V ≅ W) then 1 else 0) := by
    rw [← hkey, Fintype.card_eq_nat_card, ← mul_assoc,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos)), one_mul]
    rfl
  by_cases hVW : V.character = W.character
  · rw [ite_eq_left hVW]
    have hiso : Nonempty (V ≅ W) := by
      by_contra hcon
      rw [ite_eq_right hcon, mul_zero] at h2
      have hnorm : ∑ g : G, V.character g * V.character g⁻¹ = Nat.card G :=
        (FDRep.simple_iff_char_is_norm_one V).1 hV
      have h3 : ∑ g : G, V.character g * W.character g⁻¹ = 0 := h2
      rw [← hVW, hnorm] at h3
      exact hne (by rw [Fintype.card_eq_nat_card]; exact h3)
    rw [h2, ite_eq_left hiso, mul_one]
  · rw [ite_eq_right hVW, h2, ite_eq_right (fun ⟨i⟩ => hVW (FDRep.char_iso i)), mul_zero]

variable [Finite G] [NeZero (Nat.card G : k)]

omit [Finite G] [NeZero (Nat.card G : k)] in
/-- The norm of an integral combination of simple characters. -/
theorem charBilin_intCombination (S : Finset (G → k)) (hS : ∀ c ∈ S, IsSimpleChar c)
    (n : (G → k) → ℤ) :
    charBilin (fun g => ∑ c ∈ S, (n c : k) * c g) (fun g => ∑ c ∈ S, (n c : k) * c g)
      = (Fintype.card G : k) * ((∑ c ∈ S, n c ^ 2 : ℤ) : k) := by
  classical
  rw [charBilin_sum_left]
  have hterm : ∀ c ∈ S, charBilin (fun g => (n c : k) * c g) (fun g => ∑ d ∈ S, (n d : k) * d g)
      = (Fintype.card G : k) * ((n c : k) * (n c : k)) := by
    intro c hc
    rw [charBilin_smul_left, charBilin_sum_right]
    have hd : ∀ d ∈ S, charBilin c (fun g => (n d : k) * d g)
        = if d = c then (Fintype.card G : k) * (n c : k) else 0 := by
      intro d hdS
      rw [charBilin_smul_right, charBilin_isSimpleChar (hS c hc) (hS d hdS)]
      by_cases h : d = c
      · subst h; rw [ite_eq_left rfl, ite_eq_left rfl, mul_comm]
      · rw [ite_eq_right h, ite_eq_right (fun hh : c = d => h hh.symm), mul_zero]
    rw [Finset.sum_congr rfl hd, Finset.sum_ite_eq' S c, ite_eq_left hc]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  push_cast
  exact Finset.sum_congr rfl fun c _ => by ring

omit [Fintype G] [CharZero k] in
/-- The character of a finite-dimensional representation is a virtual character. -/
theorem IsVirtualChar.of_character (V : FDRep k G) : IsVirtualChar V.character := by
  obtain ⟨l, hl, hleq⟩ := exists_multiset_isSimpleChar V
  exact ⟨l, 0, hl, by simp, by simp [hleq]⟩

omit [Fintype G] in
/-- A simple character does not vanish at the identity. -/
theorem isSimpleChar_one_ne_zero {chi : G → k} (h : IsSimpleChar chi) : chi 1 ≠ 0 := by
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨V, hV, rfl⟩ := h
  intro h1
  have hfr : finrank k V.V = 0 := by
    have hch := FDRep.char_one V
    rw [h1] at hch
    exact_mod_cast hch.symm
  have hzero : V.character = 0 := by
    have hsub : Subsingleton V.V := by
      rw [← finrank_zero_iff (R := k)]
      exact hfr
    funext g
    have hg : V.ρ g = 0 := by ext v; exact Subsingleton.elim _ _
    simp [FDRep.character, hg]
  have hb := charBilin_isSimpleChar (c := V.character) (d := V.character)
    ⟨V, hV, rfl⟩ ⟨V, hV, rfl⟩
  rw [ite_eq_left rfl, hzero] at hb
  simp only [charBilin, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hb
  exact (NeZero.ne ((Nat.card G : k))) (by rw [Nat.card_eq_fintype_card, ← hb])

omit [Finite G] [NeZero (Nat.card G : k)] in
/-- **A virtual character of norm one is a simple character up to sign.** -/
theorem exists_isSimpleChar_of_norm_one (chi : G → k) (hchiv : IsVirtualChar chi)
    (hnorm : charBilin chi chi = (Fintype.card G : k)) :
    ∃ c : G → k, IsSimpleChar c ∧ (chi = c ∨ chi = -c) := by
  classical
  obtain ⟨la, lb, hla, hlb, hchieq⟩ := hchiv
  set S : Finset (G → k) := (la + lb).toFinset with hSdef
  have hS : ∀ c ∈ S, IsSimpleChar c := by
    intro c hc
    rcases Multiset.mem_add.1 (Multiset.mem_toFinset.1 hc) with h | h
    · exact hla c h
    · exact hlb c h
  set n : (G → k) → ℤ := fun c => (la.count c : ℤ) - (lb.count c : ℤ) with hn
  have hsum : ∀ l : Multiset (G → k), l ≤ la + lb →
      ∀ g : G, l.sum g = ∑ c ∈ S, (l.count c : k) * c g := by
    intro l hl g
    have hsub : l.toFinset ⊆ S := fun c hc =>
      Multiset.mem_toFinset.2 (Multiset.subset_of_le hl (Multiset.mem_toFinset.1 hc))
    rw [Finset.sum_multiset_count l]
    simp only [Finset.sum_apply, nsmul_eq_mul]
    exact Finset.sum_subset hsub fun c _ hc => by
      rw [Multiset.count_eq_zero.2 fun h => hc (Multiset.mem_toFinset.2 h)]
      simp
  have hchi : chi = fun g => ∑ c ∈ S, (n c : k) * c g := by
    funext g
    have ha := hsum la (Multiset.le_add_right _ _) g
    have hb := hsum lb (Multiset.le_add_left _ _) g
    simp only [hchieq, Pi.sub_apply, ha, hb, hn]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by push_cast; ring
  rw [hchi, charBilin_intCombination S hS n] at hnorm
  have hcard : (Fintype.card G : k) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hone : ((∑ c ∈ S, n c ^ 2 : ℤ) : k) = 1 :=
    mul_left_cancel₀ hcard (by rw [hnorm, mul_one])
  have honeZ : (∑ c ∈ S, n c ^ 2 : ℤ) = 1 := by exact_mod_cast hone
  obtain ⟨c₀, hc₀S, hc₀⟩ : ∃ c₀ ∈ S, n c₀ ^ 2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Finset.sum_congr rfl hcon] at honeZ
    simp at honeZ
  rw [← Finset.add_sum_erase S (fun c => n c ^ 2) hc₀S] at honeZ
  have hge : 1 ≤ n c₀ ^ 2 := by
    rcases lt_or_eq_of_le (sq_nonneg (n c₀)) with h | h
    · omega
    · exact absurd h.symm hc₀
  have hnn : 0 ≤ ∑ c ∈ S.erase c₀, n c ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hzero : ∑ c ∈ S.erase c₀, n c ^ 2 = 0 := by omega
  have hrest : ∀ c ∈ S.erase c₀, n c = 0 := fun c hc =>
    sq_eq_zero_iff.1 ((Finset.sum_eq_zero_iff_of_nonneg (fun c _ => sq_nonneg (n c))).1 hzero c hc)
  have hc₀one : n c₀ ^ 2 = 1 := by omega
  have hchi₀ : chi = fun g => (n c₀ : k) * c₀ g := by
    rw [hchi]
    funext g
    have hz : ∀ c ∈ S.erase c₀, ((n c : k) * c g) = 0 := fun c hc => by rw [hrest c hc]; simp
    rw [← Finset.add_sum_erase S (fun c => (n c : k) * c g) hc₀S, Finset.sum_eq_zero hz, add_zero]
  refine ⟨c₀, hS c₀ hc₀S, ?_⟩
  have hpm : n c₀ = 1 ∨ n c₀ = -1 := by
    have hfac : (n c₀ - 1) * (n c₀ + 1) = 0 := by nlinarith [hc₀one]
    rcases mul_eq_zero.1 hfac with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  rcases hpm with h | h
  · exact Or.inl (by rw [hchi₀, h]; funext g; simp)
  · exact Or.inr (by rw [hchi₀, h]; funext g; simp)

end FDRep
