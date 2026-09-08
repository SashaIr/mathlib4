/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.JacobiTrudi
import Mathlib.RepresentationTheory.SymmetricGroup.SchurCharacter
import Mathlib.GroupTheory.Perm.SymmetricGroup.YoungSubgroup

/-!
# The Schur class functions are the irreducible characters of the symmetric group

Combining the Jacobi-Trudi formula with the computation of the Frobenius characteristic of
the permutation character of a Young subgroup, we show that each Schur class function
`Equiv.Perm.schurChar lam` is an integral combination of characters of actual representations
of `S_n`, hence a virtual character.  Since it has norm one and a positive value at the
identity, it is the character of a simple representation over `ℂ`.

## Main definitions

* `Equiv.Perm.jtList m lam s` : the list of indices of the complete homogeneous symmetric
  polynomials occurring in the term of the Jacobi-Trudi determinant indexed by the
  permutation `s`.

## Main results

* `Equiv.Perm.schurPoly_eq_sum_jt` : the Jacobi-Trudi formula, expanded as an integral
  combination of the products `h_l`.
* `Equiv.Perm.schurChar_eq_sum_youngPermCharOf` : `schurChar lam` is the corresponding integral
  combination of permutation characters of Young subgroups.
* `Equiv.Perm.isVirtualChar_schurCharC` : `schurChar lam` is a virtual character over `ℂ`.
* `Equiv.Perm.isSimpleChar_schurCharC` : **`schurChar lam` is the character of a simple
  representation of `S_n` over `ℂ`**.
* `Equiv.Perm.exists_eq_schurCharC`, `Equiv.Perm.schurCharC_injective` : the Schur class functions
  are exactly the irreducible characters of `S_n` over `ℂ`, and distinct shapes give
  distinct characters.
* `Equiv.Perm.isSimpleChar_perm_two_iff` : the irreducible characters of `S_2` are the trivial
  character and the signature (Coq `repr_S2`).
-/

open Equiv MvPolynomial List FDRep

namespace Equiv.Perm


/-! ### An auxiliary sum -/

/-- The sum of a list of naturals as a sum over a range of `getD`. -/
lemma sum_range_getD_of_length_le {l : List ℕ} {m : ℕ} (h : l.length ≤ m) :
    ∑ i ∈ Finset.range m, l.getD i 0 = l.sum := by
  induction l generalizing m with
  | nil => simp
  | cons a t ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at h; omega⟩
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.sum_cons]
    rw [ih (by simpa using Nat.succ_le_succ_iff.1 h)]
    ring

/-! ### The Jacobi-Trudi expansion -/

variable {m : ℕ}

/-- The term of the Jacobi-Trudi determinant indexed by `s` involves nonnegative indices. -/
def JtGood (m : ℕ) (lam : List ℕ) (s : Perm (Fin m)) : Prop :=
  ∀ i : Fin m, ((s i : ℕ) : ℤ) ≤ (lam.getD (s i) 0 : ℤ) + (i : ℕ)

instance (m : ℕ) (lam : List ℕ) (s : Perm (Fin m)) : Decidable (JtGood m lam s) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- The list of indices of the complete homogeneous symmetric polynomials occurring in the
term of the Jacobi-Trudi determinant indexed by the permutation `s`. -/
def jtList (m : ℕ) (lam : List ℕ) (s : Perm (Fin m)) : List ℕ :=
  List.ofFn fun i : Fin m => ((lam.getD (s i) 0 : ℤ) + (i : ℕ) - (s i : ℕ)).toNat

/-- The integer coefficient of the term of the Jacobi-Trudi determinant indexed by `s`. -/
def jtCoeff (m : ℕ) (lam : List ℕ) (s : Perm (Fin m)) : ℤ :=
  if JtGood m lam s then (Equiv.Perm.sign s : ℤ) else 0

lemma prod_jtMatrix_of_jtGood {R : Type*} [CommRing R] (lam : List ℕ) {s : Perm (Fin m)}
    (hs : JtGood m lam s) :
    ∏ i : Fin m, jtMatrix m R lam (s i) i = hProd m R (jtList m lam s) := by
  rw [hProd, jtList, List.map_ofFn, List.prod_ofFn]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h0 : (0 : ℤ) ≤ (lam.getD (s i) 0 : ℤ) + (i : ℕ) - (s i : ℕ) := by
    have := hs i; omega
  simp only [jtMatrix, Matrix.of_apply, Function.comp_apply]
  rw [hsymmInt, ite_eq_left h0]

lemma prod_jtMatrix_of_not_jtGood {R : Type*} [CommRing R] (lam : List ℕ) {s : Perm (Fin m)}
    (hs : ¬ JtGood m lam s) :
    ∏ i : Fin m, jtMatrix m R lam (s i) i = 0 := by
  simp only [JtGood, not_forall, not_le] at hs
  obtain ⟨i, hi⟩ := hs
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  have hneg : (lam.getD (s i) 0 : ℤ) + (i : ℕ) - (s i : ℕ) < 0 := by omega
  simp only [jtMatrix, Matrix.of_apply]
  exact hsymmInt_of_neg hneg

/-- Each list occurring in the Jacobi-Trudi expansion is a composition of `lam.sum`. -/
lemma sum_jtList {lam : List ℕ} (hlen : lam.length ≤ m) {s : Perm (Fin m)}
    (hs : JtGood m lam s) : (jtList m lam s).sum = lam.sum := by
  have key : ((jtList m lam s).sum : ℤ) = (lam.sum : ℤ) := by
    rw [jtList, List.sum_ofFn, Nat.cast_sum]
    rw [Finset.sum_congr rfl fun (i : Fin m) _ =>
      Int.toNat_of_nonneg (a := (lam.getD (s i) 0 : ℤ) + (i : ℕ) - (s i : ℕ))
        (by have := hs i; omega)]
    have h1 : ∑ i : Fin m, ((lam.getD (s i) 0 : ℤ) + (i : ℕ) - (s i : ℕ))
        = (∑ i : Fin m, (lam.getD (s i) 0 : ℤ)) + (∑ i : Fin m, ((i : ℕ) : ℤ))
          - ∑ i : Fin m, ((s i : ℕ) : ℤ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have h2 : ∑ i : Fin m, (lam.getD (s i) 0 : ℤ) = ∑ j : Fin m, (lam.getD j 0 : ℤ) :=
      Equiv.sum_comp s fun j : Fin m => (lam.getD j 0 : ℤ)
    have h3 : ∑ i : Fin m, ((s i : ℕ) : ℤ) = ∑ j : Fin m, ((j : ℕ) : ℤ) :=
      Equiv.sum_comp s fun j : Fin m => ((j : ℕ) : ℤ)
    rw [h1, h2, h3, add_sub_cancel_right, ← Nat.cast_sum, Fin.sum_univ_eq_sum_range
      (fun j => lam.getD j 0), sum_range_getD_of_length_le hlen]
  exact_mod_cast key

/-- **The Jacobi-Trudi formula, expanded**: the Schur polynomial of a partition with at
most `m` parts is an integral combination of products of complete homogeneous symmetric
polynomials. -/
theorem schurPoly_eq_sum_jt {R : Type*} [CommRing R] {lam : List ℕ} (hlam : IsPart lam)
    (hlen : lam.length ≤ m) :
    schurPoly (Fin m) R lam = ∑ s : Perm (Fin m), jtCoeff m lam s • hProd m R (jtList m lam s) := by
  rw [schurPoly_eq_det_jtMatrix hlam hlen, Matrix.det_apply']
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : JtGood m lam s
  · rw [prod_jtMatrix_of_jtGood lam hs, jtCoeff, ite_eq_left hs, zsmul_eq_mul]
  · rw [prod_jtMatrix_of_not_jtGood lam hs, jtCoeff, ite_eq_right hs, mul_zero, zero_smul]

/-! ### The Schur class function as a combination of permutation characters -/

variable {n : ℕ}

/-- The Frobenius characteristic is compatible with integral scalars. -/
lemma frobChar_zsmul (k : ℕ) (c : ℤ) (f : Perm (Fin n) → ℚ) :
    frobChar k (c • f) = c • frobChar k f := by
  rw [← Int.cast_smul_eq_zsmul ℚ, frobChar_smul, Int.cast_smul_eq_zsmul]

/-- The Frobenius characteristic of a finite sum of class functions. -/
lemma frobChar_sum (k : ℕ) {ι : Type*} (s : Finset ι) (F : ι → Perm (Fin n) → ℚ) :
    frobChar k (∑ i ∈ s, F i) = ∑ i ∈ s, frobChar k (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [frobChar]
  | insert a s ha ih => rw [Finset.sum_insert ha, frobChar_add, ih, Finset.sum_insert ha]

/-- An integral multiple of a class function is a class function. -/
lemma IsClassFun.zsmul {f : Perm (Fin n) → ℚ} (hf : IsClassFun f) (c : ℤ) :
    IsClassFun (c • f) := fun sigma tau => by
  simp only [Pi.smul_apply, hf sigma tau]

/-- A finite sum of class functions is a class function. -/
lemma isClassFun_sum {ι : Type*} (s : Finset ι) (F : ι → Perm (Fin n) → ℚ)
    (hF : ∀ i ∈ s, IsClassFun (F i)) : IsClassFun (∑ i ∈ s, F i) := fun sigma tau => by
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i hi => hF i hi sigma tau

/-- **The Schur class function is an integral combination of the permutation characters of
the Young subgroups.** -/
theorem schurChar_eq_sum_youngPermCharOf (lam : PartIdx n n) :
    schurChar lam
      = ∑ s : Perm (Fin n), jtCoeff n lam.1 s • youngPermCharOf n (jtList n lam.1 s) := by
  refine eq_of_frobChar_eq (isClassFun_schurChar lam)
    (isClassFun_sum _ _ fun s _ => (youngPermCharOf_isClassFun n _).zsmul _) ?_
  rw [frobChar_schurChar, frobChar_sum, schurPoly_eq_sum_jt lam.2.1 lam.2.2.2]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [frobChar_zsmul]
  by_cases hs : JtGood n lam.1 s
  · rw [frobChar_youngPermCharOf n _ (by rw [sum_jtList lam.2.2.2 hs, lam.2.2.1])]
  · rw [jtCoeff, ite_eq_right hs, zero_smul, zero_smul]

/-! ### The Schur class functions are the irreducible characters over `ℂ` -/

/-- The Schur class function of `S_n`, with complex values. -/
noncomputable def schurCharC (lam : PartIdx n n) : Perm (Fin n) → ℂ :=
  fun sigma => ((schurChar lam sigma : ℚ) : ℂ)

instance neZero_card_perm_complex (n : ℕ) : NeZero ((Nat.card (Perm (Fin n)) : ℂ)) :=
  ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩

/-- The permutation character of a Young subgroup, with complex values, is a virtual
character. -/
theorem isVirtualChar_youngPermCharOfC (n : ℕ) (l : List ℕ) :
    IsVirtualChar (fun sigma : Perm (Fin n) => ((youngPermCharOf n l sigma : ℚ) : ℂ)) := by
  by_cases h : l.sum = n
  · subst h
    have hv := isVirtualChar_card_fixedPoints ℂ (G := Perm (Fin l.sum))
      (X := Perm (Fin l.sum) ⧸ youngSubgroup l)
    have heq : (fun sigma : Perm (Fin l.sum) =>
        ((youngPermCharOf l.sum l sigma : ℚ) : ℂ))
        = fun sigma : Perm (Fin l.sum) =>
          (Nat.card {q : Perm (Fin l.sum) ⧸ youngSubgroup l // sigma • q = q} : ℂ) := by
      funext sigma
      rw [youngPermCharOf_self, youngPermChar]
      push_cast
      rfl
    rw [heq]
    exact hv
  · simp only [youngPermCharOf, dite_eq_right h, Pi.zero_apply, Rat.cast_zero]
    exact IsVirtualChar.zero

/-- **The Schur class function is a virtual character of `S_n` over `ℂ`.** -/
theorem isVirtualChar_schurCharC (lam : PartIdx n n) : IsVirtualChar (schurCharC lam) := by
  have heq : schurCharC lam = ∑ s : Perm (Fin n), jtCoeff n lam.1 s •
      fun sigma : Perm (Fin n) => ((youngPermCharOf n (jtList n lam.1 s) sigma : ℚ) : ℂ) := by
    funext sigma
    rw [schurCharC, schurChar_eq_sum_youngPermCharOf lam]
    simp only [Finset.sum_apply, Pi.mul_apply, Pi.intCast_apply,
      zsmul_eq_mul, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast]
  rw [heq]
  exact IsVirtualChar.sum _ fun s _ => (isVirtualChar_youngPermCharOfC n _).zsmul _

/-- A class function of the symmetric group takes the same value at a permutation and at
its inverse. -/
lemma IsClassFun.inv {f : Perm (Fin n) → ℚ} (hf : IsClassFun f) (sigma : Perm (Fin n)) :
    f sigma⁻¹ = f sigma := by
  obtain ⟨u, hu⟩ := isConj_iff.1
    (Equiv.Perm.isConj_iff_cycleType_eq.2 (Equiv.Perm.cycleType_inv sigma).symm)
  have hcl := hf sigma u⁻¹
  rw [inv_inv] at hcl
  rw [← hu, hcl]

/-- The sum of the squares of the values of a Schur class function is `n !`. -/
lemma sum_sq_schurChar (lam : PartIdx n n) :
    ∑ sigma : Perm (Fin n), schurChar lam sigma * schurChar lam sigma
      = (Nat.factorial n : ℚ) := by
  have h := classInner_schurChar lam lam
  rw [ite_eq_left rfl, classInner] at h
  have hne : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have h2 : (Nat.factorial n : ℚ) * (((Nat.factorial n : ℚ))⁻¹ *
      ∑ sigma : Perm (Fin n), schurChar lam sigma * schurChar lam sigma)
      = (Nat.factorial n : ℚ) * 1 := by rw [h]
  rwa [← mul_assoc, mul_inv_cancel₀ hne, one_mul, mul_one] at h2

/-- **The Schur class function has norm one.** -/
theorem charBilin_schurCharC (lam : PartIdx n n) :
    charBilin (schurCharC lam) (schurCharC lam) = (Fintype.card (Perm (Fin n)) : ℂ) := by
  have hterm : ∀ sigma : Perm (Fin n), schurCharC lam sigma * schurCharC lam sigma⁻¹
      = ((schurChar lam sigma * schurChar lam sigma : ℚ) : ℂ) := by
    intro sigma
    simp only [schurCharC]
    rw [(isClassFun_schurChar lam).inv sigma]
    push_cast
    ring
  rw [charBilin, Finset.sum_congr rfl fun sigma _ => hterm sigma, ← Rat.cast_sum,
    sum_sq_schurChar lam, Fintype.card_perm, Fintype.card_fin]
  push_cast
  ring

/-- The number of standard Young tableaux of a given shape is positive. -/
lemma numStdTab_pos {sh : List ℕ} (hsh : IsPart sh) : 0 < numStdTab sh := by
  rcases Nat.eq_zero_or_pos (numStdTab sh) with h | h
  · exfalso
    have := numStdTab_mul_hookProd hsh
    rw [h, zero_mul] at this
    exact (Nat.factorial_ne_zero sh.sum) this.symm
  · exact h

/-- **The Schur class functions are the irreducible characters of the symmetric group**:
the class function `schurChar lam`, viewed with complex values, is the character of a
simple representation of `S_n` over `ℂ`. -/
theorem isSimpleChar_schurCharC (lam : PartIdx n n) : IsSimpleChar (schurCharC lam) := by
  obtain ⟨c, hc, hor⟩ := exists_isSimpleChar_of_norm_one (schurCharC lam)
    (isVirtualChar_schurCharC lam) (charBilin_schurCharC lam)
  rcases hor with rfl | hneg
  · exact hc
  · exfalso
    obtain ⟨V, _, rfl⟩ := hc
    have h1 : schurCharC lam 1 = (numStdTab lam.1 : ℂ) := by
      simp only [schurCharC, schurChar_one lam, Rat.cast_natCast]
    have h2 : ((numStdTab lam.1 : ℕ) : ℂ) = -((Module.finrank ℂ V.V : ℕ) : ℂ) := by
      rw [← h1, hneg, Pi.neg_apply, FDRep.char_one]
    have h3 : ((numStdTab lam.1 + Module.finrank ℂ V.V : ℕ) : ℂ) = 0 := by
      push_cast
      rw [h2]
      ring
    have h4 : numStdTab lam.1 + Module.finrank ℂ V.V = 0 := by exact_mod_cast h3
    have := numStdTab_pos lam.2.1
    omega

/-! ### Every irreducible character is a Schur class function -/

/-- The character of the regular representation of `S_n`, as a class function. -/
noncomputable def regChar (n : ℕ) : Perm (Fin n) → ℚ :=
  fun sigma => if sigma = 1 then (Nat.factorial n : ℚ) else 0

/-- The regular character is a class function. -/
lemma regChar_isClassFun : IsClassFun (regChar n) := by
  intro sigma tau
  unfold regChar
  congr 1
  simp only [eq_iff_iff]
  constructor
  · intro h
    have : sigma = tau * (tau⁻¹ * sigma * tau) * tau⁻¹ := by group
    rw [this, h]
    group
  · intro h; rw [h]; group

/-- The Frobenius characteristic of the regular character. -/
lemma frobChar_regChar (k : ℕ) :
    frobChar k (regChar n) = pProd k ℚ (cycleTypeList (1 : Perm (Fin n))) := by
  rw [frobChar]
  have hterm : ∀ sigma : Perm (Fin n), regChar n sigma • pProd k ℚ (cycleTypeList sigma)
      = if sigma = 1 then (Nat.factorial n : ℚ) • pProd k ℚ (cycleTypeList (1 : Perm (Fin n)))
        else 0 := by
    intro sigma
    unfold regChar
    split
    · next h => rw [h]
    · rw [zero_smul]
  rw [Finset.sum_congr rfl fun sigma _ => hterm sigma, Finset.sum_ite_eq' Finset.univ
    (1 : Perm (Fin n)) fun _ => (Nat.factorial n : ℚ) • pProd k ℚ
      (cycleTypeList (1 : Perm (Fin n))), ite_eq_left (Finset.mem_univ _), smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)), one_smul]

/-- **The regular character is the combination of the Schur class functions weighted by
their dimensions.** -/
theorem regChar_eq_sum_schurChar :
    regChar n = ∑ lam : PartIdx n n, schurChar lam 1 • schurChar lam := by
  refine eq_of_frobChar_eq regChar_isClassFun
    (isClassFun_sum _ _ fun lam _ => fun sigma tau => by
      simp only [Pi.smul_apply, smul_eq_mul, isClassFun_schurChar lam sigma tau]) ?_
  rw [frobChar_regChar, frobChar_sum, pProd_cycleTypeList_eq_sum (1 : Perm (Fin n))]
  exact Finset.sum_congr rfl fun lam _ => by rw [frobChar_smul, frobChar_schurChar]

/-- The regular character of `S_n`, with complex values. -/
noncomputable def regCharC (n : ℕ) : Perm (Fin n) → ℂ :=
  fun sigma => ((regChar n sigma : ℚ) : ℂ)

/-- The complex regular character is the combination of the Schur class functions weighted
by their dimensions. -/
lemma regCharC_eq_sum (n : ℕ) : regCharC n
    = fun g => ∑ lam : PartIdx n n, ((schurChar lam 1 : ℚ) : ℂ) * schurCharC lam g := by
  funext g
  rw [regCharC, regChar_eq_sum_schurChar]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Rat.cast_sum, Rat.cast_mul,
    schurCharC]

/-- The scalar product of a class function with the regular character. -/
lemma charBilin_regCharC (chi : Perm (Fin n) → ℂ) :
    charBilin chi (regCharC n) = (Nat.factorial n : ℂ) * chi 1 := by
  rw [charBilin]
  rw [Finset.sum_eq_single (1 : Perm (Fin n))]
  · simp [regCharC, regChar]
    ring
  · intro b _ hb
    have : b⁻¹ ≠ 1 := fun h => hb (by simpa using congrArg (·⁻¹) h)
    simp [regCharC, regChar, this]
  · intro h
    exact absurd (Finset.mem_univ (1 : Perm (Fin n))) h

/-- **Every irreducible character of `S_n` over `ℂ` is a Schur class function.** -/
theorem exists_eq_schurCharC {chi : Perm (Fin n) → ℂ} (h : IsSimpleChar chi) :
    ∃ lam : PartIdx n n, chi = schurCharC lam := by
  by_contra hcon
  push Not at hcon
  have hzero : charBilin chi (regCharC n) = 0 := by
    rw [regCharC_eq_sum, charBilin_sum_right]
    refine Finset.sum_eq_zero fun lam _ => ?_
    rw [charBilin_smul_right, charBilin_isSimpleChar h (isSimpleChar_schurCharC lam),
      ite_eq_right (hcon lam), mul_zero]
  rw [charBilin_regCharC] at hzero
  rcases mul_eq_zero.1 hzero with h1 | h1
  · exact (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)) h1
  · exact isSimpleChar_one_ne_zero h h1

/-- The Schur class functions attached to distinct partitions are distinct. -/
theorem schurCharC_injective (lam mu : PartIdx n n) (h : schurCharC lam = schurCharC mu) :
    lam = mu := by
  by_contra hne
  have h0 : classInner (schurChar lam) (schurChar mu) = 0 := by
    rw [classInner_schurChar, ite_eq_right hne]
  have h1 : classInner (schurChar lam) (schurChar lam) = 1 := by
    rw [classInner_schurChar, ite_eq_left rfl]
  have hq : schurChar lam = schurChar mu := by
    funext sigma
    have := congrFun h sigma
    simp only [schurCharC] at this
    exact_mod_cast this
  rw [hq] at h0 h1
  exact one_ne_zero (h1.symm.trans h0)

/-! ### The irreducible characters of `S_2` -/

/-- A partition of `2` is either the row `[2]` or the column `[1, 1]`. -/
lemma eq_of_isPart_sum_two {p : List ℕ} (hp : IsPart p) (hsum : p.sum = 2) :
    p = [2] ∨ p = [1, 1] := by
  have hlen : p.length ≤ 2 := hsum ▸ hp.length_le_sum
  match p with
  | [] => simp at hsum
  | [a] =>
    left
    simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
    rw [hsum]
  | [a, b] =>
    right
    have hb : 0 < b := hp.pos_of_mem (by simp)
    have hab : b ≤ a := by simpa using hp.1
    simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
    have ha1 : a = 1 := by omega
    have hb1 : b = 1 := by omega
    rw [ha1, hb1]
  | _ :: _ :: _ :: _ => simp only [List.length_cons] at hlen; omega

/-- The row shape of `S_2`. -/
def rowIdxTwo : PartIdx 2 2 := ⟨[2], by decide, by decide, by decide⟩

/-- The column shape of `S_2`. -/
def colIdxTwo : PartIdx 2 2 := ⟨[1, 1], by decide, by decide, by decide⟩

/-- **The irreducible characters of `S_2`** are the trivial character and the signature
(Coq `repr_S2`). -/
theorem isSimpleChar_perm_two_iff {chi : Perm (Fin 2) → ℂ} :
    IsSimpleChar chi ↔
      chi = (fun _ => 1) ∨ chi = fun sigma => ((Equiv.Perm.sign sigma : ℤ) : ℂ) := by
  have hrow : schurCharC rowIdxTwo = fun _ : Perm (Fin 2) => (1 : ℂ) := by
    funext sigma
    rw [schurCharC, schurChar_row (by norm_num) rowIdxTwo rfl]
    norm_num
  have hcol : schurCharC colIdxTwo
      = fun sigma : Perm (Fin 2) => ((Equiv.Perm.sign sigma : ℤ) : ℂ) := by
    funext sigma
    rw [schurCharC, schurChar_column colIdxTwo (by rfl)]
    norm_num
  constructor
  · intro h
    obtain ⟨lam, rfl⟩ := exists_eq_schurCharC h
    rcases eq_of_isPart_sum_two lam.2.1 lam.2.2.1 with hlam | hlam
    · exact Or.inl (by rw [show lam = rowIdxTwo from Subtype.ext hlam, hrow])
    · exact Or.inr (by rw [show lam = colIdxTwo from Subtype.ext hlam, hcol])
  · rintro (rfl | rfl)
    · rw [← hrow]; exact isSimpleChar_schurCharC rowIdxTwo
    · rw [← hcol]; exact isSimpleChar_schurCharC colIdxTwo

end Equiv.Perm
