/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RepresentationTheory.SymmetricGroup.YoungSubgroup
public import Mathlib.RepresentationTheory.SymmetricGroup.SchurCharacter
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.JacobiTrudi

/-!
# The Schur class functions are the irreducible characters of the symmetric group

Combining the Jacobi-Trudi formula with the computation of the Frobenius characteristic of
the permutation character of a Young subgroup, we show that each Schur class function
`Equiv.Perm.schurChar η` is an integral combination of characters of actual representations
of `S_n`, hence a virtual character.  Since it has norm one and a positive value at the
identity, it is the character of a simple representation.

The representation-theoretic statements are proved over an arbitrary algebraically closed field
`K` of characteristic zero; the classical statements over `ℂ` are the case `K := ℂ`. (The
instance `Complex.isAlgClosed` lives in `Mathlib/Analysis/`, which `Mathlib/RepresentationTheory/`
is not allowed to import, so the specialisation is left to the user.)

## Main definitions

* `Equiv.Perm.jtList m η s` : the list of indices of the complete homogeneous symmetric
  polynomials occurring in the term of the Jacobi-Trudi determinant indexed by the
  permutation `s`.
* `Equiv.Perm.schurCharCast K η` : the Schur class function `schurChar η` with its values
  cast into a field `K` of characteristic zero.

## Main results

* `Equiv.Perm.schurPoly_eq_sum_jt` : the Jacobi-Trudi formula, expanded as an integral
  combination of the products `h_l`.
* `Equiv.Perm.schurChar_eq_sum_youngPermCharOf` : `schurChar η` is the corresponding integral
  combination of permutation characters of Young subgroups.
* `Equiv.Perm.isVirtualChar_schurCharCast` : `schurChar η` is a virtual character over `K`.
* `Equiv.Perm.isSimpleChar_schurCharCast` : **`schurChar η` is the character of a simple
  representation of `S_n` over `K`**.
* `Equiv.Perm.exists_eq_schurCharCast`, `Equiv.Perm.schurCharCast_injective` : the Schur class
  functions are exactly the irreducible characters of `S_n` over `K`, and distinct shapes give
  distinct characters.
* `Equiv.Perm.isSimpleChar_perm_two_iff` : the irreducible characters of `S_2` are the trivial
  character and the signature (Coq `repr_S2`).
-/

@[expose] public section

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
def JtGood (m : ℕ) (η : List ℕ) (s : Perm (Fin m)) : Prop :=
  ∀ i : Fin m, ((s i : ℕ) : ℤ) ≤ (η.getD (s i) 0 : ℤ) + (i : ℕ)

instance (m : ℕ) (η : List ℕ) (s : Perm (Fin m)) : Decidable (JtGood m η s) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- The list of indices of the complete homogeneous symmetric polynomials occurring in the
term of the Jacobi-Trudi determinant indexed by the permutation `s`. -/
def jtList (m : ℕ) (η : List ℕ) (s : Perm (Fin m)) : List ℕ :=
  List.ofFn fun i : Fin m => ((η.getD (s i) 0 : ℤ) + (i : ℕ) - (s i : ℕ)).toNat

/-- The integer coefficient of the term of the Jacobi-Trudi determinant indexed by `s`. -/
def jtCoeff (m : ℕ) (η : List ℕ) (s : Perm (Fin m)) : ℤ :=
  if JtGood m η s then (Equiv.Perm.sign s : ℤ) else 0

lemma prod_jtMatrix_of_jtGood {R : Type*} [CommRing R] (η : List ℕ) {s : Perm (Fin m)}
    (hs : JtGood m η s) :
    ∏ i : Fin m, jtMatrix m R η (s i) i = hProd m R (jtList m η s) := by
  rw [hProd, jtList, List.map_ofFn, List.prod_ofFn]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h0 : (0 : ℤ) ≤ (η.getD (s i) 0 : ℤ) + (i : ℕ) - (s i : ℕ) := by
    have := hs i; omega
  simp only [jtMatrix, Matrix.of_apply, Function.comp_apply]
  rw [hsymmInt, ite_eq_left h0]

lemma prod_jtMatrix_of_not_jtGood {R : Type*} [CommRing R] (η : List ℕ) {s : Perm (Fin m)}
    (hs : ¬ JtGood m η s) :
    ∏ i : Fin m, jtMatrix m R η (s i) i = 0 := by
  simp only [JtGood, not_forall, not_le] at hs
  obtain ⟨i, hi⟩ := hs
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  have hneg : (η.getD (s i) 0 : ℤ) + (i : ℕ) - (s i : ℕ) < 0 := by omega
  simp only [jtMatrix, Matrix.of_apply]
  exact hsymmInt_of_neg hneg

/-- Each list occurring in the Jacobi-Trudi expansion is a composition of `η.sum`. -/
lemma sum_jtList {η : List ℕ} (hlen : η.length ≤ m) {s : Perm (Fin m)}
    (hs : JtGood m η s) : (jtList m η s).sum = η.sum := by
  have key : ((jtList m η s).sum : ℤ) = (η.sum : ℤ) := by
    rw [jtList, List.sum_ofFn, Nat.cast_sum]
    rw [Finset.sum_congr rfl fun (i : Fin m) _ =>
      Int.toNat_of_nonneg (a := (η.getD (s i) 0 : ℤ) + (i : ℕ) - (s i : ℕ))
        (by have := hs i; omega)]
    have h1 : ∑ i : Fin m, ((η.getD (s i) 0 : ℤ) + (i : ℕ) - (s i : ℕ))
        = (∑ i : Fin m, (η.getD (s i) 0 : ℤ)) + (∑ i : Fin m, ((i : ℕ) : ℤ))
          - ∑ i : Fin m, ((s i : ℕ) : ℤ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have h2 : ∑ i : Fin m, (η.getD (s i) 0 : ℤ) = ∑ j : Fin m, (η.getD j 0 : ℤ) :=
      Equiv.sum_comp s fun j : Fin m => (η.getD j 0 : ℤ)
    have h3 : ∑ i : Fin m, ((s i : ℕ) : ℤ) = ∑ j : Fin m, ((j : ℕ) : ℤ) :=
      Equiv.sum_comp s fun j : Fin m => ((j : ℕ) : ℤ)
    rw [h1, h2, h3, add_sub_cancel_right, ← Nat.cast_sum, Fin.sum_univ_eq_sum_range
      (fun j => η.getD j 0), sum_range_getD_of_length_le hlen]
  exact_mod_cast key

/-- **The Jacobi-Trudi formula, expanded**: the Schur polynomial of a partition with at
most `m` parts is an integral combination of products of complete homogeneous symmetric
polynomials. -/
theorem schurPoly_eq_sum_jt {R : Type*} [CommRing R] {η : List ℕ} (hlam : IsPart η)
    (hlen : η.length ≤ m) :
    schurPoly (Fin m) R η = ∑ s : Perm (Fin m), jtCoeff m η s • hProd m R (jtList m η s) := by
  rw [schurPoly_eq_det_jtMatrix hlam hlen, Matrix.det_apply']
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : JtGood m η s
  · rw [prod_jtMatrix_of_jtGood η hs, jtCoeff, ite_eq_left hs, zsmul_eq_mul]
  · rw [prod_jtMatrix_of_not_jtGood η hs, jtCoeff, ite_eq_right hs, mul_zero, zero_smul]

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
    IsClassFun (c • f) := fun σ τ => by
  simp only [Pi.smul_apply, hf σ τ]

/-- A finite sum of class functions is a class function. -/
lemma isClassFun_sum {ι : Type*} (s : Finset ι) (F : ι → Perm (Fin n) → ℚ)
    (hF : ∀ i ∈ s, IsClassFun (F i)) : IsClassFun (∑ i ∈ s, F i) := fun σ τ => by
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i hi => hF i hi σ τ

/-- **The Schur class function is an integral combination of the permutation characters of
the Young subgroups.** -/
theorem schurChar_eq_sum_youngPermCharOf (η : PartIdx n n) :
    schurChar η
      = ∑ s : Perm (Fin n), jtCoeff n η.1 s • youngPermCharOf n (jtList n η.1 s) := by
  refine eq_of_frobChar_eq (isClassFun_schurChar η)
    (isClassFun_sum _ _ fun s _ => (youngPermCharOf_isClassFun n _).zsmul _) ?_
  rw [frobChar_schurChar, frobChar_sum, schurPoly_eq_sum_jt η.2.1 η.2.2.2]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [frobChar_zsmul]
  by_cases hs : JtGood n η.1 s
  · rw [frobChar_youngPermCharOf n _ (by rw [sum_jtList η.2.2.2 hs, η.2.2.1])]
  · rw [jtCoeff, ite_eq_right hs, zero_smul, zero_smul]

/-! ### The regular character -/

/-- The character of the regular representation of `S_n`, as a class function. -/
noncomputable def regChar (n : ℕ) : Perm (Fin n) → ℚ :=
  fun σ => if σ = 1 then (Nat.factorial n : ℚ) else 0

/-- The regular character is a class function. -/
lemma regChar_isClassFun : IsClassFun (regChar n) := by
  intro σ τ
  unfold regChar
  congr 1
  simp only [eq_iff_iff]
  constructor
  · intro h
    have : σ = τ * (τ⁻¹ * σ * τ) * τ⁻¹ := by group
    rw [this, h]
    group
  · intro h; rw [h]; group

/-- The Frobenius characteristic of the regular character. -/
lemma frobChar_regChar (k : ℕ) :
    frobChar k (regChar n) = pProd k ℚ (cycleTypeList (1 : Perm (Fin n))) := by
  rw [frobChar]
  have hterm : ∀ σ : Perm (Fin n), regChar n σ • pProd k ℚ (cycleTypeList σ)
      = if σ = 1 then (Nat.factorial n : ℚ) • pProd k ℚ (cycleTypeList (1 : Perm (Fin n)))
        else 0 := by
    intro σ
    unfold regChar
    split
    · next h => rw [h]
    · rw [zero_smul]
  rw [Finset.sum_congr rfl fun σ _ => hterm σ, Finset.sum_ite_eq' Finset.univ
    (1 : Perm (Fin n)) fun _ => (Nat.factorial n : ℚ) • pProd k ℚ
      (cycleTypeList (1 : Perm (Fin n))), ite_eq_left (Finset.mem_univ _), smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)), one_smul]

/-- **The regular character is the combination of the Schur class functions weighted by
their dimensions.** -/
theorem regChar_eq_sum_schurChar :
    regChar n = ∑ η : PartIdx n n, schurChar η 1 • schurChar η := by
  refine eq_of_frobChar_eq regChar_isClassFun
    (isClassFun_sum _ _ fun η _ => fun σ τ => by
      simp only [Pi.smul_apply, smul_eq_mul, isClassFun_schurChar η σ τ]) ?_
  rw [frobChar_regChar, frobChar_sum, pProd_cycleTypeList_eq_sum (1 : Perm (Fin n))]
  exact Finset.sum_congr rfl fun η _ => by rw [frobChar_smul, frobChar_schurChar]

/-! ### The Schur class functions with values in a field

The class functions above take rational values; representation theory needs them with values in
an algebraically closed field. Everything below is stated over an arbitrary algebraically closed
field `K` of characteristic zero. The classical statement is the case `K = ℂ`, obtained by
instantiating `K := ℂ`: the instance `Complex.isAlgClosed` lives in `Mathlib/Analysis/`, which
`Mathlib/RepresentationTheory/` may not import, so the specialisation is left to the user.

`K` lives in `Type` rather than `Type*` because `FDRep k G`, and hence `IsSimpleChar`, asks for
the field and the group to be in the same universe. -/

section Defs

variable (K : Type) [Field K] [CharZero K]

/-- The Schur class function of `S_n`, with values in a field of characteristic zero. -/
noncomputable def schurCharCast (η : PartIdx n n) : Perm (Fin n) → K :=
  fun σ => ((schurChar η σ : ℚ) : K)

/-- The regular character of `S_n`, with values in a field of characteristic zero. -/
noncomputable def regCharCast (n : ℕ) : Perm (Fin n) → K :=
  fun σ => ((regChar n σ : ℚ) : K)

instance neZero_natCast_card_perm (n : ℕ) : NeZero ((Nat.card (Perm (Fin n)) : K)) :=
  ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩

end Defs

section AlgClosed

variable {K : Type} [Field K] [CharZero K] [IsAlgClosed K]

/-- The permutation character of a Young subgroup, with values in `K`, is a virtual
character. -/
theorem isVirtualChar_youngPermCharOfCast (n : ℕ) (l : List ℕ) :
    IsVirtualChar (fun σ : Perm (Fin n) => ((youngPermCharOf n l σ : ℚ) : K)) := by
  by_cases h : l.sum = n
  · subst h
    have hv := isVirtualChar_card_fixedPoints K (G := Perm (Fin l.sum))
      (X := Perm (Fin l.sum) ⧸ youngSubgroup l)
    have heq : (fun σ : Perm (Fin l.sum) =>
        ((youngPermCharOf l.sum l σ : ℚ) : K))
        = fun σ : Perm (Fin l.sum) =>
          (Nat.card {q : Perm (Fin l.sum) ⧸ youngSubgroup l // σ • q = q} : K) := by
      funext σ
      rw [youngPermCharOf_self, youngPermChar]
      push_cast
      rfl
    rw [heq]
    exact hv
  · simp only [youngPermCharOf, dite_eq_right h, Pi.zero_apply, Rat.cast_zero]
    exact IsVirtualChar.zero

/-- **The Schur class function is a virtual character of `S_n` over `K`.** -/
theorem isVirtualChar_schurCharCast (η : PartIdx n n) :
    IsVirtualChar (schurCharCast K η) := by
  have heq : schurCharCast K η = ∑ s : Perm (Fin n), jtCoeff n η.1 s •
      fun σ : Perm (Fin n) => ((youngPermCharOf n (jtList n η.1 s) σ : ℚ) : K) := by
    funext σ
    rw [schurCharCast, schurChar_eq_sum_youngPermCharOf η]
    simp only [Finset.sum_apply, Pi.mul_apply, Pi.intCast_apply,
      zsmul_eq_mul, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast]
  rw [heq]
  exact IsVirtualChar.sum _ fun s _ => (isVirtualChar_youngPermCharOfCast n _).zsmul _

/-- A class function of the symmetric group takes the same value at a permutation and at
its inverse. -/
lemma IsClassFun.inv {f : Perm (Fin n) → ℚ} (hf : IsClassFun f) (σ : Perm (Fin n)) :
    f σ⁻¹ = f σ := by
  obtain ⟨u, hu⟩ := isConj_iff.1
    (Equiv.Perm.isConj_iff_cycleType_eq.2 (Equiv.Perm.cycleType_inv σ).symm)
  have hcl := hf σ u⁻¹
  rw [inv_inv] at hcl
  rw [← hu, hcl]

/-- The sum of the squares of the values of a Schur class function is `n !`. -/
lemma sum_sq_schurChar (η : PartIdx n n) :
    ∑ σ : Perm (Fin n), schurChar η σ * schurChar η σ
      = (Nat.factorial n : ℚ) := by
  have h := classInner_schurChar η η
  rw [ite_eq_left rfl, classInner] at h
  have hne : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have h2 : (Nat.factorial n : ℚ) * (((Nat.factorial n : ℚ))⁻¹ *
      ∑ σ : Perm (Fin n), schurChar η σ * schurChar η σ)
      = (Nat.factorial n : ℚ) * 1 := by rw [h]
  rwa [← mul_assoc, mul_inv_cancel₀ hne, one_mul, mul_one] at h2

omit [IsAlgClosed K] in
/-- **The Schur class function has norm one.** -/
theorem charBilin_schurCharCast (η : PartIdx n n) :
    charBilin (schurCharCast K η) (schurCharCast K η) = (Fintype.card (Perm (Fin n)) : K) := by
  have hterm : ∀ σ : Perm (Fin n), schurCharCast K η σ * schurCharCast K η σ⁻¹
      = ((schurChar η σ * schurChar η σ : ℚ) : K) := by
    intro σ
    simp only [schurCharCast]
    rw [(isClassFun_schurChar η).inv σ]
    push_cast
    ring
  rw [charBilin, Finset.sum_congr rfl fun σ _ => hterm σ, ← Rat.cast_sum,
    sum_sq_schurChar η, Fintype.card_perm, Fintype.card_fin]
  push_cast
  ring

/-- **The Schur class functions are the irreducible characters of the symmetric group**:
the class function `schurChar η`, viewed with values in an algebraically closed field `K` of
characteristic zero, is the character of a simple representation of `S_n` over `K`. -/
theorem isSimpleChar_schurCharCast (η : PartIdx n n) :
    IsSimpleChar (schurCharCast K η) := by
  obtain ⟨c, hc, hor⟩ := exists_isSimpleChar_of_norm_one (schurCharCast K η)
    (isVirtualChar_schurCharCast η) (charBilin_schurCharCast η)
  rcases hor with rfl | hneg
  · exact hc
  · exfalso
    obtain ⟨V, _, rfl⟩ := hc
    have h1 : schurCharCast K η 1 = (numStdTab η.1 : K) := by
      simp only [schurCharCast, schurChar_one η, Rat.cast_natCast]
    have h2 : ((numStdTab η.1 : ℕ) : K) = -((Module.finrank K V.V : ℕ) : K) := by
      rw [← h1, hneg, Pi.neg_apply, FDRep.char_one]
    have h3 : ((numStdTab η.1 + Module.finrank K V.V : ℕ) : K) = 0 := by
      push_cast
      rw [h2]
      ring
    have h4 : numStdTab η.1 + Module.finrank K V.V = 0 := by exact_mod_cast h3
    have := numStdTab_pos η.2.1
    omega

/-! ### Every irreducible character is a Schur class function -/

omit [IsAlgClosed K] in
/-- The regular character over `K` is the combination of the Schur class functions weighted
by their dimensions. -/
lemma regCharCast_eq_sum (n : ℕ) : regCharCast K n
    = fun g => ∑ η : PartIdx n n, ((schurChar η 1 : ℚ) : K) * schurCharCast K η g := by
  funext g
  rw [regCharCast, regChar_eq_sum_schurChar]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Rat.cast_sum, Rat.cast_mul,
    schurCharCast]

omit [CharZero K] [IsAlgClosed K] in
/-- The scalar product of a class function with the regular character. -/
lemma charBilin_regCharCast (χ : Perm (Fin n) → K) :
    charBilin χ (regCharCast K n) = (Nat.factorial n : K) * χ 1 := by
  rw [charBilin]
  rw [Finset.sum_eq_single (1 : Perm (Fin n))]
  · simp [regCharCast, regChar]
    ring
  · intro b _ hb
    have : b⁻¹ ≠ 1 := fun h => hb (by simpa using congrArg (·⁻¹) h)
    simp [regCharCast, regChar, this]
  · intro h
    exact absurd (Finset.mem_univ (1 : Perm (Fin n))) h

/-- **Every irreducible character of `S_n` over `K` is a Schur class function.** -/
theorem exists_eq_schurCharCast {χ : Perm (Fin n) → K} (h : IsSimpleChar χ) :
    ∃ η : PartIdx n n, χ = schurCharCast K η := by
  by_contra hcon
  push Not at hcon
  have hzero : charBilin χ (regCharCast K n) = 0 := by
    rw [regCharCast_eq_sum, charBilin_sum_right]
    refine Finset.sum_eq_zero fun η _ => ?_
    rw [charBilin_smul_right, charBilin_isSimpleChar h (isSimpleChar_schurCharCast η),
      ite_eq_right (hcon η), mul_zero]
  rw [charBilin_regCharCast] at hzero
  rcases mul_eq_zero.1 hzero with h1 | h1
  · exact (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)) h1
  · exact isSimpleChar_one_ne_zero h h1

omit [IsAlgClosed K] in
/-- The Schur class functions attached to distinct partitions are distinct. -/
theorem schurCharCast_injective (η μ : PartIdx n n)
    (h : schurCharCast K η = schurCharCast K μ) : η = μ := by
  by_contra hne
  have h0 : classInner (schurChar η) (schurChar μ) = 0 := by
    rw [classInner_schurChar, ite_eq_right hne]
  have h1 : classInner (schurChar η) (schurChar η) = 1 := by
    rw [classInner_schurChar, ite_eq_left rfl]
  have hq : schurChar η = schurChar μ := by
    funext σ
    have := congrFun h σ
    simp only [schurCharCast] at this
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
theorem isSimpleChar_perm_two_iff {χ : Perm (Fin 2) → K} :
    IsSimpleChar χ ↔
      χ = (fun _ => 1) ∨ χ = fun σ => ((Equiv.Perm.sign σ : ℤ) : K) := by
  have hrow : schurCharCast K rowIdxTwo = fun _ : Perm (Fin 2) => (1 : K) := by
    funext σ
    rw [schurCharCast, schurChar_row (by norm_num) rowIdxTwo rfl]
    norm_num
  have hcol : schurCharCast K colIdxTwo
      = fun σ : Perm (Fin 2) => ((Equiv.Perm.sign σ : ℤ) : K) := by
    funext σ
    rw [schurCharCast, schurChar_column colIdxTwo (by rfl)]
    norm_num
  constructor
  · intro h
    obtain ⟨η, rfl⟩ := exists_eq_schurCharCast h
    rcases eq_of_isPart_sum_two η.2.1 η.2.2.1 with hlam | hlam
    · exact Or.inl (by rw [show η = rowIdxTwo from Subtype.ext hlam, hrow])
    · exact Or.inr (by rw [show η = colIdxTwo from Subtype.ext hlam, hcol])
  · rintro (rfl | rfl)
    · rw [← hrow]; exact isSimpleChar_schurCharCast rowIdxTwo
    · rw [← hcol]; exact isSimpleChar_schurCharCast colIdxTwo

end AlgClosed

end Equiv.Perm
