/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.RepresentationTheory.CharacterTheory.PermutationRepresentation
import Mathlib.RepresentationTheory.SymmetricGroup.FrobeniusCharacteristic

/-!
# Young subgroups and the permutation module of a Young subgroup

The Young subgroup `S_{l_1} × ⋯ × S_{l_r}` of `S_{l_1 + ⋯ + l_r}`, as the image of the
iterated injection `Equiv.Perm.tinj`, and the computation of the Frobenius characteristic of the
permutation character of the action of `S_n` on the cosets of a Young subgroup: it is the
product `h_{l_1} ⋯ h_{l_r}` of complete homogeneous symmetric polynomials.  This realises
the class function `Equiv.Perm.indTrivYoung` as the character of an actual representation.

## Main definitions

* `Equiv.Perm.youngSubgroup l` : the Young subgroup of `S_{l.sum}` attached to a list `l`.
* `Equiv.Perm.youngPermChar l` : the number of cosets of the Young subgroup fixed by a
  permutation, as a class function.

## Main results

* `Equiv.Perm.card_youngSubgroup` : the Young subgroup has `l_1 ! ⋯ l_r !` elements.
* `Equiv.Perm.sum_pProd_youngSubgroup` : `∑_{h ∈ H_l} p_{cycleType h} = l_1 ! ⋯ l_r ! · h_l`.
* `Equiv.Perm.frobChar_youngPermChar` : the Frobenius characteristic of the permutation
  character of `S_n` on the cosets of the Young subgroup `H_l` is `h_l`.
-/

open Equiv MvPolynomial

namespace Equiv.Perm


/-! ### The Young subgroup -/

/-- The Young subgroup `S_{l_1} × ⋯ × S_{l_r}` of `S_{l.sum}`, defined as the image of the
iterated injection `Equiv.Perm.tinj`. -/
def youngSubgroup : (l : List ℕ) → Subgroup (Perm (Fin l.sum))
  | [] => ⊤
  | a :: t => Subgroup.map (tinj a t.sum) ((⊤ : Subgroup (Perm (Fin a))).prod (youngSubgroup t))

/-- The Young subgroup attached to `l` has `l_1 ! ⋯ l_r !` elements. -/
theorem card_youngSubgroup (l : List ℕ) :
    Nat.card (youngSubgroup l) = (l.map Nat.factorial).prod := by
  induction l with
  | nil => simp [youngSubgroup, Nat.card_eq_fintype_card]
  | cons a t ih =>
    have e1 : youngSubgroup (a :: t) ≃ ((⊤ : Subgroup (Perm (Fin a))).prod (youngSubgroup t)) :=
      (Subgroup.equivMapOfInjective _ _ (tinj_injective a t.sum)).symm.toEquiv
    have e2 : ((⊤ : Subgroup (Perm (Fin a))).prod (youngSubgroup t))
        ≃ (Perm (Fin a) × youngSubgroup t) :=
      (Subgroup.prodEquiv _ _).toEquiv.trans
        (Equiv.prodCongr Subgroup.topEquiv.toEquiv (Equiv.refl _))
    rw [Nat.card_congr (e1.trans e2), Nat.card_prod, ih, List.map_cons, List.prod_cons,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

/-- Any subgroup of a finite group is a `Fintype` (noncomputably). -/
noncomputable instance (priority := 50) instFintypeSubgroupOfFinite {G : Type*} [Group G]
    [Finite G] (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite _

/-- The sum of the power sum products over a Young subgroup. -/
theorem sum_pProd_youngSubgroup (k : ℕ) (l : List ℕ) :
    ∑ h : youngSubgroup l, pProd k ℚ (cycleTypeList (h : Perm (Fin l.sum)))
      = ((l.map Nat.factorial).prod : ℚ) • hProd k ℚ l := by
  induction l with
  | nil =>
    have h0 : ∑ sigma : Perm (Fin 0), pProd k ℚ (cycleTypeList sigma) = 1 := by
      have h := factorial_nsmul_hsymm_eq_sum_perm k 0 ℚ
      simpa using h.symm
    have hsum : ∑ h : youngSubgroup ([] : List ℕ),
        pProd k ℚ (cycleTypeList (h : Perm (Fin ([] : List ℕ).sum)))
        = ∑ sigma : Perm (Fin 0), pProd k ℚ (cycleTypeList sigma) :=
      Fintype.sum_equiv Subgroup.topEquiv.toEquiv _ _ fun _ => rfl
    rw [hsum, h0]
    simp
  | cons a t ih =>
    have hinj := tinj_injective a t.sum
    have step1 : ∑ x : ((⊤ : Subgroup (Perm (Fin a))).prod (youngSubgroup t)),
          pProd k ℚ (cycleTypeList (tinj a t.sum (x : Perm (Fin a) × Perm (Fin t.sum))))
        = ∑ h : youngSubgroup (a :: t), pProd k ℚ (cycleTypeList (h : Perm (Fin (a :: t).sum))) :=
      Fintype.sum_equiv (Subgroup.equivMapOfInjective _ _ hinj).toEquiv _ _ fun x => by
        simp [Subgroup.coe_equivMapOfInjective_apply]
    have step2 : ∑ x : ((⊤ : Subgroup (Perm (Fin a))).prod (youngSubgroup t)),
          pProd k ℚ (cycleTypeList (tinj a t.sum (x : Perm (Fin a) × Perm (Fin t.sum))))
        = ∑ y : Perm (Fin a) × youngSubgroup t,
          pProd k ℚ (cycleTypeList (tinj a t.sum (y.1, (y.2 : Perm (Fin t.sum))))) :=
      Fintype.sum_equiv
        ({ toFun := fun x => ((x : Perm (Fin a) × Perm (Fin t.sum)).1,
            ⟨(x : Perm (Fin a) × Perm (Fin t.sum)).2, (Subgroup.mem_prod.1 x.2).2⟩)
           invFun := fun y => ⟨(y.1, (y.2 : Perm (Fin t.sum))),
            Subgroup.mem_prod.2 ⟨trivial, y.2.2⟩⟩
           left_inv := fun x => Subtype.ext rfl
           right_inv := fun y => rfl } :
          ((⊤ : Subgroup (Perm (Fin a))).prod (youngSubgroup t))
            ≃ (Perm (Fin a) × youngSubgroup t)) _ _ fun x => rfl
    have step3 : ∑ y : Perm (Fin a) × youngSubgroup t,
          pProd k ℚ (cycleTypeList (tinj a t.sum (y.1, (y.2 : Perm (Fin t.sum)))))
        = (∑ u : Perm (Fin a), pProd k ℚ (cycleTypeList u))
          * ∑ v : youngSubgroup t, pProd k ℚ (cycleTypeList (v : Perm (Fin t.sum))) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
        pProd_cycleTypeList_tinj k ℚ u (v : Perm (Fin t.sum))
    have ha : ∑ u : Perm (Fin a), pProd k ℚ (cycleTypeList u)
        = ((Nat.factorial a : ℚ)) • hsymm (Fin k) ℚ a := by
      rw [Nat.cast_smul_eq_nsmul ℚ]
      exact (factorial_nsmul_hsymm_eq_sum_perm k a ℚ).symm
    rw [← step1, step2, step3, ha, ih, smul_mul_smul_comm, List.map_cons, List.prod_cons]
    push_cast
    simp [hProd]

/-! ### The permutation character of a Young subgroup -/

/-- The number of cosets of the Young subgroup `H_l` fixed by a permutation. -/
noncomputable def youngPermChar (l : List ℕ) (sigma : Perm (Fin l.sum)) : ℚ :=
  (Nat.card {q : Perm (Fin l.sum) ⧸ youngSubgroup l // sigma • q = q} : ℚ)

/-- The number of fixed cosets is a class function. -/
theorem youngPermChar_isClassFun (l : List ℕ) : IsClassFun (youngPermChar l) := by
  intro sigma tau
  refine congrArg Nat.cast (Nat.card_congr ?_)
  refine
    { toFun := fun q => ⟨tau • (q : Perm (Fin l.sum) ⧸ youngSubgroup l), ?_⟩
      invFun := fun q => ⟨tau⁻¹ • (q : Perm (Fin l.sum) ⧸ youngSubgroup l), ?_⟩
      left_inv := fun q => ?_
      right_inv := fun q => ?_ }
  · rw [← mul_smul, show sigma * tau = tau * (tau⁻¹ * sigma * tau) by group, mul_smul, q.2]
  · rw [← mul_smul, show tau⁻¹ * sigma * tau * tau⁻¹ = tau⁻¹ * sigma by group, mul_smul, q.2]
  · exact Subtype.ext (by simp [← mul_smul])
  · exact Subtype.ext (by simp [← mul_smul])

/-- **The Frobenius characteristic of the permutation character of a Young subgroup** is
the product `h_l = h_{l_1} ⋯ h_{l_r}`. -/
theorem frobChar_youngPermChar (k : ℕ) (l : List ℕ) :
    frobChar k (youngPermChar l) = hProd k ℚ l := by
  have hclass : ∀ a b : Perm (Fin l.sum),
      pProd k ℚ (cycleTypeList (b⁻¹ * a * b)) = pProd k ℚ (cycleTypeList a) := by
    intro a b
    rw [cycleTypeList_conj]
  have hmain := FDRep.sum_card_fixedPoints_quotient_mul (youngSubgroup l)
    (fun sigma => pProd k ℚ (cycleTypeList sigma)) hclass
  have hlagrange : Nat.card (Perm (Fin l.sum) ⧸ youngSubgroup l) * (l.map Nat.factorial).prod
      = Nat.factorial l.sum := by
    rw [← card_youngSubgroup l, ← Subgroup.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rw [frobChar]
  have hterm : ∀ sigma : Perm (Fin l.sum), youngPermChar l sigma • pProd k ℚ (cycleTypeList sigma)
      = (Nat.card {q : Perm (Fin l.sum) ⧸ youngSubgroup l // sigma • q = q} :
          MvPolynomial (Fin k) ℚ) * pProd k ℚ (cycleTypeList sigma) := by
    intro sigma
    rw [youngPermChar, Nat.cast_smul_eq_nsmul ℚ, nsmul_eq_mul]
  rw [Finset.sum_congr rfl fun sigma _ => hterm sigma, hmain,
    sum_pProd_youngSubgroup k l, Nat.cast_smul_eq_nsmul ℚ, nsmul_eq_mul, ← mul_assoc,
    ← Nat.cast_mul, hlagrange, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)), one_smul]

/-! ### Transporting along an equality of degrees -/

/-- The permutation character of the Young subgroup attached to a composition `l` of `n`,
as a class function on `S_n`; junk (zero) if `l` is not a composition of `n`. -/
noncomputable def youngPermCharOf (n : ℕ) (l : List ℕ) : Perm (Fin n) → ℚ :=
  if h : l.sum = n then h ▸ youngPermChar l else 0

@[simp]
lemma youngPermCharOf_self (l : List ℕ) : youngPermCharOf l.sum l = youngPermChar l := by
  simp [youngPermCharOf]

/-- The Frobenius characteristic of the permutation character of a Young subgroup. -/
theorem frobChar_youngPermCharOf (k : ℕ) {n : ℕ} (l : List ℕ) (h : l.sum = n) :
    frobChar k (youngPermCharOf n l) = hProd k ℚ l := by
  subst h
  rw [youngPermCharOf_self, frobChar_youngPermChar]

/-- The permutation character of a Young subgroup is a class function. -/
theorem youngPermCharOf_isClassFun (n : ℕ) (l : List ℕ) : IsClassFun (youngPermCharOf n l) := by
  unfold youngPermCharOf
  split
  · next h => subst h; exact youngPermChar_isClassFun l
  · intro _ _; rfl

end Equiv.Perm
