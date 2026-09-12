/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.CycleIndex
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.Omega

/-!
# The involution `omega` is multiplicative, and its action on the power sums

Following `theories/MPoly/sympoly.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove that the involution `omega`
is multiplicative and that it acts on the power sums by
`omega p_μ = (-1)^(|μ| - length μ) p_μ`.

## Main results

* `MvPolynomial.omegaSym_mul` : `omega` is multiplicative.
* `MvPolynomial.omegaSym_psum` : `omega p_r = (-1)^(r+1) p_r`.
* `MvPolynomial.omegaSym_pSub` : `omega p_μ = (-1)^(|μ| - length μ) p_μ`.
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial

variable {m n a b : ℕ} {R : Type*}

/-! ### Merging two partitions -/

/-- The partition obtained by merging the parts of two partitions. -/
noncomputable def mergePart (μ ν : List ℕ) : List ℕ :=
  sortDesc ((μ : Multiset ℕ) + (ν : Multiset ℕ))

lemma coe_mergePart (μ ν : List ℕ) :
    ((mergePart μ ν : List ℕ) : Multiset ℕ) = ((μ ++ ν : List ℕ) : Multiset ℕ) := by
  rw [mergePart, coe_sortDesc]
  simp

lemma mergePart_perm (μ ν : List ℕ) : (mergePart μ ν).Perm (μ ++ ν) :=
  Quotient.exact (coe_mergePart μ ν)

lemma isPart_mergePart {μ ν : List ℕ} (hμ : IsPart μ) (hν : IsPart ν) :
    IsPart (mergePart μ ν) := by
  refine isPart_sortDesc fun i hi => ?_
  rcases Multiset.mem_add.1 hi with h | h
  · exact hμ.pos_of_mem (by simpa using h)
  · exact hν.pos_of_mem (by simpa using h)

@[simp] lemma sum_mergePart (μ ν : List ℕ) :
    (mergePart μ ν).sum = μ.sum + ν.sum := by
  rw [(mergePart_perm μ ν).sum_eq, List.sum_append]

@[simp] lemma length_mergePart (μ ν : List ℕ) :
    (mergePart μ ν).length = μ.length + ν.length := by
  rw [(mergePart_perm μ ν).length_eq, List.length_append]

/-! ### Products of complete homogeneous and elementary symmetric polynomials -/

lemma hProd_of_perm (m : ℕ) (R : Type*) [CommRing R] {l l' : List ℕ} (h : l.Perm l') :
    hProd m R l = hProd m R l' :=
  List.Perm.prod_eq (h.map _)

lemma hProd_append (m : ℕ) (R : Type*) [CommRing R] (l l' : List ℕ) :
    hProd m R (l ++ l') = hProd m R l * hProd m R l' := by
  rw [hProd, hProd, hProd, List.map_append, List.prod_append]

lemma hProd_mergePart (m : ℕ) (R : Type*) [CommRing R] (μ ν : List ℕ) :
    hProd m R (mergePart μ ν) = hProd m R μ * hProd m R ν := by
  rw [hProd_of_perm m R (mergePart_perm μ ν), hProd_append]

lemma eProd_of_perm (m : ℕ) (R : Type*) [CommRing R] {l l' : List ℕ} (h : l.Perm l') :
    eProd m R l = eProd m R l' :=
  List.Perm.prod_eq (h.map _)

lemma eProd_append (m : ℕ) (R : Type*) [CommRing R] (l l' : List ℕ) :
    eProd m R (l ++ l') = eProd m R l * eProd m R l' := by
  rw [eProd, eProd, eProd, List.map_append, List.prod_append]

lemma eProd_mergePart (m : ℕ) (R : Type*) [CommRing R] (μ ν : List ℕ) :
    eProd m R (mergePart μ ν) = eProd m R μ * eProd m R ν := by
  rw [eProd_of_perm m R (mergePart_perm μ ν), eProd_append]

/-! ### `omega` is multiplicative -/

lemma mul_mem_symHomogeneousSubmodule [CommRing R] {f g : MvPolynomial (Fin m) R}
    (hf : f ∈ symHomogeneousSubmodule m a R) (hg : g ∈ symHomogeneousSubmodule m b R) :
    f * g ∈ symHomogeneousSubmodule m (a + b) R :=
  ⟨hf.1.mul hg.1, hf.2.mul hg.2⟩

/-- The product of two homogeneous symmetric polynomials, as an element of the homogeneous
component of the sum of the degrees. -/
noncomputable def mulSub (m : ℕ) (R : Type*) [CommRing R] (hab : a + b = n) :
    symHomogeneousSubmodule m a R →ₗ[R] symHomogeneousSubmodule m b R →ₗ[R]
      symHomogeneousSubmodule m n R :=
  LinearMap.mk₂ R
    (fun f g => ⟨(f : MvPolynomial (Fin m) R) * g,
      hab ▸ mul_mem_symHomogeneousSubmodule f.2 g.2⟩)
    (by intro f₁ f₂ g; apply Subtype.ext; simp [add_mul])
    (by intro c f g; apply Subtype.ext; simp)
    (by intro f g₁ g₂; apply Subtype.ext; simp [mul_add])
    (by intro c f g; apply Subtype.ext; simp)

@[simp] lemma coe_mulSub [CommRing R] (hab : a + b = n)
    (f : symHomogeneousSubmodule m a R) (g : symHomogeneousSubmodule m b R) :
    (mulSub m R hab f g : MvPolynomial (Fin m) R)
      = (f : MvPolynomial (Fin m) R) * (g : MvPolynomial (Fin m) R) := rfl

@[simp] lemma hBasis_apply (m n : ℕ) (R : Type*) [CommRing R] (μ : PartLengthLe n m) :
    hBasis m n R μ = hSub m n R μ := by
  rw [hBasis, Module.Basis.mk_apply]

/-- **`omega` is multiplicative**. -/
theorem omegaSym_mul [CommRing R] (hab : a + b = n) (hnm : n ≤ m)
    (f : symHomogeneousSubmodule m a R) (g : symHomogeneousSubmodule m b R) :
    (omegaSym m n R hnm (mulSub m R hab f g) : MvPolynomial (Fin m) R)
      = (omegaSym m a R (by omega) f : MvPolynomial (Fin m) R)
        * (omegaSym m b R (by omega) g : MvPolynomial (Fin m) R) := by
  have ha : a ≤ m := by omega
  have hb : b ≤ m := by omega
  set L : symHomogeneousSubmodule m n R →ₗ[R] MvPolynomial (Fin m) R :=
    (symHomogeneousSubmodule m n R).subtype ∘ₗ (omegaSym m n R hnm).toLinearMap with hL
  set Phi : symHomogeneousSubmodule m a R →ₗ[R] symHomogeneousSubmodule m b R →ₗ[R]
      MvPolynomial (Fin m) R := LinearMap.compr₂ (mulSub m R hab) L with hPhi
  set Psi : symHomogeneousSubmodule m a R →ₗ[R] symHomogeneousSubmodule m b R →ₗ[R]
      MvPolynomial (Fin m) R :=
    LinearMap.mk₂ R
      (fun f g => (omegaSym m a R ha f : MvPolynomial (Fin m) R)
        * (omegaSym m b R hb g : MvPolynomial (Fin m) R))
      (by intro f₁ f₂ g; simp [add_mul])
      (by intro c f g; simp)
      (by intro f g₁ g₂; simp [mul_add])
      (by intro c f g; simp) with hPsi
  have key : Phi = Psi := by
    refine (hBasis m a R).ext fun μ => (hBasis m b R).ext fun ν => ?_
    have hρ : IsPart (mergePart μ.1 ν.1) ∧ (mergePart μ.1 ν.1).sum = n ∧
        (mergePart μ.1 ν.1).length ≤ m := by
      refine ⟨isPart_mergePart μ.2.1 ν.2.1, by rw [sum_mergePart, μ.2.2.1, ν.2.2.1, hab],
        ?_⟩
      rw [length_mergePart]
      have h1 := μ.2.1.length_le_sum
      have h2 := ν.2.1.length_le_sum
      rw [μ.2.2.1] at h1
      rw [ν.2.2.1] at h2
      omega
    set ρ : PartLengthLe n m := ⟨mergePart μ.1 ν.1, hρ⟩ with hρdef
    have hmul : mulSub m R hab (hSub m a R μ) (hSub m b R ν) = hSub m n R ρ := by
      apply Subtype.ext
      rw [coe_mulSub, coe_hSub, coe_hSub, coe_hSub, hρdef, hProd_mergePart]
    simp only [hBasis_apply, hPhi, hPsi, LinearMap.compr₂_apply, LinearMap.mk₂_apply, hL,
      LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype]
    rw [hmul, omegaSym_hSub, omegaSym_hSub, omegaSym_hSub, coe_eSubOfPart, coe_eSubOfPart,
      coe_eSubOfPart, hρdef, eProd_mergePart]
  have := LinearMap.congr_fun (LinearMap.congr_fun key f) g
  simpa [hPhi, hPsi, hL] using this

/-! ### The one-part partitions -/

/-- The partition of `k` with a single part, as an index. -/
def rowPart (m k : ℕ) (hkm : k ≤ m) : PartLengthLe k m :=
  ⟨rowShape k, isPart_rowShape k, sum_rowShape k, by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [rowShape]
    · exact le_trans (length_rowShape_le k) (by omega)⟩

@[simp] lemma rowPart_val (m k : ℕ) (hkm : k ≤ m) : (rowPart m k hkm).1 = rowShape k := rfl

@[simp] lemma hProd_rowShape (m : ℕ) (R : Type*) [CommRing R] (k : ℕ) :
    hProd m R (rowShape k) = hsymm (Fin m) R k := by
  rw [rowShape]
  split
  · next h => rw [h, hProd_nil, hsymm_zero]
  · rw [hProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

@[simp] lemma eProd_rowShape (m : ℕ) (R : Type*) [CommRing R] (k : ℕ) :
    eProd m R (rowShape k) = esymm (Fin m) R k := by
  rw [rowShape]
  split
  · next h => rw [h, eProd_nil, esymm_zero]
  · rw [eProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

lemma pProd_rowShape (m : ℕ) (R : Type*) [CommRing R] {k : ℕ} (hk : 0 < k) :
    pProd m R (rowShape k) = psum (Fin m) R k := by
  rw [rowShape, ite_eq_right hk.ne', pProd, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]

/-! ### The action of `omega` on the power sums -/

/-- **`omega` acts on the power sums by the sign `(-1)^(r+1)`**, by strong induction on the
degree. -/
private theorem omegaSym_psum_aux (m : ℕ) (R : Type*) [CommRing R] :
    ∀ r : ℕ, 0 < r → ∀ hrm : r ≤ m,
      (omegaSym m r R hrm (pSub m r R (rowPart m r hrm)) : MvPolynomial (Fin m) R)
        = (-1) ^ (r + 1) * psum (Fin m) R r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r IH =>
  intro hr hrm
  classical
  set T : ℕ → symHomogeneousSubmodule m r R := fun j =>
    if h : 1 ≤ j ∧ j ≤ r then
      mulSub m R (show j + (r - j) = r by omega)
        (pSub m j R (rowPart m j (by omega)))
        (hSub m (r - j) R (rowPart m (r - j) (by omega)))
    else 0 with hT
  have hTcoe : ∀ j ∈ Finset.Icc 1 r,
      (T j : MvPolynomial (Fin m) R) = psum (Fin m) R j * hsymm (Fin m) R (r - j) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [hT]
    simp only [dite_eq_left (⟨hj.1, hj.2⟩ : 1 ≤ j ∧ j ≤ r), coe_mulSub, coe_pSub, coe_hSub,
      rowPart_val, hProd_rowShape]
    rw [pProd_rowShape m R (show 0 < j by omega)]
  have hA : (r : ℕ) • hSub m r R (rowPart m r hrm) = ∑ j ∈ Finset.Icc 1 r, T j := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_nsmul, coe_hSub, rowPart_val, hProd_rowShape, Submodule.coe_sum,
      Finset.sum_congr rfl hTcoe]
    exact nsmul_hsymm_eq_sum_psum_mul_hsymm m r R
  have hB : (r : ℕ) • esymm (Fin m) R r
      = ∑ j ∈ Finset.Icc 1 r, (omegaSym m r R hrm (T j) : MvPolynomial (Fin m) R) := by
    have hcong := congrArg
      (fun x : symHomogeneousSubmodule m r R =>
        ((omegaSym m r R hrm x : symHomogeneousSubmodule m r R) : MvPolynomial (Fin m) R))
      hA
    simp only [map_nsmul, map_sum, AddSubmonoidClass.coe_nsmul, Submodule.coe_sum,
      omegaSym_hSub, coe_eSubOfPart, rowPart_val, eProd_rowShape] at hcong
    exact hcong
  have hTomega : ∀ j ∈ (Finset.Icc 1 r).erase r,
      (omegaSym m r R hrm (T j) : MvPolynomial (Fin m) R)
        = (-1 : MvPolynomial (Fin m) R) ^ (j + 1)
            * (psum (Fin m) R j * esymm (Fin m) R (r - j)) := by
    intro j hj
    have hne : j ≠ r := (Finset.mem_erase.1 hj).1
    have hj' := Finset.mem_Icc.1 (Finset.mem_erase.1 hj).2
    have hjr : j < r := lt_of_le_of_ne hj'.2 hne
    rw [hT]
    simp only [dite_eq_left (⟨hj'.1, hj'.2⟩ : 1 ≤ j ∧ j ≤ r)]
    rw [omegaSym_mul, IH j hjr (by omega) (by omega), omegaSym_hSub, coe_eSubOfPart,
      rowPart_val, eProd_rowShape, mul_assoc]
  have hTr : (omegaSym m r R hrm (T r) : MvPolynomial (Fin m) R)
      = (omegaSym m r R hrm (pSub m r R (rowPart m r hrm)) : MvPolynomial (Fin m) R) := by
    have hTreq : T r = pSub m r R (rowPart m r hrm) := by
      rw [hT]
      simp only [dite_eq_left (⟨hr, le_refl r⟩ : 1 ≤ r ∧ r ≤ r)]
      apply Subtype.ext
      rw [coe_mulSub, coe_hSub, rowPart_val, Nat.sub_self, hProd_rowShape, hsymm_zero,
        mul_one, coe_pSub]
    rw [hTreq]
  have hmemr : r ∈ Finset.Icc 1 r := Finset.mem_Icc.2 ⟨hr, le_refl r⟩
  have hkey : (omegaSym m r R hrm (T r) : MvPolynomial (Fin m) R)
      = (-1 : MvPolynomial (Fin m) R) ^ (r + 1) * (psum (Fin m) R r * esymm (Fin m) R (r - r)) := by
    have h1 := hB
    rw [nsmul_esymm_eq_sum_psum_mul_esymm m r R] at h1
    rw [← Finset.add_sum_erase _ _ hmemr, ← Finset.add_sum_erase _ _ hmemr,
      Finset.sum_congr rfl hTomega] at h1
    exact (add_right_cancel h1.symm)
  rw [← hTr, hkey, Nat.sub_self, esymm_zero, mul_one]

/-- **`omega` acts on the power sums by the sign `(-1)^(r+1)`**. -/
theorem omegaSym_psum (m : ℕ) (R : Type*) [CommRing R] {r : ℕ} (hr : 0 < r) (hrm : r ≤ m) :
    (omegaSym m r R hrm (pSub m r R (rowPart m r hrm)) : MvPolynomial (Fin m) R)
      = (-1) ^ (r + 1) * psum (Fin m) R r :=
  omegaSym_psum_aux m R r hr hrm

/-! ### The action of `omega` on the products of power sums -/

/-- **`omega` acts on the products of power sums by the sign
`(-1)^(|μ| - length μ)`**, in terms of a partition given as a list. -/
theorem omegaSym_pProd (m : ℕ) (R : Type*) [CommRing R] (μ : List ℕ) :
    ∀ (hμ : IsPart μ) (hle : μ.sum ≤ m),
      (omegaSym m μ.sum R hle
          (pSub m μ.sum R ⟨μ, hμ, rfl, le_trans hμ.length_le_sum hle⟩)
        : MvPolynomial (Fin m) R)
        = (-1) ^ (μ.sum - μ.length) * pProd m R μ := by
  induction μ with
  | nil =>
    intro hμ hle
    have hpe : (pSub m ([] : List ℕ).sum R ⟨[], hμ, rfl, le_trans hμ.length_le_sum hle⟩)
        = hSub m ([] : List ℕ).sum R ⟨[], hμ, rfl, le_trans hμ.length_le_sum hle⟩ := by
      apply Subtype.ext
      rw [coe_pSub, coe_hSub]
      rfl
    rw [hpe, omegaSym_hSub, coe_eSubOfPart]
    simp
  | cons a l ih =>
    intro hμ hle
    have hlpart : IsPart l := hμ.of_cons
    have hsum : (a :: l).sum = a + l.sum := List.sum_cons
    have hle' : l.sum ≤ m := by omega
    have ha : 0 < a := hμ.pos_of_mem (List.mem_cons_self ..)
    have ham : a ≤ m := by omega
    have hab : a + l.sum = (a :: l).sum := hsum.symm
    have hmul : (pSub m (a :: l).sum R
          ⟨a :: l, hμ, rfl, le_trans hμ.length_le_sum hle⟩)
        = mulSub m R hab (pSub m a R (rowPart m a ham))
            (pSub m l.sum R ⟨l, hlpart, rfl, le_trans hlpart.length_le_sum hle'⟩) := by
      apply Subtype.ext
      rw [coe_mulSub, coe_pSub, coe_pSub, coe_pSub, rowPart_val, pProd_rowShape m R ha,
        pProd_cons]
    rw [hmul, omegaSym_mul, omegaSym_psum m R ha ham, ih hlpart hle']
    have hlen : l.length ≤ l.sum := hlpart.length_le_sum
    have hexp : (a + 1) + (l.sum - l.length)
        = ((a :: l).sum - (a :: l).length) + 2 := by
      rw [hsum, List.length_cons]
      omega
    rw [pProd_cons, mul_mul_mul_comm, ← pow_add, hexp, pow_add]
    ring

/-- **`omega` acts on the products of power sums by the sign
`(-1)^(|μ| - length μ)`**. -/
theorem omegaSym_pSub (m n : ℕ) (R : Type*) [CommRing R] (hnm : n ≤ m) (μ : PartLengthLe n m) :
    (omegaSym m n R hnm (pSub m n R μ) : MvPolynomial (Fin m) R)
      = (-1) ^ (n - μ.1.length) * pProd m R μ.1 := by
  obtain ⟨l, hpart, hsum, hlen⟩ := μ
  subst hsum
  exact omegaSym_pProd m R l hpart hnm

end MvPolynomial
