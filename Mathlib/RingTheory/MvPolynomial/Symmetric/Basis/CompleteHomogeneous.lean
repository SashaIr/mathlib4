/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.Basis
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.Pieri

/-!
# The products of complete homogeneous symmetric polynomials form a basis

Following `theories/MPoly/sympoly.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove the expansion of a product
`h_μ = h_{μ_1} * ... * h_{μ_k}` of complete homogeneous symmetric polynomials in the
basis of Schur polynomials, `h_μ = ∑_ν K_{ν μ} s_ν`, where `K_{ν μ}` is the
Kostka number counting the tableaux of shape `ν` and content `μ`.  Since the Kostka
numbers are unitriangular for the dominance order, the polynomials `h_μ`, for `μ` a
partition of `n` with at most `m` parts, form a basis of the module of symmetric
homogeneous polynomials of degree `n` in `m` variables.

## Main results

* `MvPolynomial.hProd_eq_sum_kostka` : `h_μ = ∑_ν K_{ν μ} s_ν`.
* `MvPolynomial.linearIndependent_hProd` : the `h_μ` are linearly independent.
* `MvPolynomial.span_hProd` : they span the symmetric homogeneous polynomials of degree `n`.
* `MvPolynomial.hBasis` : the resulting basis.
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial

variable {m : ℕ} {R : Type*}

/-! ### Kostka numbers: elementary properties -/

/-- There is exactly one tableau of empty shape, and it has empty content. -/
lemma kostkaNum_nil {N : ℕ} {c : ℕ → ℕ} (h : ∀ i, i < N → c i = 0) :
    kostkaNum N [] c = 1 := by
  rw [kostkaNum, Nat.card_eq_one_iff_exists]
  refine ⟨⟨[], ?_⟩, ?_⟩
  · refine ⟨?_, rfl, by simp, fun i hi => by simpa using (h i hi).symm⟩
    simp [IsTableau]
  · rintro ⟨P, hP, hμ, -, -⟩
    refine Subtype.ext ?_
    have : P.map List.length = [] := hμ
    simpa using this

/-! ### The content of a list, as a function -/

/-- The content function attached to a list: `i ↦ μ.getD i 0`. -/
def contentOf (μ : List ℕ) : ℕ → ℕ := fun i => μ.getD i 0

@[simp] lemma contentOf_apply (μ : List ℕ) (i : ℕ) : contentOf μ i = μ.getD i 0 := rfl

lemma contentOf_append_singleton_of_lt {μ : List ℕ} {r i : ℕ} (hi : i < μ.length) :
    contentOf (μ ++ [r]) i = contentOf μ i := by
  simp [contentOf, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma contentOf_append_singleton_self (μ : List ℕ) (r : ℕ) :
    contentOf (μ ++ [r]) μ.length = r := by
  simp [contentOf, List.getD_eq_getElem?_getD]

/-! ### The product of complete homogeneous symmetric polynomials -/

/-- The product `h_μ = h_{μ_1} * ... * h_{μ_k}` of complete homogeneous symmetric
polynomials attached to a list `μ`. -/
noncomputable def hProd (m : ℕ) (R : Type*) [CommRing R] (μ : List ℕ) :
    MvPolynomial (Fin m) R := (μ.map (hsymm (Fin m) R)).prod

@[simp] lemma hProd_nil (m : ℕ) (R : Type*) [CommRing R] : hProd m R [] = 1 := rfl

lemma hProd_append_singleton (m : ℕ) (R : Type*) [CommRing R] (μ : List ℕ) (r : ℕ) :
    hProd m R (μ ++ [r]) = hProd m R μ * hsymm (Fin m) R r := by
  simp [hProd]

/-- **The Pieri recursion determines the Kostka expansion**: if a family `F` of
polynomials indexed by partitions satisfies the Pieri rule for a family `H` of
multipliers, then the product `H_{μ_1} * ⋯ * H_{μ_k} * F []` expands with the Kostka
numbers as coefficients.  Applied to `H = h` and to the Schur polynomials, this is the
expansion `h_μ = ∑_ν K_{ν μ} s_ν`. -/
theorem pieriProd_mul_eq_sum_kostkaNum [CommRing R] (m : ℕ) (H : ℕ → MvPolynomial (Fin m) R)
    (F : List ℕ → MvPolynomial (Fin m) R)
    (hF : ∀ ν : List ℕ, IsPart ν → ∀ r : ℕ, F ν * H r
      = ∑ ρ ∈ partFinset (ν.sum + r), if HorizStrip ρ ν then F ρ else 0)
    (μ : List ℕ) :
    (μ.map H).prod * F []
      = ∑ ν ∈ partFinset μ.sum,
          (kostkaNum μ.length ν (contentOf μ) : R) • F ν := by
  classical
  induction μ using List.reverseRecOn with
  | nil =>
    rw [List.map_nil, List.prod_nil, List.sum_nil, partFinset_zero, Finset.sum_singleton,
      kostkaNum_nil (fun i hi => absurd hi (by simp))]
    simp
  | append_singleton μ r ih =>
    have hsum : (μ ++ [r]).sum = μ.sum + r := by simp
    have hlen : (μ ++ [r]).length = μ.length + 1 := by simp
    have hcontent : ∀ ν : List ℕ,
        kostkaNum μ.length ν (contentOf (μ ++ [r]))
          = kostkaNum μ.length ν (contentOf μ) :=
      fun ν => kostkaNum_congr _ _ fun i hi => contentOf_append_singleton_of_lt hi
    have hprod : ((μ ++ [r]).map H).prod = (μ.map H).prod * H r := by simp
    rw [hprod, mul_right_comm, ih, Finset.sum_mul, hsum, hlen]
    have hstep : ∀ ν ∈ partFinset μ.sum,
        ((kostkaNum μ.length ν (contentOf μ) : R) • F ν) * H r
          = ∑ ρ ∈ partFinset (μ.sum + r),
              if HorizStrip ρ ν then
                (kostkaNum μ.length ν (contentOf μ) : R) • F ρ else 0 := by
      intro ν hν
      obtain ⟨hνpart, hνsum⟩ := mem_partFinset.1 hν
      rw [smul_mul_assoc, hF ν hνpart r, hνsum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun ρ _ => by split_ifs <;> simp
    rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    obtain ⟨hρpart, hρsum⟩ := mem_partFinset.1 hρ
    have hkey : kostkaNum (μ.length + 1) ρ (contentOf (μ ++ [r]))
        = ∑ ν ∈ partFinset μ.sum,
            if HorizStrip ρ ν then kostkaNum μ.length ν (contentOf μ) else 0 := by
      have := kostkaNum_succ (N := μ.length) (μ := ρ) (c := contentOf (μ ++ [r]))
        (m := μ.sum) hρpart (by rw [contentOf_append_singleton_self, hρsum])
      rw [this, sum_subtype_eq_sum_partFinset μ.sum
        (fun p => if HorizStrip ρ p then kostkaNum μ.length p (contentOf (μ ++ [r])) else 0)]
      exact Finset.sum_congr rfl fun ν _ => by rw [hcontent ν]
    rw [hkey, Nat.cast_sum, Finset.sum_smul]
    exact Finset.sum_congr rfl fun ν _ => by split_ifs <;> simp

/-- The Pieri recursion determines the Kostka expansion, for the products `h_μ` of
complete homogeneous symmetric polynomials. -/
theorem hProd_mul_eq_sum_kostkaNum [CommRing R] (m : ℕ) (F : List ℕ → MvPolynomial (Fin m) R)
    (hF : ∀ ν : List ℕ, IsPart ν → ∀ r : ℕ, F ν * hsymm (Fin m) R r
      = ∑ ρ ∈ partFinset (ν.sum + r), if HorizStrip ρ ν then F ρ else 0)
    (μ : List ℕ) :
    hProd m R μ * F []
      = ∑ ν ∈ partFinset μ.sum,
          (kostkaNum μ.length ν (contentOf μ) : R) • F ν :=
  pieriProd_mul_eq_sum_kostkaNum m (hsymm (Fin m) R) F hF μ

/-- **The expansion of `h_μ` in the Schur polynomials**: `h_μ = ∑_ν K_{ν μ} s_ν`,
where the Kostka number `K_{ν μ}` counts the tableaux of shape `ν` and content
`μ`. -/
theorem hProd_eq_sum_kostkaNum [CommRing R] (m : ℕ) (μ : List ℕ) :
    hProd m R μ
      = ∑ ν ∈ partFinset μ.sum,
          (kostkaNum μ.length ν (contentOf μ) : R) • schurPoly (Fin m) R ν := by
  have := hProd_mul_eq_sum_kostkaNum (R := R) m (schurPoly (Fin m) R)
    (fun ν hν r => schurPoly_mul_hsymm m hν r) μ
  rwa [schurPoly_nil, mul_one] at this

/-- `h_μ` is a symmetric homogeneous polynomial of degree `|μ|`. -/
lemma hProd_mem_symHomogeneousSubmodule' [CommRing R] (μ : List ℕ) :
    hProd m R μ ∈ symHomogeneousSubmodule m μ.sum R := by
  induction μ with
  | nil => exact ⟨isHomogeneous_one (Fin m) R, IsSymmetric.one⟩
  | cons a l ih =>
    have hcons : hProd m R (a :: l) = hsymm (Fin m) R a * hProd m R l := by simp [hProd]
    have hrow : hsymm (Fin m) R a = schurPoly (Fin m) R (rowShape a) :=
      (schurPoly_rowShape (Fin m) R a).symm
    obtain ⟨hhom, hsym⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [hcons, hrow]
      have := (isHomogeneous_schurPoly_of_sum (m := m) (R := R) (n := a)
        (sum_rowShape a)).mul hhom
      simpa [List.sum_cons] using this
    · rw [hcons, hrow]
      exact (schurPoly_isSymmetric _).mul hsym

/-- `h_μ` is a symmetric homogeneous polynomial of degree `|μ|`. -/
lemma hProd_mem_symHomogeneousSubmodule [CommRing R] {n : ℕ} (μ : PartLengthLe n m) :
    hProd m R μ.1 ∈ symHomogeneousSubmodule m n R := by
  have := hProd_mem_symHomogeneousSubmodule' (m := m) (R := R) μ.1
  rwa [μ.2.2.1] at this

/-! ### The bridge with the Kostka numbers of `Combinatorics/Young/Tableau/Kostka.lean` -/

/-- A letter occurs as often in the reading word of a tableau as in its list of boxes. -/
lemma count_toWord_eq_count_flatten (t : List (List ℕ)) (i : ℕ) :
    (toWord t).count i = t.flatten.count i :=
  ((List.reverse_perm t).flatten).count_eq i

/-- The two definitions of the Kostka numbers agree: the number of tableaux of shape `ν`
with letters `< μ.length` and content `μ` is the number of tableaux of shape `ν`
whose reading word has evaluation `μ`. -/
theorem kostkaNum_eq_kostka {μ : List ℕ} (hμ : IsPart μ) (ν : List ℕ) :
    kostkaNum μ.length ν (contentOf μ) = kostka ν μ := by
  rw [kostkaNum, kostka]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun t => ?_)
  simp only [tabSet, Set.mem_ofPred_eq, contentOf_apply]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨hlt, hcount⟩
    refine ext_getD_of_getLastD_ne_zero (getLastD_evalseq_ne_zero _) hμ.getLastD_ne_zero
      fun i => ?_
    rw [getD_evalseq, count_toWord_eq_count_flatten]
    rcases lt_or_ge i μ.length with hi | hi
    · exact hcount i hi
    · rw [List.getD_eq_default _ _ hi, List.count_eq_zero]
      intro hmem
      exact absurd (hlt i hmem) (by omega)
  · intro hev
    have hgetD : ∀ i, t.flatten.count i = μ.getD i 0 := by
      intro i
      rw [← count_toWord_eq_count_flatten, ← getD_evalseq, hev]
    refine ⟨fun x hx => ?_, fun i _ => hgetD i⟩
    by_contra hxlt
    have hzero : μ.getD x 0 = 0 := List.getD_eq_default _ _ (by omega)
    have hpos : 0 < t.flatten.count x := List.count_pos_iff.2 hx
    rw [hgetD x, hzero] at hpos
    exact absurd hpos (by omega)

/-- The expansion of `h_μ` in the Schur polynomials, with the Kostka numbers of
`Combinatorics/Young/Tableau/Kostka.lean`. -/
theorem hProd_eq_sum_kostka [CommRing R] (m : ℕ) {μ : List ℕ} (hμ : IsPart μ) :
    hProd m R μ
      = ∑ ν ∈ partFinset μ.sum, (kostka ν μ : R) • schurPoly (Fin m) R ν := by
  rw [hProd_eq_sum_kostkaNum]
  exact Finset.sum_congr rfl fun ν _ => by rw [kostkaNum_eq_kostka hμ ν]

/-- The expansion of `h_μ`, restricted to the shapes with at most `m` rows: the Schur
polynomials of the other shapes vanish in `m` variables. -/
theorem hProd_eq_sum_partFinsetLengthLe [CommRing R] (m : ℕ) {μ : List ℕ} (hμ : IsPart μ) :
    hProd m R μ
      = ∑ ν ∈ partFinsetLengthLe μ.sum m, (kostka ν μ : R) • schurPoly (Fin m) R ν := by
  classical
  rw [hProd_eq_sum_kostka m hμ]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro ν hν
    obtain ⟨h1, h2, -⟩ := mem_partFinsetLengthLe.1 hν
    exact mem_partFinset.2 ⟨h1, h2⟩
  · intro ν hν hnot
    have hlen : m < ν.length := by
      by_contra hle
      obtain ⟨h1, h2⟩ := mem_partFinset.1 hν
      exact hnot (mem_partFinsetLengthLe.2 ⟨h1, h2, by omega⟩)
    rw [schurPoly_eq_zero_of_lt_length hlen, smul_zero]

/-! ### Linear independence -/

/-- A Kostka number `K_{ν μ}` is nonzero only if `ν` dominates `μ`. -/
lemma partdom_of_kostka_ne_zero {ν μ : List ℕ} (h : kostka ν μ ≠ 0) : Partdom μ ν := by
  by_contra hdom
  exact h (kostka_eq_zero_of_not_partdom hdom)

/-- The expansion of `h_μ` in the Schur polynomials, indexed by `PartLengthLe n m`. -/
lemma hProd_eq_sum_partLengthLe [CommRing R] {n : ℕ} (μ : PartLengthLe n m) :
    hProd m R μ.1
      = ∑ ν : PartLengthLe n m, (kostka ν.1 μ.1 : R) • schurPoly (Fin m) R ν.1 := by
  classical
  rw [hProd_eq_sum_partFinsetLengthLe m μ.2.1, μ.2.2.1, partFinsetLengthLe,
    Finset.sum_image fun x _ y _ h => Subtype.ext h]

/-- **The products `h_μ` are linearly independent**: over any commutative ring, the
polynomials `h_μ` for `μ` a partition of `n` with at most `m` parts are linearly
independent. -/
theorem linearIndependent_hProd (m n : ℕ) (R : Type*) [CommRing R] :
    LinearIndependent R fun μ : PartLengthLe n m => hProd m R μ.1 := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg μ
  have hexp : ∑ ν : PartLengthLe n m, g ν • hProd m R ν.1
      = ∑ ρ : PartLengthLe n m,
          (∑ ν : PartLengthLe n m, g ν * (kostka ρ.1 ν.1 : R)) • schurPoly (Fin m) R ρ.1 := by
    simp only [hProd_eq_sum_partLengthLe, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  have hcoef : ∀ ρ : PartLengthLe n m, ∑ ν : PartLengthLe n m, g ν * (kostka ρ.1 ν.1 : R) = 0 :=
    Fintype.linearIndependent_iff.1 (linearIndependent_schurPoly m n R) _ (by rw [← hexp, hg])
  by_contra hne
  obtain ⟨ρ, hρt, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun ν : PartLengthLe n m => g ν ≠ 0) (fun ν => domWeight n ν.1)
    ⟨μ, Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩⟩
  obtain ⟨-, hρ0⟩ := Finset.mem_filter.1 hρt
  have hsingle : ∀ ν ∈ (Finset.univ : Finset (PartLengthLe n m)), ν ≠ ρ →
      g ν * (kostka ρ.1 ν.1 : R) = 0 := by
    intro ν _ hνne
    by_cases hgmu : g ν = 0
    · rw [hgmu, zero_mul]
    · have hνt : ν ∈ Finset.univ.filter fun ν : PartLengthLe n m => g ν ≠ 0 :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hgmu⟩
      have hzero : kostka ρ.1 ν.1 = 0 := by
        by_contra hk
        have hdom : Partdom ν.1 ρ.1 := partdom_of_kostka_ne_zero hk
        exact hνne (Subtype.ext (eq_of_partdom_of_domWeight_eq ν.2.1 ρ.2.1 ν.2.2.1
          ρ.2.2.1 hdom (hmin ν hνt)))
      rw [hzero, Nat.cast_zero, mul_zero]
  have := hcoef ρ
  rw [Finset.sum_eq_single ρ hsingle (fun h => absurd (Finset.mem_univ ρ) h),
    kostka_self ρ.2.1, Nat.cast_one, mul_one] at this
  exact hρ0 this

/-! ### Spanning -/

/-- Every Schur polynomial of a partition of `n` with at most `m` parts is a linear
combination of the products `h_μ`. -/
theorem schurPoly_mem_span_hProd [CommRing R] (n : ℕ) {μ : List ℕ} (hμ : IsPart μ)
    (hsum : μ.sum = n) (hlen : μ.length ≤ m) :
    schurPoly (Fin m) R μ
      ∈ Submodule.span R (Set.range fun ν : PartLengthLe n m => hProd m R ν.1) := by
  classical
  set W := Submodule.span R (Set.range fun ν : PartLengthLe n m => hProd m R ν.1) with hW
  suffices H : ∀ k : ℕ, ∀ ρ : List ℕ, IsPart ρ → ρ.sum = n → ρ.length ≤ m →
      (n + 1) * n - domWeight n ρ ≤ k → schurPoly (Fin m) R ρ ∈ W by
    exact H _ μ hμ hsum hlen le_rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro ρ hρ hρsum hρlen hk
    have hexp := hProd_eq_sum_partFinsetLengthLe (R := R) m hρ
    rw [hρsum] at hexp
    have hmem : ρ ∈ partFinsetLengthLe n m := mem_partFinsetLengthLe.2 ⟨hρ, hρsum, hρlen⟩
    have hsplit := Finset.add_sum_erase (partFinsetLengthLe n m)
      (fun ν => (kostka ν ρ : R) • schurPoly (Fin m) R ν) hmem
    simp only [kostka_self hρ, Nat.cast_one, one_smul] at hsplit
    have hrest : ∀ ν ∈ (partFinsetLengthLe n m).erase ρ,
        (kostka ν ρ : R) • schurPoly (Fin m) R ν ∈ W := by
      intro ν hν
      have hνne : ν ≠ ρ := Finset.ne_of_mem_erase hν
      obtain ⟨hνpart, hνsum, hνlen⟩ := mem_partFinsetLengthLe.1 (Finset.mem_of_mem_erase hν)
      by_cases hk0 : kostka ν ρ = 0
      · rw [hk0, Nat.cast_zero, zero_smul]
        exact Submodule.zero_mem _
      · have hdom : Partdom ρ ν := partdom_of_kostka_ne_zero hk0
        have hlt : domWeight n ρ < domWeight n ν := by
          rcases lt_or_eq_of_le (domWeight_le_domWeight (n := n) hdom) with h | h
          · exact h
          · exact absurd (eq_of_partdom_of_domWeight_eq hρ hνpart hρsum hνsum hdom
              (le_of_eq h.symm)).symm hνne
        have hbd : domWeight n ν ≤ (n + 1) * n := by
          rw [domWeight]
          calc ∑ j ∈ Finset.range (n + 1), (ν.take j).sum
              ≤ ∑ _j ∈ Finset.range (n + 1), n :=
                Finset.sum_le_sum fun j _ => hνsum ▸ sum_take_le_sum ν j
            _ = (n + 1) * n := by simp [mul_comm]
        exact Submodule.smul_mem _ _
          (ih ((n + 1) * n - domWeight n ν) (by omega) ν hνpart hνsum hνlen le_rfl)
    have hkey : schurPoly (Fin m) R ρ
        = hProd m R ρ - ∑ ν ∈ (partFinsetLengthLe n m).erase ρ,
            (kostka ν ρ : R) • schurPoly (Fin m) R ν :=
      eq_sub_of_add_eq (hsplit.trans hexp.symm)
    rw [hkey]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨⟨ρ, hρ, hρsum, hρlen⟩, rfl⟩)
      (Submodule.sum_mem _ hrest)

/-- **The products `h_μ` span** the module of symmetric homogeneous polynomials of
degree `n` in `m` variables. -/
theorem span_hProd [CommRing R] (m n : ℕ) :
    Submodule.span R (Set.range fun μ : PartLengthLe n m => hProd m R μ.1)
      = symHomogeneousSubmodule m n R := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro q ⟨μ, rfl⟩
    exact hProd_mem_symHomogeneousSubmodule μ
  · rw [← span_schurPoly m n]
    refine Submodule.span_le.2 ?_
    rintro q ⟨ν, rfl⟩
    exact schurPoly_mem_span_hProd n ν.2.1 ν.2.2.1 ν.2.2.2

/-- The product `h_μ`, as an element of the module of symmetric homogeneous polynomials
of degree `n`. -/
noncomputable def hSub (m n : ℕ) (R : Type*) [CommRing R] (μ : PartLengthLe n m) :
    symHomogeneousSubmodule m n R :=
  ⟨hProd m R μ.1, hProd_mem_symHomogeneousSubmodule μ⟩

@[simp] lemma coe_hSub (m n : ℕ) (R : Type*) [CommRing R] (μ : PartLengthLe n m) :
    (hSub m n R μ : MvPolynomial (Fin m) R) = hProd m R μ.1 := rfl

lemma linearIndependent_hSub (m n : ℕ) (R : Type*) [CommRing R] :
    LinearIndependent R (hSub m n R) :=
  LinearIndependent.of_comp (symHomogeneousSubmodule m n R).subtype
    (linearIndependent_hProd m n R)

lemma span_hSub (m n : ℕ) (R : Type*) [CommRing R] :
    ⊤ ≤ Submodule.span R (Set.range (hSub m n R)) := by
  intro p _
  have hmap : Submodule.map (symHomogeneousSubmodule m n R).subtype
      (Submodule.span R (Set.range (hSub m n R))) = symHomogeneousSubmodule m n R := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact span_hProd m n
  have hp : (p : MvPolynomial (Fin m) R) ∈ Submodule.map
      (symHomogeneousSubmodule m n R).subtype
      (Submodule.span R (Set.range (hSub m n R))) := by
    rw [hmap]
    exact p.2
  obtain ⟨q, hq, hqp⟩ := hp
  have hqp' : q = p := Subtype.ext hqp
  rwa [hqp'] at hq

/-- **The products of complete homogeneous symmetric polynomials form a basis** of the
module of symmetric homogeneous polynomials of degree `n` in `m` variables, indexed by the
partitions of `n` with at most `m` parts. -/
noncomputable def hBasis (m n : ℕ) (R : Type*) [CommRing R] :
    Module.Basis (PartLengthLe n m) R (symHomogeneousSubmodule m n R) :=
  Module.Basis.mk (linearIndependent_hSub m n R) (span_hSub m n R)

lemma coe_hBasis (m n : ℕ) (R : Type*) [CommRing R] (μ : PartLengthLe n m) :
    (hBasis m n R μ : MvPolynomial (Fin m) R) = hProd m R μ.1 := by
  rw [hBasis, Module.Basis.mk_apply, coe_hSub]

end MvPolynomial
