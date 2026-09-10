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
`h_η = h_{η_1} * ... * h_{η_k}` of complete homogeneous symmetric polynomials in the
basis of Schur polynomials, `h_η = ∑_mu K_{μ η} s_μ`, where `K_{μ η}` is the
Kostka number counting the tableaux of shape `μ` and content `η`.  Since the Kostka
numbers are unitriangular for the dominance order, the polynomials `h_η`, for `η` a
partition of `n` with at most `m` parts, form a basis of the module of symmetric
homogeneous polynomials of degree `n` in `m` variables.

## Main results

* `MvPolynomial.hProd_eq_sum_kostka` : `h_η = ∑_mu K_{μ η} s_μ`.
* `MvPolynomial.linearIndependent_hProd` : the `h_η` are linearly independent.
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

/-- The content function attached to a list: `i ↦ η.getD i 0`. -/
def contentOf (η : List ℕ) : ℕ → ℕ := fun i => η.getD i 0

@[simp] lemma contentOf_apply (η : List ℕ) (i : ℕ) : contentOf η i = η.getD i 0 := rfl

lemma contentOf_append_singleton_of_lt {η : List ℕ} {r i : ℕ} (hi : i < η.length) :
    contentOf (η ++ [r]) i = contentOf η i := by
  simp [contentOf, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma contentOf_append_singleton_self (η : List ℕ) (r : ℕ) :
    contentOf (η ++ [r]) η.length = r := by
  simp [contentOf, List.getD_eq_getElem?_getD]

/-! ### The product of complete homogeneous symmetric polynomials -/

/-- The product `h_η = h_{η_1} * ... * h_{η_k}` of complete homogeneous symmetric
polynomials attached to a list `η`. -/
noncomputable def hProd (m : ℕ) (R : Type*) [CommRing R] (η : List ℕ) :
    MvPolynomial (Fin m) R := (η.map (hsymm (Fin m) R)).prod

@[simp] lemma hProd_nil (m : ℕ) (R : Type*) [CommRing R] : hProd m R [] = 1 := rfl

lemma hProd_append_singleton (m : ℕ) (R : Type*) [CommRing R] (η : List ℕ) (r : ℕ) :
    hProd m R (η ++ [r]) = hProd m R η * hsymm (Fin m) R r := by
  simp [hProd]

/-- **The Pieri recursion determines the Kostka expansion**: if a family `F` of
polynomials indexed by partitions satisfies the Pieri rule for a family `H` of
multipliers, then the product `H_{η_1} * ⋯ * H_{η_k} * F []` expands with the Kostka
numbers as coefficients.  Applied to `H = h` and to the Schur polynomials, this is the
expansion `h_η = ∑_mu K_{μ η} s_μ`. -/
theorem pieriProd_mul_eq_sum_kostkaNum [CommRing R] (m : ℕ) (H : ℕ → MvPolynomial (Fin m) R)
    (F : List ℕ → MvPolynomial (Fin m) R)
    (hF : ∀ μ : List ℕ, IsPart μ → ∀ r : ℕ, F μ * H r
      = ∑ ν ∈ partFinset (μ.sum + r), if HorizStrip ν μ then F ν else 0)
    (η : List ℕ) :
    (η.map H).prod * F []
      = ∑ μ ∈ partFinset η.sum,
          (kostkaNum η.length μ (contentOf η) : R) • F μ := by
  classical
  induction η using List.reverseRecOn with
  | nil =>
    rw [List.map_nil, List.prod_nil, List.sum_nil, partFinset_zero, Finset.sum_singleton,
      kostkaNum_nil (fun i hi => absurd hi (by simp))]
    simp
  | append_singleton η r ih =>
    have hsum : (η ++ [r]).sum = η.sum + r := by simp
    have hlen : (η ++ [r]).length = η.length + 1 := by simp
    have hcontent : ∀ μ : List ℕ,
        kostkaNum η.length μ (contentOf (η ++ [r]))
          = kostkaNum η.length μ (contentOf η) :=
      fun μ => kostkaNum_congr _ _ fun i hi => contentOf_append_singleton_of_lt hi
    have hprod : ((η ++ [r]).map H).prod = (η.map H).prod * H r := by simp
    rw [hprod, mul_right_comm, ih, Finset.sum_mul, hsum, hlen]
    have hstep : ∀ μ ∈ partFinset η.sum,
        ((kostkaNum η.length μ (contentOf η) : R) • F μ) * H r
          = ∑ ν ∈ partFinset (η.sum + r),
              if HorizStrip ν μ then
                (kostkaNum η.length μ (contentOf η) : R) • F ν else 0 := by
      intro μ hμ
      obtain ⟨hμpart, hμsum⟩ := mem_partFinset.1 hμ
      rw [smul_mul_assoc, hF μ hμpart r, hμsum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun ν _ => by split_ifs <;> simp
    rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν hν => ?_
    obtain ⟨hνpart, hνsum⟩ := mem_partFinset.1 hν
    have hkey : kostkaNum (η.length + 1) ν (contentOf (η ++ [r]))
        = ∑ μ ∈ partFinset η.sum,
            if HorizStrip ν μ then kostkaNum η.length μ (contentOf η) else 0 := by
      have := kostkaNum_succ (N := η.length) (μ := ν) (c := contentOf (η ++ [r]))
        (m := η.sum) hνpart (by rw [contentOf_append_singleton_self, hνsum])
      rw [this, sum_subtype_eq_sum_partFinset η.sum
        (fun p => if HorizStrip ν p then kostkaNum η.length p (contentOf (η ++ [r])) else 0)]
      exact Finset.sum_congr rfl fun μ _ => by rw [hcontent μ]
    rw [hkey, Nat.cast_sum, Finset.sum_smul]
    exact Finset.sum_congr rfl fun μ _ => by split_ifs <;> simp

/-- The Pieri recursion determines the Kostka expansion, for the products `h_η` of
complete homogeneous symmetric polynomials. -/
theorem hProd_mul_eq_sum_kostkaNum [CommRing R] (m : ℕ) (F : List ℕ → MvPolynomial (Fin m) R)
    (hF : ∀ μ : List ℕ, IsPart μ → ∀ r : ℕ, F μ * hsymm (Fin m) R r
      = ∑ ν ∈ partFinset (μ.sum + r), if HorizStrip ν μ then F ν else 0)
    (η : List ℕ) :
    hProd m R η * F []
      = ∑ μ ∈ partFinset η.sum,
          (kostkaNum η.length μ (contentOf η) : R) • F μ :=
  pieriProd_mul_eq_sum_kostkaNum m (hsymm (Fin m) R) F hF η

/-- **The expansion of `h_η` in the Schur polynomials**: `h_η = ∑_mu K_{μ η} s_μ`,
where the Kostka number `K_{μ η}` counts the tableaux of shape `μ` and content
`η`. -/
theorem hProd_eq_sum_kostkaNum [CommRing R] (m : ℕ) (η : List ℕ) :
    hProd m R η
      = ∑ μ ∈ partFinset η.sum,
          (kostkaNum η.length μ (contentOf η) : R) • schurPoly (Fin m) R μ := by
  have := hProd_mul_eq_sum_kostkaNum (R := R) m (schurPoly (Fin m) R)
    (fun μ hμ r => schurPoly_mul_hsymm m hμ r) η
  rwa [schurPoly_nil, mul_one] at this

/-- `h_η` is a symmetric homogeneous polynomial of degree `|η|`. -/
lemma hProd_mem_symHomogeneousSubmodule' [CommRing R] (η : List ℕ) :
    hProd m R η ∈ symHomogeneousSubmodule m η.sum R := by
  induction η with
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

/-- `h_η` is a symmetric homogeneous polynomial of degree `|η|`. -/
lemma hProd_mem_symHomogeneousSubmodule [CommRing R] {n : ℕ} (η : PartIdx n m) :
    hProd m R η.1 ∈ symHomogeneousSubmodule m n R := by
  have := hProd_mem_symHomogeneousSubmodule' (m := m) (R := R) η.1
  rwa [η.2.2.1] at this

/-! ### The bridge with the Kostka numbers of `Combinatorics/Young/Tableau/Kostka.lean` -/

/-- A letter occurs as often in the reading word of a tableau as in its list of boxes. -/
lemma count_toWord_eq_count_flatten (t : List (List ℕ)) (i : ℕ) :
    (toWord t).count i = t.flatten.count i :=
  ((List.reverse_perm t).flatten).count_eq i

/-- The two definitions of the Kostka numbers agree: the number of tableaux of shape `μ`
with letters `< η.length` and content `η` is the number of tableaux of shape `μ`
whose reading word has evaluation `η`. -/
theorem kostkaNum_eq_kostka {η : List ℕ} (hη : IsPart η) (μ : List ℕ) :
    kostkaNum η.length μ (contentOf η) = kostka μ η := by
  rw [kostkaNum, kostka]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun t => ?_)
  simp only [tabSet, Set.mem_ofPred_eq, contentOf_apply]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨hlt, hcount⟩
    refine ext_getD_of_getLastD_ne_zero (getLastD_evalseq_ne_zero _) hη.getLastD_ne_zero
      fun i => ?_
    rw [getD_evalseq, count_toWord_eq_count_flatten]
    rcases lt_or_ge i η.length with hi | hi
    · exact hcount i hi
    · rw [List.getD_eq_default _ _ hi, List.count_eq_zero]
      intro hmem
      exact absurd (hlt i hmem) (by omega)
  · intro hev
    have hgetD : ∀ i, t.flatten.count i = η.getD i 0 := by
      intro i
      rw [← count_toWord_eq_count_flatten, ← getD_evalseq, hev]
    refine ⟨fun x hx => ?_, fun i _ => hgetD i⟩
    by_contra hxlt
    have hzero : η.getD x 0 = 0 := List.getD_eq_default _ _ (by omega)
    have hpos : 0 < t.flatten.count x := List.count_pos_iff.2 hx
    rw [hgetD x, hzero] at hpos
    exact absurd hpos (by omega)

/-- The expansion of `h_η` in the Schur polynomials, with the Kostka numbers of
`Combinatorics/Young/Tableau/Kostka.lean`. -/
theorem hProd_eq_sum_kostka [CommRing R] (m : ℕ) {η : List ℕ} (hη : IsPart η) :
    hProd m R η
      = ∑ μ ∈ partFinset η.sum, (kostka μ η : R) • schurPoly (Fin m) R μ := by
  rw [hProd_eq_sum_kostkaNum]
  exact Finset.sum_congr rfl fun μ _ => by rw [kostkaNum_eq_kostka hη μ]

/-- The expansion of `h_η`, restricted to the shapes with at most `m` rows: the Schur
polynomials of the other shapes vanish in `m` variables. -/
theorem hProd_eq_sum_partsFinset [CommRing R] (m : ℕ) {η : List ℕ} (hη : IsPart η) :
    hProd m R η
      = ∑ μ ∈ partsFinset η.sum m, (kostka μ η : R) • schurPoly (Fin m) R μ := by
  classical
  rw [hProd_eq_sum_kostka m hη]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro μ hμ
    obtain ⟨h1, h2, -⟩ := mem_partsFinset.1 hμ
    exact mem_partFinset.2 ⟨h1, h2⟩
  · intro μ hμ hnot
    have hlen : m < μ.length := by
      by_contra hle
      obtain ⟨h1, h2⟩ := mem_partFinset.1 hμ
      exact hnot (mem_partsFinset.2 ⟨h1, h2, by omega⟩)
    rw [schurPoly_eq_zero_of_lt_length hlen, smul_zero]

/-! ### Linear independence -/

/-- A Kostka number `K_{μ η}` is nonzero only if `μ` dominates `η`. -/
lemma partdom_of_kostka_ne_zero {μ η : List ℕ} (h : kostka μ η ≠ 0) : Partdom η μ := by
  by_contra hdom
  exact h (kostka_eq_zero_of_not_partdom hdom)

/-- The expansion of `h_η` in the Schur polynomials, indexed by `PartIdx n m`. -/
lemma hProd_eq_sum_partIdx [CommRing R] {n : ℕ} (η : PartIdx n m) :
    hProd m R η.1
      = ∑ ν : PartIdx n m, (kostka ν.1 η.1 : R) • schurPoly (Fin m) R ν.1 := by
  classical
  rw [hProd_eq_sum_partsFinset m η.2.1, η.2.2.1, partsFinset,
    Finset.sum_image fun x _ y _ h => Subtype.ext h]

/-- **The products `h_η` are linearly independent**: over any commutative ring, the
polynomials `h_η` for `η` a partition of `n` with at most `m` parts are linearly
independent. -/
theorem linearIndependent_hProd (m n : ℕ) (R : Type*) [CommRing R] :
    LinearIndependent R fun η : PartIdx n m => hProd m R η.1 := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg η
  have hexp : ∑ μ : PartIdx n m, g μ • hProd m R μ.1
      = ∑ ν : PartIdx n m,
          (∑ μ : PartIdx n m, g μ * (kostka ν.1 μ.1 : R)) • schurPoly (Fin m) R ν.1 := by
    simp only [hProd_eq_sum_partIdx, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  have hcoef : ∀ ν : PartIdx n m, ∑ μ : PartIdx n m, g μ * (kostka ν.1 μ.1 : R) = 0 :=
    Fintype.linearIndependent_iff.1 (linearIndependent_schurPoly m n R) _ (by rw [← hexp, hg])
  by_contra hne
  obtain ⟨ν, hνt, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun μ : PartIdx n m => g μ ≠ 0) (fun μ => domWeight n μ.1)
    ⟨η, Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩⟩
  obtain ⟨-, hν0⟩ := Finset.mem_filter.1 hνt
  have hsingle : ∀ μ ∈ (Finset.univ : Finset (PartIdx n m)), μ ≠ ν →
      g μ * (kostka ν.1 μ.1 : R) = 0 := by
    intro μ _ hμne
    by_cases hgmu : g μ = 0
    · rw [hgmu, zero_mul]
    · have hμt : μ ∈ Finset.univ.filter fun μ : PartIdx n m => g μ ≠ 0 :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hgmu⟩
      have hzero : kostka ν.1 μ.1 = 0 := by
        by_contra hk
        have hdom : Partdom μ.1 ν.1 := partdom_of_kostka_ne_zero hk
        exact hμne (Subtype.ext (eq_of_partdom_of_domWeight_eq μ.2.1 ν.2.1 μ.2.2.1
          ν.2.2.1 hdom (hmin μ hμt)))
      rw [hzero, Nat.cast_zero, mul_zero]
  have := hcoef ν
  rw [Finset.sum_eq_single ν hsingle (fun h => absurd (Finset.mem_univ ν) h),
    kostka_self ν.2.1, Nat.cast_one, mul_one] at this
  exact hν0 this

/-! ### Spanning -/

/-- Every Schur polynomial of a partition of `n` with at most `m` parts is a linear
combination of the products `h_η`. -/
theorem schurPoly_mem_span_hProd [CommRing R] (n : ℕ) {η : List ℕ} (hη : IsPart η)
    (hsum : η.sum = n) (hlen : η.length ≤ m) :
    schurPoly (Fin m) R η
      ∈ Submodule.span R (Set.range fun μ : PartIdx n m => hProd m R μ.1) := by
  classical
  set W := Submodule.span R (Set.range fun μ : PartIdx n m => hProd m R μ.1) with hW
  suffices H : ∀ k : ℕ, ∀ ν : List ℕ, IsPart ν → ν.sum = n → ν.length ≤ m →
      (n + 1) * n - domWeight n ν ≤ k → schurPoly (Fin m) R ν ∈ W by
    exact H _ η hη hsum hlen le_rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro ν hν hνsum hνlen hk
    have hexp := hProd_eq_sum_partsFinset (R := R) m hν
    rw [hνsum] at hexp
    have hmem : ν ∈ partsFinset n m := mem_partsFinset.2 ⟨hν, hνsum, hνlen⟩
    have hsplit := Finset.add_sum_erase (partsFinset n m)
      (fun μ => (kostka μ ν : R) • schurPoly (Fin m) R μ) hmem
    simp only [kostka_self hν, Nat.cast_one, one_smul] at hsplit
    have hrest : ∀ μ ∈ (partsFinset n m).erase ν,
        (kostka μ ν : R) • schurPoly (Fin m) R μ ∈ W := by
      intro μ hμ
      have hμne : μ ≠ ν := Finset.ne_of_mem_erase hμ
      obtain ⟨hμpart, hμsum, hμlen⟩ := mem_partsFinset.1 (Finset.mem_of_mem_erase hμ)
      by_cases hk0 : kostka μ ν = 0
      · rw [hk0, Nat.cast_zero, zero_smul]
        exact Submodule.zero_mem _
      · have hdom : Partdom ν μ := partdom_of_kostka_ne_zero hk0
        have hlt : domWeight n ν < domWeight n μ := by
          rcases lt_or_eq_of_le (domWeight_le_domWeight (n := n) hdom) with h | h
          · exact h
          · exact absurd (eq_of_partdom_of_domWeight_eq hν hμpart hνsum hμsum hdom
              (le_of_eq h.symm)).symm hμne
        have hbd : domWeight n μ ≤ (n + 1) * n := by
          rw [domWeight]
          calc ∑ j ∈ Finset.range (n + 1), (μ.take j).sum
              ≤ ∑ _j ∈ Finset.range (n + 1), n :=
                Finset.sum_le_sum fun j _ => hμsum ▸ sum_take_le_sum μ j
            _ = (n + 1) * n := by simp [mul_comm]
        exact Submodule.smul_mem _ _
          (ih ((n + 1) * n - domWeight n μ) (by omega) μ hμpart hμsum hμlen le_rfl)
    have hkey : schurPoly (Fin m) R ν
        = hProd m R ν - ∑ μ ∈ (partsFinset n m).erase ν,
            (kostka μ ν : R) • schurPoly (Fin m) R μ :=
      eq_sub_of_add_eq (hsplit.trans hexp.symm)
    rw [hkey]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨⟨ν, hν, hνsum, hνlen⟩, rfl⟩)
      (Submodule.sum_mem _ hrest)

/-- **The products `h_η` span** the module of symmetric homogeneous polynomials of
degree `n` in `m` variables. -/
theorem span_hProd [CommRing R] (m n : ℕ) :
    Submodule.span R (Set.range fun η : PartIdx n m => hProd m R η.1)
      = symHomogeneousSubmodule m n R := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro q ⟨η, rfl⟩
    exact hProd_mem_symHomogeneousSubmodule η
  · rw [← span_schurPoly m n]
    refine Submodule.span_le.2 ?_
    rintro q ⟨ν, rfl⟩
    exact schurPoly_mem_span_hProd n ν.2.1 ν.2.2.1 ν.2.2.2

/-- The product `h_η`, as an element of the module of symmetric homogeneous polynomials
of degree `n`. -/
noncomputable def hSub (m n : ℕ) (R : Type*) [CommRing R] (η : PartIdx n m) :
    symHomogeneousSubmodule m n R :=
  ⟨hProd m R η.1, hProd_mem_symHomogeneousSubmodule η⟩

@[simp] lemma coe_hSub (m n : ℕ) (R : Type*) [CommRing R] (η : PartIdx n m) :
    (hSub m n R η : MvPolynomial (Fin m) R) = hProd m R η.1 := rfl

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
    Module.Basis (PartIdx n m) R (symHomogeneousSubmodule m n R) :=
  Module.Basis.mk (linearIndependent_hSub m n R) (span_hSub m n R)

lemma coe_hBasis (m n : ℕ) (R : Type*) [CommRing R] (η : PartIdx n m) :
    (hBasis m n R η : MvPolynomial (Fin m) R) = hProd m R η.1 := by
  rw [hBasis, Module.Basis.mk_apply, coe_hSub]

end MvPolynomial
