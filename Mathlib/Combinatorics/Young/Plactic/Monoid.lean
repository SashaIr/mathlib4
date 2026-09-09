/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Combinatorics.Young.Plactic.RobinsonSchensted
public import Mathlib.Combinatorics.Young.Tableau.StandardYamanouchi

/-!
# The plactic monoid and tableaux

A Lean 4 port of the identification of the plactic monoid with the monoid of tableaux,
following `theories/LRrule/plactic.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

Knuth equivalence is compatible with concatenation of words, so the quotient of the free
monoid on a linearly ordered alphabet by the plactic congruence is a monoid, the *plactic
monoid*.  By `List.placticEquiv_iff_RS_eq` its elements are in bijection with the
Robinson–Schensted insertion tableaux, that is (by `List.RS_toWord`) with all Young
tableaux over the alphabet.  Transporting the product gives the *plactic product* of two
tableaux: insert the reading word of the second tableau into the first one.

## Main definitions

* `List.PlacticMonoid T` : the quotient of `List T` by Knuth equivalence.
* `List.tabMul` : the plactic product of two tableaux (Coq `plactic` product on
  tableaux).

## Main results

* `List.exists_word_RS` : every tableau is an insertion tableau.
* `List.RS_toWord` : the insertion tableau of the reading word of a tableau is the
  tableau itself (Coq `RS_tabE`).
* `List.RS_append` : the insertion tableau of a concatenation only depends on the
  insertion tableaux of the two factors.
* `List.placticMonoidEquivTableau` : the plactic monoid is in bijection with the set of
  tableaux, and this bijection turns the product into `List.tabMul`.
-/

@[expose] public section

namespace List

open List

variable {T : Type*} [LinearOrder T]

/-! ### Tableaux are insertion tableaux -/

/-- Every tableau is the insertion tableau of some word. -/
theorem exists_word_RS {P : List (List T)} (hP : IsTableau P) : ∃ w : List T, RS w = P := by
  have hpart : IsPart (shape P) := isPart_shape hP
  obtain ⟨hQ, hsh, -⟩ := stdTabOfYam_spec (isYam_hyperYam hpart)
  obtain ⟨w, hw, -⟩ :=
    exists_word_RS_RSQ hP hQ (by rw [hsh, evalseq_hyperYam hpart])
  exact ⟨w, hw⟩

/-- The insertion tableau of the reading word of a tableau is the tableau itself
(Coq `RS_tabE`). -/
theorem RS_toWord {t : List (List T)} (h : IsTableau t) : RS (toWord t) = t := by
  obtain ⟨w, rfl⟩ := exists_word_RS h
  exact RS_eq_of_placticEquiv (plactic_toWord_RS w)

/-- `RS` is a retraction onto tableaux: it is the identity on insertion tableaux. -/
lemma RS_toWord_RS (w : List T) : RS (toWord (RS w)) = RS w := RS_toWord (isTableau_RS w)

/-! ### Compatibility of Knuth equivalence with concatenation -/

lemma PlacticEquiv.append {u u' v v' : List T} (hu : PlacticEquiv u u')
    (hv : PlacticEquiv v v') : PlacticEquiv (u ++ v) (u' ++ v') :=
  (hu.append_right v).trans (hv.append_left u')

/-- The insertion tableau of a concatenation only depends on the insertion tableaux of the
two factors. -/
theorem RS_append_congr {u u' v v' : List T} (hu : RS u = RS u') (hv : RS v = RS v') :
    RS (u ++ v) = RS (u' ++ v') :=
  RS_eq_of_placticEquiv
    ((placticEquiv_iff_RS_eq.2 hu).append (placticEquiv_iff_RS_eq.2 hv))

/-! ### The plactic product of tableaux -/

/-- The plactic product of two tableaux: insert the reading word of the second tableau
into the first one. -/
def tabMul (t u : List (List T)) : List (List T) := RS (toWord t ++ toWord u)

lemma isTableau_tabMul (t u : List (List T)) : IsTableau (tabMul t u) := isTableau_RS _

/-- The insertion tableau of a concatenation is the plactic product of the insertion
tableaux. -/
theorem RS_append (u v : List T) : RS (u ++ v) = tabMul (RS u) (RS v) :=
  RS_eq_of_placticEquiv ((plactic_toWord_RS u).append (plactic_toWord_RS v)).symm

lemma tabMul_assoc {t u v : List (List T)} (ht : IsTableau t) (hu : IsTableau u)
    (hv : IsTableau v) : tabMul (tabMul t u) v = tabMul t (tabMul u v) := by
  obtain ⟨a, rfl⟩ := exists_word_RS ht
  obtain ⟨b, rfl⟩ := exists_word_RS hu
  obtain ⟨c, rfl⟩ := exists_word_RS hv
  rw [← RS_append, ← RS_append, ← RS_append, ← RS_append, List.append_assoc]

@[simp] lemma tabMul_nil_left (t : List (List T)) : tabMul [] t = RS (toWord t) := by
  simp [tabMul, toWord]

@[simp] lemma tabMul_nil_right (t : List (List T)) : tabMul t [] = RS (toWord t) := by
  simp [tabMul, toWord]

/-- The tableaux over a linearly ordered alphabet form a monoid under the plactic
product, with the empty tableau as unit. -/
instance tableauMonoid : Monoid {t : List (List T) // IsTableau t} where
  mul t u := ⟨tabMul t.1 u.1, isTableau_tabMul _ _⟩
  one := ⟨[], trivial⟩
  mul_assoc a b c := Subtype.ext (tabMul_assoc a.2 b.2 c.2)
  one_mul a := Subtype.ext (by
    change tabMul [] a.1 = a.1
    rw [tabMul_nil_left]
    exact RS_toWord a.2)
  mul_one a := Subtype.ext (by
    change tabMul a.1 [] = a.1
    rw [tabMul_nil_right]
    exact RS_toWord a.2)

@[simp] lemma coe_tableau_mul (t u : {t : List (List T) // IsTableau t}) :
    ((t * u : {t : List (List T) // IsTableau t}) : List (List T)) = tabMul t.1 u.1 := rfl

/-! ### The plactic monoid -/

/-- Knuth equivalence as a setoid on words. -/
@[instance_reducible]
def placticSetoid (T : Type*) [LinearOrder T] : Setoid (List T) where
  r := PlacticEquiv
  iseqv := ⟨PlacticEquiv.refl, PlacticEquiv.symm, PlacticEquiv.trans⟩

attribute [local instance] placticSetoid

/-- The plactic monoid on the alphabet `T`: words modulo Knuth equivalence. -/
def PlacticMonoid (T : Type*) [LinearOrder T] : Type _ := Quotient (placticSetoid T)

namespace PlacticMonoid

/-- The class of a word in the plactic monoid. -/
def mk (w : List T) : PlacticMonoid T := Quotient.mk (placticSetoid T) w

lemma mk_surjective : Function.Surjective (mk : List T → PlacticMonoid T) :=
  Quotient.mk_surjective

@[simp] lemma mk_eq_mk {u v : List T} : mk u = mk v ↔ PlacticEquiv u v := Quotient.eq

instance : Monoid (PlacticMonoid T) where
  mul a b :=
    Quotient.liftOn₂ a b (fun u v => mk (u ++ v))
      fun _ _ _ _ hu hv => Quotient.sound (hu.append hv)
  one := mk []
  mul_assoc a b c := by
    obtain ⟨a, rfl⟩ := mk_surjective a
    obtain ⟨b, rfl⟩ := mk_surjective b
    obtain ⟨c, rfl⟩ := mk_surjective c
    change mk _ = mk _
    rw [List.append_assoc]
  one_mul a := by
    obtain ⟨a, rfl⟩ := mk_surjective a
    change mk _ = mk _
    rw [List.nil_append]
  mul_one a := by
    obtain ⟨a, rfl⟩ := mk_surjective a
    change mk _ = mk _
    rw [List.append_nil]

@[simp] lemma mk_append (u v : List T) : mk (u ++ v) = mk u * mk v := rfl

@[simp] lemma mk_nil : (mk [] : PlacticMonoid T) = 1 := rfl

end PlacticMonoid

/-- The plactic monoid is in bijection with the tableaux over the alphabet: a class of
words is sent to the common insertion tableau of its elements. -/
def placticMonoidEquivTableau : PlacticMonoid T ≃ {t : List (List T) // IsTableau t} where
  toFun := Quotient.lift (fun w => (⟨RS w, isTableau_RS w⟩ : {t : List (List T) // IsTableau t}))
    fun _ _ h => Subtype.ext (RS_eq_of_placticEquiv h)
  invFun t := PlacticMonoid.mk (toWord t.1)
  left_inv a := by
    obtain ⟨w, rfl⟩ := PlacticMonoid.mk_surjective a
    exact Quotient.sound (plactic_toWord_RS w)
  right_inv t := Subtype.ext (RS_toWord t.2)

@[simp] lemma placticMonoidEquivTableau_mk (w : List T) :
    (placticMonoidEquivTableau (PlacticMonoid.mk w) : List (List T)) = RS w := rfl

/-- Under the bijection between the plactic monoid and tableaux, the product of the
plactic monoid becomes the plactic product of tableaux. -/
theorem placticMonoidEquivTableau_mul (a b : PlacticMonoid T) :
    (placticMonoidEquivTableau (a * b) : List (List T))
      = tabMul (placticMonoidEquivTableau a) (placticMonoidEquivTableau b) := by
  obtain ⟨u, rfl⟩ := PlacticMonoid.mk_surjective a
  obtain ⟨v, rfl⟩ := PlacticMonoid.mk_surjective b
  change RS (u ++ v) = tabMul (RS u) (RS v)
  exact RS_append u v

/-- The plactic monoid is isomorphic, as a monoid, to the tableaux with the plactic
product. -/
def placticMonoidMulEquivTableau :
  MulEquiv (PlacticMonoid T) {t : List (List T) // IsTableau t} :=
  { placticMonoidEquivTableau with
    map_mul' := fun a b => Subtype.ext (placticMonoidEquivTableau_mul a b) }

end List
