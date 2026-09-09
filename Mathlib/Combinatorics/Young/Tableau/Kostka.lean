/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.RobinsonSchensted.InsertionTableau
public import Mathlib.Combinatorics.Young.Shape.Dominance
public import Mathlib.Combinatorics.Young.Word.Yamanouchi
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Content of a tableau, dominance, and Kostka numbers

The *content* (or evaluation) of a semistandard Young tableau with entries in `ℕ` is the
list `List.evalseq (List.toWord t)` counting how many times each letter occurs.

Since the entries of a tableau increase strictly down the columns, the entry sitting in
row `i` is at least `i`; hence all the boxes containing a letter `< k` lie in the first
`k` rows.  Counting boxes gives the classical fact that the shape of a tableau dominates
its content, so that the Kostka number `K` of a shape `λ` and a content `μ` vanishes
unless `λ` dominates `μ`.  When the content equals the shape, the tableau is forced to be
the *superstandard* one, whose `i`-th row consists of `λ i` copies of `i`; in other words
`K λ λ = 1`.

## Main definitions

* `List.superTab lam` : the tableau whose `i`-th row is `lam i` copies of `i`.
* `List.kostka lam mu` : the Kostka number, the number of tableaux of shape `lam` and
  content `mu`.

## Main results

* `List.le_of_mem_getD_tableau` : an entry of the `i`-th row of a tableau is at least `i`.
* `List.partdom_evalseq_toWord` : the content of a tableau is dominated by its shape.
* `List.isTableau_superTab`, `List.shape_superTab`, `List.evalseq_toWord_superTab` :
  the superstandard tableau of a partition is a tableau of that shape and content.
* `List.eq_superTab_of_evalseq_eq` : a tableau whose content equals its shape is the
  superstandard tableau.
* `List.kostka_eq_zero_of_not_partdom`, `List.kostka_self` : `K λ μ = 0` unless `λ`
  dominates `μ`, and `K λ λ = 1`.
* `List.partdom_evalseq_RS` : the shape of the insertion tableau of a word dominates the
  content of the word.
-/

@[expose] public section

namespace List

open List

/-! ### Counting letters in the reading word of a tableau -/

variable {T : Type*} [LinearOrder T]

omit [LinearOrder T] in
lemma countP_toWord (p : T → Bool) (t : List (List T)) :
    (toWord t).countP p = ∑ i ∈ Finset.range t.length, (t.getD i []).countP p := by
  induction t with
  | nil => simp
  | cons t0 t ih =>
    rw [toWord_cons, List.countP_append, ih, List.length_cons, Finset.sum_range_succ']
    simp

/-- The partial sums of the content of a word count its letters below a threshold. -/
lemma sum_take_evalseq (w : List ℕ) (k : ℕ) :
    ((evalseq w).take k).sum = w.countP (fun x => decide (x < k)) := by
  rw [sum_take_eq_sum_range]
  simp only [getD_evalseq]
  induction w with
  | nil => simp
  | cons a w ih =>
    have hcount : ∀ i, (a :: w).count i = w.count i + (if a = i then 1 else 0) := by
      intro i
      rw [List.count_cons]
      simp only [beq_iff_eq]
    simp only [hcount, Finset.sum_add_distrib, ih, List.countP_cons]
    have : ∑ i ∈ Finset.range k, (if a = i then 1 else 0) = if a < k then 1 else 0 := by
      rw [Finset.sum_ite_eq (Finset.range k) a (fun _ => 1)]
      simp
    rw [this]
    by_cases h : a < k <;> simp [h]

/-! ### Entries of the `i`-th row are at least `i` -/

lemma le_of_mem_getD_tableau {t : List (List ℕ)} (ht : IsTableau t) (i : ℕ) {x : ℕ}
    (hx : x ∈ t.getD i []) : i ≤ x := by
  obtain ⟨c, hc, rfl⟩ := List.mem_iff_getElem.1 hx
  exact ht.index_le_getElem hc

/-- Rows of index at least `k` contain no letter smaller than `k`. -/
lemma countP_lt_row_eq_zero {t : List (List ℕ)} (ht : IsTableau t) {i k : ℕ} (hik : k ≤ i) :
    (t.getD i []).countP (fun x => decide (x < k)) = 0 := by
  rw [List.countP_eq_zero]
  intro x hx
  have := le_of_mem_getD_tableau ht i hx
  simp only [decide_eq_true_eq]
  omega

/-! ### The shape of a tableau dominates its content -/

/-- Coq: the evaluation of a tableau is dominated by its shape. -/
theorem partdom_evalseq_toWord {t : List (List ℕ)} (ht : IsTableau t) :
    Partdom (evalseq (toWord t)) (shape t) := by
  intro k
  rw [sum_take_evalseq, countP_toWord, sum_take_eq_sum_range]
  have hterm : ∀ r ∈ Finset.range (min t.length k),
      (t.getD r []).countP (fun x => decide (x < k)) ≤ (shape t).getD r 0 := by
    intro r _
    rw [getD_shape]
    exact List.countP_le_length
  calc ∑ r ∈ Finset.range t.length, (t.getD r []).countP (fun x => decide (x < k))
      = ∑ r ∈ Finset.range (min t.length k), (t.getD r []).countP (fun x => decide (x < k)) := by
        refine (Finset.sum_subset (Finset.range_subset_range.2 (min_le_left t.length k)) ?_).symm
        intro x hx hx'
        simp only [Finset.mem_range, not_lt] at hx hx'
        rcases Nat.lt_or_ge x k with h | h
        · exact absurd (lt_min hx h) (by omega)
        · exact countP_lt_row_eq_zero ht h
    _ ≤ ∑ r ∈ Finset.range (min t.length k), (shape t).getD r 0 := Finset.sum_le_sum hterm
    _ ≤ ∑ r ∈ Finset.range k, (shape t).getD r 0 :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (min_le_right t.length k))

/-! ### The superstandard tableau of a partition -/

lemma sum_range_eq_sum_range_of_zero {c : ℕ → ℕ} {n k : ℕ} (h1 : ∀ r, k ≤ r → c r = 0)
    (h2 : ∀ r, n ≤ r → c r = 0) :
    ∑ r ∈ Finset.range n, c r = ∑ r ∈ Finset.range k, c r := by
  have e1 : ∑ r ∈ Finset.range n, c r = ∑ r ∈ Finset.range (min n k), c r := by
    refine (Finset.sum_subset (Finset.range_subset_range.2 (min_le_left n k)) ?_).symm
    intro x hx hx'
    simp only [Finset.mem_range, not_lt] at hx hx'
    exact h1 x (by omega)
  have e2 : ∑ r ∈ Finset.range k, c r = ∑ r ∈ Finset.range (min n k), c r := by
    refine (Finset.sum_subset (Finset.range_subset_range.2 (min_le_right n k)) ?_).symm
    intro x hx hx'
    simp only [Finset.mem_range, not_lt] at hx hx'
    exact h2 x (by omega)
  rw [e1, e2]

lemma isRow_replicate (n a : ℕ) : IsRow (List.replicate n a) := by
  rw [IsRow, List.isChain_iff_pairwise]
  exact List.pairwise_replicate.2 (Or.inr le_rfl)

lemma dominate_replicate {m n a b : ℕ} (hmn : m ≤ n) (hab : a < b) :
    Dominate (List.replicate m b) (List.replicate n a) := by
  induction m generalizing n with
  | zero => simp
  | succ p ih =>
    cases n with
    | zero => omega
    | succ q =>
      rw [List.replicate_succ, List.replicate_succ, dominate_cons_cons]
      exact ⟨hab, ih (by omega)⟩

/-- The rows of the superstandard tableau, starting the labels at `i`. -/
def superTabFrom (i : ℕ) : List ℕ → List (List ℕ)
  | [] => []
  | n :: lam => List.replicate n i :: superTabFrom (i + 1) lam

/-- The *superstandard* tableau of a partition: its `i`-th row consists of `lam i` copies
of the letter `i`.  It is the unique tableau whose content equals its shape. -/
def superTab (lam : List ℕ) : List (List ℕ) := superTabFrom 0 lam

@[simp] lemma superTabFrom_nil (i : ℕ) : superTabFrom i [] = [] := rfl

@[simp] lemma superTabFrom_cons (i n : ℕ) (lam : List ℕ) :
    superTabFrom i (n :: lam) = List.replicate n i :: superTabFrom (i + 1) lam := rfl

@[simp] lemma shape_superTabFrom (i : ℕ) (lam : List ℕ) : shape (superTabFrom i lam) = lam := by
  induction lam generalizing i with
  | nil => simp
  | cons n lam ih => simp [ih]

@[simp] lemma shape_superTab (lam : List ℕ) : shape (superTab lam) = lam :=
  shape_superTabFrom 0 lam

lemma headD_superTabFrom (i : ℕ) (lam : List ℕ) :
    (superTabFrom i lam).headD [] = List.replicate (lam.headD 0) i := by
  cases lam <;> simp

lemma getD_superTabFrom (i : ℕ) (lam : List ℕ) (j : ℕ) :
    (superTabFrom i lam).getD j [] = List.replicate (lam.getD j 0) (i + j) := by
  induction lam generalizing i j with
  | nil => simp
  | cons n lam ih =>
    cases j with
    | zero => simp
    | succ m =>
      simp only [superTabFrom_cons, List.getD_cons_succ, ih]
      congr 1
      omega

lemma getD_superTab (lam : List ℕ) (j : ℕ) :
    (superTab lam).getD j [] = List.replicate (lam.getD j 0) j := by
  change (superTabFrom 0 lam).getD j [] = _
  simpa using getD_superTabFrom 0 lam j

lemma isTableau_superTabFrom (i : ℕ) {lam : List ℕ} (h : IsPart lam) :
    IsTableau (superTabFrom i lam) := by
  induction lam generalizing i with
  | nil => simp
  | cons n lam ih =>
    obtain ⟨hhead, hpart⟩ := h
    have hn : n ≠ 0 := by
      have := IsPart.headD_ne_zero (sh := n :: lam) ⟨hhead, hpart⟩
      simpa using this
    have hle : lam.headD 0 ≤ n := by cases lam <;> simp_all
    refine ⟨?_, isRow_replicate n i, ?_, ih (i + 1) hpart⟩
    · simp [hn]
    · rw [headD_superTabFrom]
      exact dominate_replicate hle (by omega)

lemma isTableau_superTab {lam : List ℕ} (h : IsPart lam) : IsTableau (superTab lam) :=
  isTableau_superTabFrom 0 h

lemma count_toWord_superTabFrom (i : ℕ) (lam : List ℕ) (j : ℕ) :
    (toWord (superTabFrom i lam)).count j = if i ≤ j then lam.getD (j - i) 0 else 0 := by
  induction lam generalizing i with
  | nil => simp
  | cons n lam ih =>
    rw [superTabFrom_cons, toWord_cons, List.count_append, ih, List.count_replicate]
    rcases lt_trichotomy j i with h | h | h
    · have h1 : ¬ (i ≤ j) := by omega
      have h2 : ¬ (i + 1 ≤ j) := by omega
      have h3 : i ≠ j := by omega
      simp [h1, h2, h3]
    · subst h
      have h2 : ¬ (j + 1 ≤ j) := by omega
      simp [h2]
    · have h1 : i ≤ j := by omega
      have h2 : i + 1 ≤ j := by omega
      have h3 : i ≠ j := by omega
      have h4 : j - i = (j - i - 1) + 1 := by omega
      simp only [h1, h2, ite_true, beq_iff_eq]
      rw [ite_eq_right h3, h4, List.getD_cons_succ, add_zero]
      congr 1

lemma count_toWord_superTab (lam : List ℕ) (j : ℕ) :
    (toWord (superTab lam)).count j = lam.getD j 0 := by
  change (toWord (superTabFrom 0 lam)).count j = _
  simpa using count_toWord_superTabFrom 0 lam j

/-- The content of the superstandard tableau of a partition is that partition. -/
theorem evalseq_toWord_superTab {lam : List ℕ} (h : IsPart lam) :
    evalseq (toWord (superTab lam)) = lam :=
  ext_getD_of_getLastD_ne_zero (getLastD_evalseq_ne_zero _) h.getLastD_ne_zero
    (fun i => by rw [getD_evalseq, count_toWord_superTab])

/-! ### A tableau whose content is its shape is superstandard -/

/-- If the content of a tableau equals its shape, then all the entries of its `i`-th row
are equal to `i`: the tableau is the superstandard one. -/
theorem eq_superTab_of_evalseq_eq {t : List (List ℕ)} (ht : IsTableau t)
    (h : evalseq (toWord t) = shape t) : t = superTab (shape t) := by
  -- for every `k`, the rows of index `< k` only contain letters `< k`
  have hrowlt : ∀ k, ∀ r < k, ∀ x ∈ t.getD r [], x < k := by
    intro k
    have hsum : ∑ r ∈ Finset.range k, (t.getD r []).countP (fun x => decide (x < k))
        = ∑ r ∈ Finset.range k, (t.getD r []).length := by
      have h1 : ((evalseq (toWord t)).take k).sum = ((shape t).take k).sum := by rw [h]
      rw [sum_take_evalseq, countP_toWord, sum_take_eq_sum_range] at h1
      have h2 : ∑ r ∈ Finset.range t.length, (t.getD r []).countP (fun x => decide (x < k))
          = ∑ r ∈ Finset.range k, (t.getD r []).countP (fun x => decide (x < k)) := by
        refine sum_range_eq_sum_range_of_zero (fun r hr => countP_lt_row_eq_zero ht hr)
          (fun r hr => ?_)
        rw [List.getD_eq_default _ _ hr]
        simp
      rw [h2] at h1
      rw [h1]
      exact Finset.sum_congr rfl fun r _ => getD_shape t r
    have hterm := (Finset.sum_eq_sum_iff_of_le
      (fun r (_ : r ∈ Finset.range k) => List.countP_le_length
        (p := fun x => decide (x < k)) (l := t.getD r []))).1 hsum
    intro r hr x hx
    have := List.countP_eq_length.1 (hterm r (Finset.mem_range.2 hr)) x hx
    simpa using this
  -- hence the `i`-th row consists of copies of `i`
  have hrow : ∀ r, t.getD r [] = List.replicate ((shape t).getD r 0) r := by
    intro r
    rw [List.eq_replicate_iff]
    refine ⟨(getD_shape t r).symm, fun x hx => ?_⟩
    have h1 : r ≤ x := le_of_mem_getD_tableau ht r hx
    have h2 : x < r + 1 := hrowlt (r + 1) r (by omega) x hx
    omega
  have hlen : t.length = (superTab (shape t)).length := by
    have h1 : (shape t).length = t.length := by simp [shape]
    have h2 : (shape (superTab (shape t))).length = (superTab (shape t)).length := by simp [shape]
    rw [shape_superTab] at h2
    omega
  refine List.ext_getElem hlen fun r h1 h2 => ?_
  rw [← List.getD_eq_getElem _ [] h1, ← List.getD_eq_getElem _ [] h2, getD_superTab, hrow r]

/-! ### Kostka numbers -/

/-- The Kostka number `K lam mu`: the number of tableaux of shape `lam` and content
`mu`. -/
noncomputable def kostka (lam mu : List ℕ) : ℕ :=
  Nat.card {t : List (List ℕ) // IsTableau t ∧ shape t = lam ∧ evalseq (toWord t) = mu}

/-- A Kostka number `K lam mu` vanishes unless the shape `lam` dominates the content
`mu`. -/
theorem kostka_eq_zero_of_not_partdom {lam mu : List ℕ} (h : ¬ Partdom mu lam) :
    kostka lam mu = 0 := by
  have : IsEmpty {t : List (List ℕ) // IsTableau t ∧ shape t = lam ∧ evalseq (toWord t) = mu} := by
    constructor
    rintro ⟨t, ht, rfl, rfl⟩
    exact h (partdom_evalseq_toWord ht)
  exact Nat.card_of_isEmpty

/-- The Kostka number `K lam lam` is `1`: the superstandard tableau is the unique tableau
whose content equals its shape. -/
theorem kostka_self {lam : List ℕ} (h : IsPart lam) : kostka lam lam = 1 := by
  rw [kostka, Nat.card_eq_one_iff_exists]
  refine ⟨⟨superTab lam, isTableau_superTab h, shape_superTab lam,
    evalseq_toWord_superTab h⟩, ?_⟩
  rintro ⟨t, ht, hsh, hev⟩
  refine Subtype.ext ?_
  have heq := eq_superTab_of_evalseq_eq ht (by rw [hev, hsh])
  rw [hsh] at heq
  exact heq

/-! ### The content of a word and its insertion tableau -/

lemma evalseq_of_perm {u v : List ℕ} (h : u.Perm v) : evalseq u = evalseq v :=
  ext_getD_of_getLastD_ne_zero (getLastD_evalseq_ne_zero _) (getLastD_evalseq_ne_zero _)
    (fun i => by rw [getD_evalseq, getD_evalseq, h.count_eq])

/-- The shape of the insertion tableau of a word dominates the content of the word. -/
theorem partdom_evalseq_RS (w : List ℕ) : Partdom (evalseq w) (shape (RS w)) := by
  have h := partdom_evalseq_toWord (isTableau_RS w)
  rwa [evalseq_of_perm (perm_toWord_RS w)] at h

end List
