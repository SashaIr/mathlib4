# Young tableaux, symmetric functions and the characters of `Sₙ` — a contribution to Mathlib

*A guide for Mathlib reviewers.  It says what this project contains, how it is meant to reach
Mathlib, and what we would like maintainers to decide.*

---

## 1. What this project is

This is a port to Mathlib of [Coq-Combi](https://github.com/math-comp/Coq-Combi)
(F. Hivert et al.), the Coq/mathcomp development of the combinatorics of integer partitions,
Young tableaux and symmetric functions, together with the representation-theoretic results that
crown it. It also includes an extra commit to define q-analogs. In its current state it is

* **190 new modules**, about **47 000 added lines**, and **15 pre-existing files** that it extends
  or adapts (no file is deleted from Mathlib);
* free of `sorry`, of `axiom`, of `@[implemented_by]` and of `native_decide`;
* written against the module system (`module` / `public import`), with Mathlib's headers,
  docstrings, `## Main results` sections and bibliography entries.

### The headline results

| result                                                                     | statement in the library                                                                      |
| -------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------- |
| q-analogs                                                                  | `Mathlib/Combinatorics/QAnalog`                                                             |
| Bell numbers count set partitions                                          | `Finpartition.card_finpartition`                                                            |
| The Tamari lattice                                                         | `Tree.TamariOfCard.instLattice`                                                             |
| Dyck words: the cycle lemma and the rotation action                        | `Mathlib/Combinatorics/Enumerative/DyckWord/Rotation.lean`                                  |
| Erdős–Szekeres for lists                                                 | `List.erdos_szekeres` (the Archive's `Theorems100.erdos_szekeres` is now derived from it) |
| Robinson–Schensted is a bijection                                         | `Young.RS_RSQ_bijOn`                                                                        |
| `∑_μ (f^μ)² = n!`                                                    | `Nat.Partition.sum_sq_numStdTab`, `YoungDiagram.sum_sq_numStdTab`                         |
| Greene's theorem                                                           | `Young.greeneRow_eq_sum_rowLen`, `Young.greeneCol_eq_sum_colLen`                          |
| The plactic monoid, and RS as its quotient map                             | `Mathlib/Combinatorics/Young/Plactic/`                                                      |
| The hook length formula                                                    | `YoungDiagram.numStdTab_mul_hookProd`, `YoungDiagram.numStdTab_eq_factorial_div_hookProd` |
| The Coxeter presentation of`Sₙ`, Bruhat and weak orders                 | `Equiv.Perm.permCoxeterSystem`, `Mathlib/GroupTheory/Perm/SymmetricGroup/`                |
| The`m`, `e`, `h`, `p`, `s` bases of the symmetric polynomials    | `Mathlib/RingTheory/MvPolynomial/Symmetric/Basis/`                                          |
| Pieri, dual Pieri, Jacobi–Trudi and its dual                              | `Mathlib/RingTheory/MvPolynomial/Symmetric/Schur/`                                          |
| The Cauchy identities and the Hall inner product                           | `Mathlib/RingTheory/MvPolynomial/Symmetric/Cauchy/`, `.../Basis/HallInnerProduct.lean`    |
| The Littlewood–Richardson rule                                            | `Young.lrCoeff`, `SymFunc.schurFunc_mul_schurFunc_youngDiagram`                           |
| The Murnaghan–Nakayama rule                                               | `SymFunc.psymFunc_mul_schurFunc`, `Equiv.Perm.schurChar_mnRule_ribbon`                    |
| The ring of symmetric functions                                            | `Mathlib/RingTheory/SymmetricFunctions/`                                                    |
| The Schur class functions are exactly the irreducible characters of`Sₙ` | `Equiv.Perm.isSimpleChar_schurCharCast`, `Equiv.Perm.schurCharCast_injective`             |

Supporting theory that is of independent interest: set partitions and Stirling numbers, ordered
trees, integer compositions and integer vectors, crystals for type `A`, shuffles and shifted
shuffles of words, standardization, Yamanouchi words, Kostka numbers, and a hundred-odd
general-purpose `List` lemmas.

---

## 2. How it is meant to reach Mathlib: a stack of 23 PRs

A single 47 000-line PR is not reviewable, so the contribution is cut into **23 pull requests, each
at most ~3 000 lines, each import-closed** (it compiles on top of its predecessors) **and each
about one subject**. Each patch begins with the intended PR title and
description (new files, changed files and why), and applying `pr-01 … pr-22` in order to the stated
base reproduces the goal end state exactly.

| #  | patch                                | subject                                                                                                 | size |
| -- | ------------------------------------ | ------------------------------------------------------------------------------------------------------- | ---- |
| 0  | `pr-00-qanalogs`                   | q-analogs                                                                                               | 959  |
| 1  | `pr-01-prerequisites`              | shuffles, permuted lists, fibers of a map, lattice of finite sets, plus ~30 general`Data/List` lemmas | 969  |
| 2  | `pr-02-set-partitions`             | set partitions of a finite type, Bell and Stirling numbers                                              | 1064 |
| 3  | `pr-03-dyck-words`                 | the list model of Dyck words, rotation and the cycle lemma                                              | 821  |
| 4  | `pr-04-tamari-lattice`             | ordered trees, Tamari vectors, the Tamari lattice                                                       | 1791 |
| 5  | `pr-05-erdos-szekeres`             | Erdős–Szekeres for lists; the Archive proof is re-derived from it                                     | 283  |
| 6  | `pr-06-partition-list-model`       | integer partitions as lists: conjugation, dominance, inclusion, corners                                 | 2911 |
| 7  | `pr-07-partition-dictionaries`     | ribbons, vertical strips, and the dictionaries with`YoungDiagram` and `Nat.Partition`               | 1401 |
| 8  | `pr-08-tableaux-insertion`         | tableaux, Schensted insertion, Greene invariants                                                        | 2702 |
| 9  | `pr-09-greene-theorem`             | Greene's theorem, and invariance under the plactic congruence                                           | 2988 |
| 10 | `pr-10-rsk-bijection`              | recording tableaux; the Robinson–Schensted bijection and its enumeration                               | 3009 |
| 11 | `pr-11-standardization-kostka`     | standardization, Yamanouchi words, Kostka numbers, the plactic monoid                                   | 2974 |
| 12 | `pr-12-rsk-symmetry`               | symmetry of the correspondence, reverse words, shifted shuffles                                         | 1188 |
| 13 | `pr-13-compositions-and-vectors`   | integer compositions and integer vectors                                                                | 449  |
| 14 | `pr-14-crystals-and-lr-rule`       | crystals of type`A`, and the combinatorial Littlewood–Richardson rule                                | 2345 |
| 15 | `pr-15-hook-length-formula`        | the hook length formula (hook walks, Frobenius identity)                                                | 2538 |
| 16 | `pr-16-symmetric-group`            | `Sₙ`: cycle types, Coxeter presentation, Bruhat order, weak order                                    | 2891 |
| 17 | `pr-17-schur-polynomials`          | Schur polynomials, the monomial basis, alternants                                                       | 2899 |
| 18 | `pr-18-power-sums-and-pieri`       | power sums, cycle index, the Pieri rules, bialternants                                                  | 3002 |
| 19 | `pr-19-cauchy-and-hall`            | the Cauchy formulas, the Hall inner product, ω                                                         | 2737 |
| 20 | `pr-20-jacobi-trudi-and-mn`        | Jacobi–Trudi and its dual, LR symmetry, Murnaghan–Nakayama                                            | 2632 |
| 21 | `pr-21-symmetric-functions`        | the ring of symmetric functions                                                                         | 1149 |
| 22 | `pr-22-symmetric-group-characters` | characters of finite groups, Frobenius characteristic, Schur characters                                 | 2760 |

(Sizes are added lines of the patch, including the changes to pre-existing files and to
`Mathlib.lean`.)

### Practical points about the stack

* **`Mathlib.lean` and `docs/references.bib`** change in every PR: each adds the import lines of
  its own modules and the 1–3 bibliography entries its files cite (8 entries in total:
  `fulton1997`, `greene1974`, `greene-nijenhuis-wilf1979`, `hivert-coqcombi`, `knuth1970`,
  `lascoux-schutzenberger1981`, `macdonald1995`, `sagan2001`).
* **One `git mv`.**  PR 3 moves `Combinatorics/Enumerative/DyckWord.lean` to
  `Enumerative/DyckWord/Defs.lean` with **no content change**, and leaves a `deprecated_module`
  stub behind, so downstream imports keep working.  The patch is generated with rename detection,
  so it shows as a move.
* **Nothing is deleted from Mathlib**, and no existing declaration changes its statement.  The one
  proof that is rewritten is `Theorems100.erdos_szekeres` in the Archive, which becomes a
  three-line consequence of `List.erdos_szekeres`.

## 3. Design decisions a reviewer should know about

These are the choices we expect to be discussed; all of them are already implemented, and each can
be revisited.

1. **Two representations, and a stated policy.**  Young diagrams, partitions, tableaux and Dyck
   words all exist in Mathlib in a bundled form (`YoungDiagram`, `Nat.Partition`,
   `SemistandardYoungTableau`, `DyckWord`) and, in this development, in a list form
   (`μ : List ℕ` with `Young.IsPart μ`, `t : List (List ℕ)` with `Young.IsTableau t`, …).  The
   policy we adopted, and wrote into `docs/Combi.lean`: **the bundled types are the user-facing
   API** — every headline theorem is available for them — while **the list models are the
   computational layer**, because essentially every proof here is an induction on a word or on the
   rows of a tableau.  Explicit dictionaries connect the two (`YoungDiagram.equivListRowLens`,
   `Young.listPartEquivNatPartition`, `Nat.Partition.partsList`, …).
2. **A new top-level namespace `Young`.**  The list layer originally added some 1 600 declarations
   to the root `List` namespace.  They now live in `Young` (`Young.IsPart`, `Young.IsTableau`,
   `Young.RS`, `Young.greeneRow`, …), and the root `List` namespace keeps only what is about lists
   as such (`List.IsDyckWord`, `List.IsShuffle`, `List.erdos_szekeres`).  A new top-level namespace
   is a maintainer decision; we flag it early, in PR 6, where it first appears.
3. **Character theory over an arbitrary algebraically closed field of characteristic zero.**  The
   classical statements over `ℂ` are the case `K := ℂ`, instantiated by the user.  This is what
   keeps `RepresentationTheory` from importing `Analysis` (for `Complex.isAlgClosed`), i.e. it
   avoids a new heavy import edge.
4. **Layering.**  There is no `Combinatorics → RingTheory` edge: the combinatorial statements of
   the Littlewood–Richardson and Murnaghan–Nakayama rules live in `Combinatorics/Young/`, and the
   symmetric-function statements in `RingTheory/`.  General-purpose material is filed where it
   belongs (`Data/List/`, `Data/Fintype/`, `Order/`), which is what PR 1 is.
5. **The index type of the bases.**  The monomial and Schur bases in `m` variables are indexed by
   partitions of `n` with at most `m` parts.  That is a genuine restriction when `m < n`, so it is a
   named type, `Young.PartLengthLe n m`, living in the partition layer, with coercions both ways
   (`Young.PartLengthLe.toPartition`, `Nat.Partition.toPartLengthLe`) and an equivalence with
   `Nat.Partition n` when `n ≤ m`.
6. **Naming and notation conventions.**  Greek letters are written as Greek letters (`σ`, `τ`, `μ`,
   `ν`, `ρ`, `χ`), never spelled out.  Partitions are named `μ`, then `ν`, then `ρ` — Lean forbids
   `λ` as an identifier, and `Λ` means the exterior algebra — and docstrings use the same letters as
   the code, so the prose and the binders of a declaration agree.

---

## 4. Status: verified against current master

The whole contribution was rebased onto current upstream master and **`lake build Mathlib docs`
completes successfully** there (9116 jobs), with no `sorry` and no new axiom.  `lake exe mk_all --check` reports no update necessary, `lake exe lint-style` is clean, and the environment linter
(`lake lint`) reports a single finding, in a pre-existing file unrelated to this work
(`Mathlib/FieldTheory/Galois/IsGaloisGroup.lean`).

The split is checked mechanically as well: every one of the 23 commits is import-closed — each
module it adds has all of its imports already present — and the 23 patches apply in order to the
stated base and reproduce, byte for byte, the tree that builds.  Since a module's elaboration only
depends on its transitive imports, and those have exactly the content they have in the end state,
each PR of the stack compiles on top of its predecessors.

## 5. Questions for maintainers

1. **`Young` as a top-level namespace** (design decision 2) — accept it, or nest the list layer
   somewhere else?
2. **Ten of the lemmas added to pre-existing files have no user inside the contribution**: the
   three of `SemistandardTableau.lean`, six of the nine of `YoungDiagram.lean`, `Finpartition.sup_eq_iff`
   and `List.split_three_getElem`.  They complete the dictionaries they belong to; we are happy to
   drop them if reviewers prefer.
3. **The old `Combinatorics/Enumerative/Partition.lean` path.**  Upstream split that module into
   `Partition/Basic.lean` and retired the stub.  We follow upstream and do **not** re-create it; the
   development tree still contains a stub, which is listed as not shipping.
4. **PR granularity.**  3 000 lines is our budget; if reviewers prefer 1 500, re-running
   `pr_split_check.py --chunks --budget 1500` and `make_pr_diffs.py` produces a finer stack with no
   manual work.
5. **Attribution.**  Most of the new files are authored `Alessandro Iraci, Aristotle (Harmonic)` and cite
   Coq-Combi (`hivert-coqcombi`) in their `## References`; each module also names the Coq theory it
   comes from.  Tell us if a different attribution convention is wanted.
