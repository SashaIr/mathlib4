/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.DFinsupp.Basic
import Mathlib.Data.Finsupp.Notation
import Mathlib.Data.List.Sigma

/-!
# Notation for `DFinsupp`

This file extends the existing `fun₀ | 3 => a | 7 => b` notation to work for `DFinsupp`,
which desugars to `DFinsupp.update` and `DFinsupp.single`,
in the same way that `{a, b}` desugars to `insert` and `singleton`.

Note that this syntax is for `Finsupp` by default, but works for `DFinsupp` if the expected type
is correct.
-/

namespace DFinsupp

open Lean
open Lean.Parser
open Lean.Parser.Term

extend_docs Finsupp.fun₀ after
  "If the expected type is `Π₀ i, α i` (`DFinsupp`),
  then this is notation for `DFinsupp.single` and  `Dfinsupp.update` instead."

macro_rules
  | `(term| fun₀ $x:matchAlt*) => do
    let mut stx : Term ← `(0)
    let mut fst : Bool := true
    for xi in x do
      for xii in (← Elab.Term.expandMatchAlt xi) do
        match xii with
        | `(matchAltExpr| | $pat => $val) =>
          if fst then
            stx ← `(DFinsupp.single $pat $val)
          else
            stx ← `(DFinsupp.update $pat $stx $val)
          fst := false
        | _ => Macro.throwUnsupported
    pure stx

/-- Unexpander for the `fun₀ | i => x` notation. -/
@[app_unexpander Finsupp.single]
def singleUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $pat $val) => `(fun₀ | $pat => $val)
  | _ => throw ()

/-- Unexpander for the `fun₀ | i => x` notation. -/
@[app_unexpander Finsupp.update]
def updateUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $pat $val) => match f with
    | `(fun₀ $xs:matchAlt*) => `(fun₀ $xs:matchAlt* | $pat => $val)
    | _ => throw ()
  | _ => throw ()


/-- Display `DFinsupp` using `fun₀` notation. -/
unsafe instance {α : Type*} {β : α → Type*} [Repr α] [∀ i, Repr (β i)] [∀ i, Zero (β i)] :
    Repr (Π₀ a, β a) where
  reprPrec f p :=
    let vals :=
      ((f.support'.unquot.val.map fun i => (repr i, repr (f i))).filter
        (fun p => toString p.2 != "0")).unquot
    let vals_dedup := vals.foldl (fun xs x => x :: xs.eraseP (toString ·.1 == toString x.1)) []
    if vals.length = 0 then
      "0"
    else
      let ret := "fun₀" ++
        Std.Format.join (vals_dedup.map <|
          fun a => f!" | " ++ a.1 ++ f!" => " ++ a.2)
      if p ≥ leadPrec then Format.paren ret else ret

end DFinsupp
