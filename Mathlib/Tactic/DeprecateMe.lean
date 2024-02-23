/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Lean.Expr.Basic
import Mathlib.Tactic.Lemma

/-!
#  Deprecation tool

Writing
```lean
deprecate to id₁ id₂ ... idₙ
theorem easy : True := .intro
```
where `id₁ id₂ ... idₙ` is a sequence of identifiers produces the `Try this` suggestion:
```lean
theorem easy : True := .intro
@[deprecated] alias d₁ := id₁
@[deprecated] alias d₂ := id₂
...
@[deprecated] alias dₙ := idₙ
```
where `d₁ d₂ ... dₙ` are the non-blacklisted declarations autogenerated by the initial command.

TODO:
* rename the old declarations with the new names
  (`easy` should become `id₁`);
* add a comment with today's date to the deprecations
  (e.g. `@[deprecated] alias d₁ := id₁ -- YYYY-MM-DD`);
* improve the formatting of the `Try this` suggestion
  (currently there are non-ideal indentations and line breaks).
-/

namespace Mathlib.Tactic.DeprecateMe

/-- Syntax for a sequence of commands. -/
syntax commandSeq := sepBy1IndentSemicolon(command)

open Lean Elab Term Command

/-- Produce the syntax for the command `@[deprecated] alias n := id`. -/
def mkDeprecationStx (id : TSyntax `ident) (n : Name) : CommandElabM (TSyntax `command) := do
  `(command| @[deprecated] alias $(mkIdent n) := $id)

/-- Returns the array of names that are in `new` but not in `old`. -/
def newNames (old new : Environment) : Array Name := Id.run do
  let mut diffs := #[]
  for (c, _) in new.constants.map₂.toList do
    unless old.constants.map₂.contains c do
      diffs := diffs.push c
  pure <| diffs

variable (newName : TSyntax `ident) in
/--
If the input command is a `theorem` or a `lemma`, then it replaces the name of the
resulting declaration with `newName` and it returns the old declaration name and the
command with the new name.

If the input command is neither a `theorem` nor a `lemma`, then it returns
`.missing` and the unchanged command.
-/
def renameTheorem : TSyntax `command → TSyntax `Lean.Parser.Command.declId × TSyntax `command
  | `(command| $dm:declModifiers theorem $id:declId $d:declSig $v:declVal) => Unhygienic.run do
    return (id, ← `($dm:declModifiers theorem $newName:declId $d:declSig $v:declVal))
  | `(command| $dm:declModifiers lemma $id:declId $d:declSig $v:declVal) => Unhygienic.run do
    return (id, ← `($dm:declModifiers lemma $newName:declId $d:declSig $v:declVal))
  | a => (default, a)

/--
Writing
```lean
deprecate to id₁ id₂ ... idₙ
theorem easy : True := .intro
```
where `id₁ id₂ ... idₙ` is a sequence of identifiers produces the `Try this` suggestion:
```lean
theorem id₁ : True := .intro
@[deprecated] alias easy := id₁
@[deprecated] alias d₂ := id₂
...
@[deprecated] alias dₙ := idₙ
```
where `easy d₂ ... dₙ` are the non-blacklisted declarations autogenerated by the initial command.

*Note.*
The "new" declarations `easy d₂ ... dₙ` are not produced in any specific order.
`deprecate to` makes an effort to match `easy` (the "visible" one) with
`id₁` (the first identifier produced by the user).
The ordering of the remaining assignment is unspecified.
However, in the case in which the initial declaration produces at most 2 non-blacklisted
declarations, then in effect there is no choice in the ordering.
-/
elab "deprecate to" id:ident* ppLine cmd:command : command => do
  let oldEnv ← getEnv
  try
    elabCommand cmd
  finally
    let newEnv ← getEnv
    let allNew := newNames oldEnv newEnv
    let skip ← allNew.filterM (·.isBlackListed)
    let mut news := allNew.filter (! · ∈ skip)
    let mut warn := #[]
    if id.size < news.size then
      warn := warn.push s!"Un-deprecated declarations: {news.toList.drop id.size}"
    if news.size < id.size then
      for i in id.toList.drop news.size do logWarningAt i ""
      warn := warn.push s!"Unused names: {id.toList.drop news.size}"
    let (oldId, newCmd) := renameTheorem id[0]! cmd
    let oldNames := ← resolveGlobalName (oldId.raw.getArg 0).getId.eraseMacroScopes
    let fil := news.filter fun n => n.toString.endsWith oldNames[0]!.1.toString
    if fil.size != 1 && oldId != default then
      logError m!"Expected to find one declaration called {oldNames[0]!.1}, found {fil.size}"
    if oldId != default then
      news := #[fil[0]!] ++ (news.erase fil[0]!)
    let pairs := id.zip news
    let msg := s!"* Pairings:\n{pairs}" ++ if skip.size != 0 then s!"\n\n* Ignoring: {skip}" else ""
    let stxs ← pairs.mapM fun (id, n) => mkDeprecationStx id n
    if newCmd == cmd then
      logWarningAt cmd m!"New declaration uses the old name {oldId.raw.getArg 0}!"
    let stxs := #[newCmd] ++ stxs
    if warn != #[] then
      logWarningAt (← getRef) m!"{warn.foldl (· ++ "\n" ++ ·) "Warnings:\n"}"
    liftTermElabM do
      Std.Tactic.TryThis.addSuggestion (header := msg ++ "\n\nTry this:\n") (← getRef)
        (← `(commandSeq| $stxs*))

end Mathlib.Tactic.DeprecateMe
