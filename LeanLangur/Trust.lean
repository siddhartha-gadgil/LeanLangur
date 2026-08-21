import Mathlib

variable (P : Prop)

theorem weHaveP [Fact P] : P := by simp [Fact.elim]

-- Should also include a variable for the instance if we do not prove. However, we do not want a clash if we implement.
macro "trust" p:term "as" n:ident : command => do
    `(command| theorem $n [Fact $p] : $p := by simp [Fact.elim])

macro "prove"  p:term ":=" pf:term : command => do
    `(command| instance : Fact $p :=⟨$pf⟩)

macro "use" p:term : command => do
    `(command| variable [Fact $p])

trust P as go

trust (2 + 2 = 4) as obvious


prove 2 + 2 = 4 := by
    simp

#check go

/--
error: failed to synthesize
  Fact P

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example : P := by
    apply go

section

use P

example : P := by
    apply go

end

prove P := sorry

example : P := by
    apply go

variable [trustP : Fact P]

#synth Fact P


open Lean

#check Meta.kabstract

#check Meta.transform

#check Core.transform

#check Expr.replace

declare_syntax_cat commandSeqCat
syntax commandSeq := sepBy1IndentSemicolon(command)
syntax commandSeq : commandSeqCat


variable [Monad m] [MonadQuotation m]
def toCommandSeq : Array (TSyntax `command) → m (TSyntax `commandSeq)
  | cs => `(commandSeq| $cs*)

def commands : TSyntax `commandSeq → Array (TSyntax `command)
  | `(commandSeq| $cs*) => cs
  | _ => #[]

-- Does not work as a command.
macro "#one_two" : commandSeqCat => do
    let c1 ← `(command| def one := 1)
    let c2 ← `(command| def two := 2)
    let seq ← toCommandSeq #[c1, c2]
    `(commandSeqCat| $seq:commandSeq)

variable (n: Nat)

/-- error: invalid declaration name `n`, there is a section variable with the same name -/
#guard_msgs in
def n: Nat := 1

def transformTermsIOtoId (name newName: Name) : MetaM Syntax.Command := do
  -- Create two arbitrary local constants for illustration
  let sourceTerm := mkConst ``IO
  let targetTerm := mkConst ``Id

  let decl ← getConstInfo name
  let typeExpr := decl.type
  let valueExpr := decl.value?.getD (mkConst ``Unit)
  let newTypeExpr ← Meta.transform typeExpr (pre := fun subExpr => do
    if subExpr == sourceTerm then
        -- Found an exact match; swap it and stop traversing this branch
        return .done targetTerm
    else
        -- Not a match; move on to check the children
        return .continue
    )
  let newValueExpr ← Meta.transform valueExpr (pre := fun subExpr => do
    if subExpr == sourceTerm then
        -- Found an exact match; swap it and stop traversing this branch
        return .done targetTerm
    else
        -- Not a match; move on to check the children
        return .continue
    )
  let newId := mkIdent newName
  let newTypeSyntax ← PrettyPrinter.delab newTypeExpr
  let newValueSyntax ← PrettyPrinter.delab newValueExpr
  let cmd ← `(command| def $newId : $newTypeSyntax := $newValueSyntax)
  return cmd

open Lean Meta Elab Term Command Tactic
def eg (n: Nat) : IO Nat := do
    return n + 1

syntax (name := transformIOtoId) "abstract" ident "as" ident : command

@[command_elab transformIOtoId]
def elabTransformIOtoId : CommandElab :=
  fun stx =>
    match stx with
    | `(abstract $name:ident as $newName:ident) => do
        let command ← liftTermElabM  do
            let cmd ← transformTermsIOtoId name.getId newName.getId
            TryThis.addSuggestion stx cmd
            pure cmd
        elabCommand command
    | _ => throwUnsupportedSyntax

abstract eg as egAbs

#check egAbs

example (n: Nat) : egAbs (egAbs n) = n + 2 := by
    rfl


-- From Gemini
open Meta
def transformTermsDemo : MetaM Unit := do
  -- Create two arbitrary local constants for illustration
  let sourceTerm := mkNatLit 42
  let targetTerm := mkStrLit "forty-two" -- Changing type from Nat to String

  -- Target expression: (42, 42)
  let pairExpr ← mkAppM ``Prod.mk #[sourceTerm, sourceTerm]
  IO.println s!"Original Pair: {← ppExpr pairExpr}"

  -- Transform the expression
  let resultExpr ← Meta.transform pairExpr (post := fun subExpr => do
    if subExpr == sourceTerm then
      -- If we match our named term, replace it with the new one
      return .done targetTerm
    else
      -- Otherwise, keep traversing recursively
      return .continue
  )

  IO.println s!"Transformed Pair: {← ppExpr resultExpr}"

#eval transformTermsDemo

def transformTermsDemo' : MetaM Unit := do
  -- Create two arbitrary local constants for illustration
  let sourceTerm := mkNatLit 42
  let targetTerm := mkStrLit "forty-two" -- Changing type from Nat to String

  -- Target expression: (42, 42)
  let pairExpr ← mkAppM ``Prod.mk #[sourceTerm, sourceTerm]
  IO.println s!"Original Pair: {← ppExpr pairExpr}"

  -- Transform the expression
  let resultExpr ← Meta.transform pairExpr (pre := fun subExpr => do
    if subExpr == sourceTerm then
        -- Found an exact match; swap it and stop traversing this branch
        return .done targetTerm
    else
        -- Not a match; move on to check the children
        return .continue
    )


  IO.println s!"Transformed Pair: {← ppExpr resultExpr}"

#eval transformTermsDemo'
