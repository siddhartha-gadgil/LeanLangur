import Mathlib

open Nat

inductive LeanMode
    | run | prove

variable {mode : LeanMode}

abbrev Out := match mode with
    | LeanMode.run => IO
    | LeanMode.prove => Id

@[reducible]
instance {mode : LeanMode} : Monad <| Out (mode := mode) :=
    match mode with
    | LeanMode.run => inferInstanceAs (Monad IO)
    | LeanMode.prove => inferInstanceAs (Monad Id)


def doubleM' {mode: LeanMode} (n: Nat) : Out (mode := mode) Nat :=
    return n + n

#check doubleM'


example : doubleM' (mode := .prove) 3 = 6 := by
    rfl

macro "OutM" : term =>
    let modeId := Lean.mkIdent `mode
    `(Out (mode := $modeId))

class DoubleM (mode: LeanMode) where
    doubleM : Nat → OutM Nat

def doubleM  [inst: DoubleM mode] (n: Nat) : OutM Nat :=
    inst.doubleM n

instance : DoubleM LeanMode.run where
    doubleM n := return n + n

instance [instAbs : DoubleM .prove] : DoubleM mode := match mode with
    | LeanMode.run => inferInstanceAs (DoubleM LeanMode.run)
    | LeanMode.prove => instAbs

def timesFourM [DoubleM .prove] (n: Nat) : OutM Nat := do
    let x ← doubleM  n
    doubleM (mode:= mode) x

#eval doubleM (mode := .run) 3

#check doubleM (mode := .run) 3

example : IO Nat := doubleM (mode := .run) 3

namespace abstraction

variable [inst: DoubleM .prove]

-- We cannot allow a branch to be abstract.
/-- error: Cannot evaluate, contains free variable `inst` -/
#guard_msgs in
#eval timesFourM (mode := .run) 3

/--
error: Tactic `rfl` failed: The left-hand side
  doubleM 3
is not definitionally equal to the right-hand side
  6

mode : LeanMode
inst : DoubleM LeanMode.prove
⊢ doubleM 3 = 6
-/
#guard_msgs in
example : doubleM (mode := .prove) 3 = 6 := by
    rfl


end abstraction


namespace reference_implementation

scoped instance : DoubleM LeanMode.prove where
    doubleM n := n + n

example : doubleM (mode := .prove) 3 = 6 := by
    rfl

#eval timesFourM (mode := .run) 3



end reference_implementation

namespace noncomputable_implementation

noncomputable scoped instance : DoubleM LeanMode.prove where
    doubleM n := n + n

example : doubleM (mode := .prove) 3 = 6 := by
    rfl

-- This is a problem. One branch being noncomputable makes the whole function noncomputable, even though the other branch is computable.
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'instDoubleMProve', which is 'noncomputable'
-/
#guard_msgs in
#eval timesFourM (mode := .run) 3

end noncomputable_implementation

namespace sorry_implementation

scoped instance : DoubleM LeanMode.prove where
    doubleM := sorry


-- We cannot also use sorry in the proof branch to avoid implementation.
/--
error: cannot evaluate code because 'sorry_implementation.instDoubleMProve' uses 'sorry' and/or contains errors
-/
#guard_msgs in
#eval! timesFourM (mode := .run) 3

end sorry_implementation

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
