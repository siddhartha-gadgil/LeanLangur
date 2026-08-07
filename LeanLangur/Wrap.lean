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
