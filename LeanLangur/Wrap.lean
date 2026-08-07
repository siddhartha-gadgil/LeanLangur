import Mathlib

open Nat

variable (comb : Nat → Nat → Nat)

class CombDef : Prop where
    comb_eqn (n m : Nat) : n ! * comb n m = m ! * (n -m)!

variable [inst_CombDef : CombDef comb]

theorem comb_eqn (n m : Nat) :
    n ! * comb n m = m ! * (n -m)! := by
    apply inst_CombDef.comb_eqn

def combIO (n m: IO Nat): IO Nat := do
    return (← n) ! / ((← m) ! * ((← n)- (← m))!)

def twoPowN (n: Nat) : Nat :=
    List.range (n + 1) |>.foldl
        (fun k acc ↦ acc + comb n k) 0

#check twoPowN

-- Issue: extract `ℕ → ℕ → ℕ` from function that is IO valued in `IO`.
def twoPowNIO (n: IO Nat) : IO Nat :=
    do
    let comb : Nat → Nat → Nat ← do
        pure <| sorry
    return twoPowN comb (← n)

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

#eval doubleM (mode := .run) 3

#check doubleM (mode := .run) 3

example : IO Nat := doubleM (mode := .run) 3

namespace reference_implementation

scoped instance : DoubleM LeanMode.prove where
    doubleM n := n + n

scoped instance : DoubleM mode := match mode with
    | LeanMode.run => inferInstanceAs (DoubleM LeanMode.run)
    | LeanMode.prove => inferInstanceAs (DoubleM LeanMode.prove)

example : doubleM (mode := .prove) 3 = 6 := by
    rfl

def timesFourM (n: Nat) : OutM Nat := do
    let x ← doubleM  n
    doubleM (mode:= mode) x

end reference_implementation

namespace abstraction

variable [inst: DoubleM .prove]

scoped instance : DoubleM mode := match mode with
    | LeanMode.run => inferInstanceAs (DoubleM LeanMode.run)
    | LeanMode.prove => inferInstanceAs (DoubleM LeanMode.prove)

/--
error: Tactic `rfl` failed: The left-hand side
  doubleM 3
is not definitionally equal to the right-hand side
  6

comb : ℕ → ℕ → ℕ
inst_CombDef : CombDef comb
mode : LeanMode
inst : DoubleM LeanMode.prove
⊢ doubleM 3 = 6
-/
#guard_msgs in
example : doubleM (mode := .prove) 3 = 6 := by
    rfl

def timesFourM (n: Nat) : OutM Nat := do
    let x ← doubleM  n
    doubleM (mode:= mode) x

end abstraction
