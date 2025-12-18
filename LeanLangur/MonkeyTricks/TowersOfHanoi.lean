import Mathlib
import ProofWidgets

open ProofWidgets Jsx in
#html < iframe src="https://math.iisc.ac.in/~gadgil/TowerOfHanoi/index.html" width="1200" height="600"></iframe>

namespace TowersOfHanoi

abbrev Disk := Nat

abbrev Peg := List Disk

@[grind] structure BoardState where
  leftPeg   : Peg
  middlePeg : Peg
  rightPeg  : Peg
  leftPeg_sorted   : leftPeg.SortedLT   := by grind
  middlePeg_sorted : middlePeg.SortedLT := by grind
  rightPeg_sorted  : rightPeg.SortedLT  := by grind
deriving Repr

def Disk.isCompatibleWith (disk : Disk) (peg : Peg) :=
  ∀ d ∈ peg, disk < d

infix:50 " ≺ " => Disk.isCompatibleWith

@[grind .] theorem Peg.sorted_cons (d : Disk) (peg : Peg) (peg_sorted : peg.SortedLT) (compat : d ≺ peg := by grind) :
    (d :: peg).SortedLT := by sorry

@[grind]
inductive BoardState.Transition : BoardState → BoardState → Prop where
  | leftToMiddle {leftPeg middlePeg rightPeg : Peg} {disk : Disk}
        (leftPeg_sorted : leftPeg.SortedLT := by grind) (middlePeg_sorted : middlePeg.SortedLT := by grind) (rightPeg_sorted : rightPeg.SortedLT := by grind)
        (compat_src : disk ≺ leftPeg := by grind [Disk.isCompatibleWith]) (compat_tgt : disk ≺ middlePeg := by grind [Disk.isCompatibleWith]) :
      Transition { leftPeg := disk :: leftPeg, middlePeg, rightPeg } { leftPeg, middlePeg := disk :: middlePeg, rightPeg }

  | leftToRight {leftPeg middlePeg rightPeg : Peg} {disk : Disk}
        (leftPeg_sorted : leftPeg.SortedLT := by grind) (middlePeg_sorted : middlePeg.SortedLT := by grind) (rightPeg_sorted : rightPeg.SortedLT := by grind)
        (compat_src : disk ≺ leftPeg := by grind [Disk.isCompatibleWith]) (compat_tgt : disk ≺ rightPeg := by grind [Disk.isCompatibleWith]) :
      Transition { leftPeg := disk :: leftPeg, middlePeg, rightPeg } { leftPeg, middlePeg, rightPeg := disk :: rightPeg }

  | middleToLeft {leftPeg middlePeg rightPeg : Peg} {disk : Disk}
        (leftPeg_sorted : leftPeg.SortedLT := by grind) (middlePeg_sorted : middlePeg.SortedLT := by grind) (rightPeg_sorted : rightPeg.SortedLT := by grind)
        (compat_src : disk ≺ middlePeg := by grind [Disk.isCompatibleWith]) (compat_tgt : disk ≺ leftPeg := by grind [Disk.isCompatibleWith]) :
      Transition { leftPeg, middlePeg := disk :: middlePeg, rightPeg } { leftPeg := disk :: leftPeg, middlePeg, rightPeg }

  | middleToRight {leftPeg middlePeg rightPeg : Peg} {disk : Disk}
        (leftPeg_sorted : leftPeg.SortedLT := by grind) (middlePeg_sorted : middlePeg.SortedLT := by grind) (rightPeg_sorted : rightPeg.SortedLT := by grind)
        (compat_src : disk ≺ middlePeg := by grind [Disk.isCompatibleWith]) (compat_tgt : disk ≺ rightPeg := by grind [Disk.isCompatibleWith]) :
      Transition { leftPeg, middlePeg := disk :: middlePeg, rightPeg } { leftPeg, middlePeg, rightPeg := disk :: rightPeg }

  | rightToLeft {leftPeg middlePeg rightPeg : Peg} {disk : Disk}
        (leftPeg_sorted : leftPeg.SortedLT := by grind) (middlePeg_sorted : middlePeg.SortedLT := by grind) (rightPeg_sorted : rightPeg.SortedLT := by grind)
        (compat_src : disk ≺ rightPeg := by grind [Disk.isCompatibleWith]) (compat_tgt : disk ≺ leftPeg := by grind [Disk.isCompatibleWith]) :
      Transition { leftPeg, middlePeg, rightPeg := disk :: rightPeg } { leftPeg := disk :: leftPeg, middlePeg, rightPeg }

  | rightToMiddle {leftPeg middlePeg rightPeg : Peg} {disk : Disk}
        (leftPeg_sorted : leftPeg.SortedLT := by grind) (middlePeg_sorted : middlePeg.SortedLT := by grind) (rightPeg_sorted : rightPeg.SortedLT := by grind)
        (compat_src : disk ≺ rightPeg := by grind [Disk.isCompatibleWith]) (compat_tgt : disk ≺ middlePeg := by grind [Disk.isCompatibleWith]) :
      Transition { leftPeg, middlePeg, rightPeg := disk :: rightPeg } { leftPeg, middlePeg := disk :: middlePeg, rightPeg }

theorem BoardState.Transition_symm : Symmetric BoardState.Transition := by
  sorry

abbrev BoardState.TransitionGraph : SimpleGraph BoardState where
  Adj := BoardState.Transition
  symm := BoardState.Transition_symm
  loopless := by sorry

#check BoardState.TransitionGraph.Walk

section Tactics

open Lean Elab Meta Term Tactic

macro "left_to_middle" : tactic => `(tactic| apply SimpleGraph.Walk.cons BoardState.Transition.leftToMiddle)

macro "left_to_right" : tactic => `(tactic| apply SimpleGraph.Walk.cons BoardState.Transition.leftToRight)

macro "middle_to_left" : tactic => `(tactic| apply SimpleGraph.Walk.cons BoardState.Transition.middleToLeft)

macro "middle_to_right" : tactic => `(tactic| apply SimpleGraph.Walk.cons BoardState.Transition.middleToRight)

macro "right_to_left" : tactic => `(tactic| apply SimpleGraph.Walk.cons BoardState.Transition.rightToLeft)

macro "right_to_middle" : tactic => `(tactic| apply SimpleGraph.Walk.cons BoardState.Transition.rightToMiddle)

macro "finish" : tactic => `(tactic| exact SimpleGraph.Walk.nil)

end Tactics

example : BoardState.TransitionGraph.Walk { leftPeg := [1, 2, 3], middlePeg := [], rightPeg := [] } { leftPeg := [], middlePeg := [], rightPeg := [1, 2, 3] } := by
  sorry

abbrev BoardState.swapLeftMiddle (bs : BoardState) : BoardState :=
  { leftPeg := bs.middlePeg, middlePeg := bs.leftPeg, rightPeg := bs.rightPeg }

abbrev BoardState.swapMiddleRight (bs : BoardState) : BoardState :=
  { leftPeg := bs.leftPeg, middlePeg := bs.rightPeg, rightPeg := bs.middlePeg }

abbrev BoardState.swapLeftRight (bs : BoardState) : BoardState :=
  { leftPeg := bs.rightPeg, middlePeg := bs.middlePeg, rightPeg := bs.leftPeg }

@[grind =] theorem BoardState.swapLeftMiddle_involutive (bs : BoardState) :
    bs.swapLeftMiddle.swapLeftMiddle = bs := by sorry

@[grind =] theorem BoardState.swapMiddleRight_involutive (bs : BoardState) :
    bs.swapMiddleRight.swapMiddleRight = bs := by sorry

@[grind =] theorem BoardState.swapLeftRight_involutive (bs : BoardState) :
    bs.swapLeftRight.swapLeftRight = bs := by sorry

def BoardState.TransitionGraph.Adj_iff_Adj_swapLeftMiddle (bs bs' : BoardState) :
    BoardState.TransitionGraph.Adj bs bs' ↔ BoardState.TransitionGraph.Adj bs.swapLeftMiddle bs'.swapLeftMiddle := by
  sorry

def BoardState.TransitionGraph.Adj_iff_Adj_swapMiddleRight (bs bs' : BoardState) :
    BoardState.TransitionGraph.Adj bs bs' ↔ BoardState.TransitionGraph.Adj bs.swapMiddleRight bs'.swapMiddleRight := by
  sorry

def BoardState.TransitionGraph.Adj_iff_Adj_swapLeftRight (bs bs' : BoardState) :
    BoardState.TransitionGraph.Adj bs bs' ↔ BoardState.TransitionGraph.Adj bs.swapLeftRight bs'.swapLeftRight := by
  sorry

@[grind] def BoardState.TransitionGraph.Walk_of_Walk_swapLeftMiddle {bs bs' : BoardState} :
    BoardState.TransitionGraph.Walk bs.swapLeftMiddle bs'.swapLeftMiddle → BoardState.TransitionGraph.Walk bs bs' :=
  SimpleGraph.Walk.map { toFun := BoardState.swapLeftMiddle, map_rel' := by sorry }

macro "swap_left_middle" : tactic =>
  `(tactic| (apply BoardState.TransitionGraph.Walk_of_Walk_swapLeftMiddle; dsimp only [BoardState.swapLeftMiddle]))

@[grind] def BoardState.TransitionGraph.Walk_of_Walk_swapMiddleRight {bs bs' : BoardState} :
    BoardState.TransitionGraph.Walk bs.swapMiddleRight bs'.swapMiddleRight → BoardState.TransitionGraph.Walk bs bs' :=
  SimpleGraph.Walk.map { toFun := BoardState.swapMiddleRight, map_rel' := by sorry }

macro "swap_middle_right" : tactic =>
  `(tactic| (apply BoardState.TransitionGraph.Walk_of_Walk_swapMiddleRight; dsimp only [BoardState.swapMiddleRight]))

@[grind] def BoardState.TransitionGraph.Walk_of_Walk_swapLeftRight {bs bs' : BoardState} :
    BoardState.TransitionGraph.Walk bs.swapLeftRight bs'.swapLeftRight → BoardState.TransitionGraph.Walk bs bs' :=
  SimpleGraph.Walk.map { toFun := BoardState.swapLeftRight, map_rel' := by sorry }

macro "swap_left_right" : tactic =>
  `(tactic| (apply BoardState.TransitionGraph.Walk_of_Walk_swapLeftRight; dsimp only [BoardState.swapLeftRight]))

def Peg.isCompatibleWith (peg peg' : Peg) := ∀ d ∈ peg, d ≺ peg'

@[grind .] theorem Peg.append_sorted_of_compat (peg peg' : Peg)
    (peg_sorted : peg.SortedLT) (peg'_sorted : peg'.SortedLT)
    (compat : peg.isCompatibleWith peg' := by grind) : (peg ++ peg').SortedLT := by
  sorry

@[grind →] theorem Peg.isCompatible_with_of_append_SortedLT (peg peg' : Peg)
    (append_sorted : (peg ++ peg').SortedLT := by grind) :
    peg.isCompatibleWith peg' := by
  sorry

@[grind]
def BoardState.isCompatibleWith (bs bs' : BoardState) : Prop :=
  (bs.leftPeg   |>.isCompatibleWith bs'.leftPeg)   ∧
  (bs.leftPeg   |>.isCompatibleWith bs'.middlePeg) ∧
  (bs.leftPeg   |>.isCompatibleWith bs'.rightPeg)  ∧
  (bs.middlePeg |>.isCompatibleWith bs'.leftPeg)   ∧
  (bs.middlePeg |>.isCompatibleWith bs'.middlePeg) ∧
  (bs.middlePeg |>.isCompatibleWith bs'.rightPeg)  ∧
  (bs.rightPeg  |>.isCompatibleWith bs'.leftPeg)   ∧
  (bs.rightPeg  |>.isCompatibleWith bs'.middlePeg) ∧
  (bs.rightPeg  |>.isCompatibleWith bs'.rightPeg)

abbrev BoardState.append (bs bs' : BoardState)
  (compat : bs.isCompatibleWith bs' := by grind [Peg.isCompatibleWith, Disk.isCompatibleWith]) : BoardState :=
  { leftPeg   :=   bs.leftPeg ++ bs'.leftPeg
    middlePeg := bs.middlePeg ++ bs'.middlePeg
    rightPeg  :=  bs.rightPeg ++ bs'.rightPeg }

infixr:70 " ⧏ " => BoardState.append

@[grind .] theorem BoardState.isCompatibleWith_of_Adj {bs bs' : BoardState} (rel : TransitionGraph.Adj bs bs')
    (β : BoardState) : bs.isCompatibleWith β → bs'.isCompatibleWith β := by
  sorry

theorem BoardState.isCompatibleWith_of_Walk {bs bs' β : BoardState} (walk : TransitionGraph.Walk bs bs')
    : bs.isCompatibleWith β → bs'.isCompatibleWith β := by
  induction walk <;> sorry

@[grind →] theorem BoardState.TransitionGraph.Adj_append_of_Adj {bs bs' β : BoardState}
    (compat : bs.isCompatibleWith β := by grind) (rel : TransitionGraph.Adj bs bs') : TransitionGraph.Adj (bs ⧏ β) (bs' ⧏ β) := by
  sorry

def BoardState.TransitionGraph.Walk_append_of_Walk {bs bs' : BoardState} (walk : TransitionGraph.Walk bs bs') (β : BoardState)
    (compat : bs.isCompatibleWith β := by grind [Disk.isCompatibleWith, Peg.isCompatibleWith]) :
      have : bs'.isCompatibleWith β := isCompatibleWith_of_Walk walk compat;
      -- the preceding `have` statement is necessary for the theorem statement to compile
      TransitionGraph.Walk (bs ⧏ β) (bs' ⧏ β) :=
  match walk with
  | .nil => .nil
  | .cons rel walk' =>.cons (by sorry) (TransitionGraph.Walk_append_of_Walk walk' β)

#check SimpleGraph.Walk.length_nil
#check SimpleGraph.Walk.length_cons
@[grind =]
theorem BoardState.TransitionGraph.Walk_append_of_Walk_length {bs bs' : BoardState} (walk : TransitionGraph.Walk bs bs') (β : BoardState)
    (compat : bs.isCompatibleWith β := by grind) : (BoardState.TransitionGraph.Walk_append_of_Walk walk β).length = walk.length := by
  induction walk <;> sorry

/--
Example:

```
 BoardState.TransitionGraph.Walk
  { leftPeg := List.range (n + 1), middlePeg := [], rightPeg := [] }
  { leftPeg := [], middlePeg := [], rightPeg := List.range (n + 1) }

split_as { leftPeg := .range n, middlePeg := [], rightPeg := [] } ⧏ { leftPeg := [n], middlePeg := [], rightPeg := [] }

BoardState.TransitionGraph.Walk
  ({ leftPeg := List.range n, middlePeg := [], rightPeg := [] } ⧏
      { leftPeg := [n], middlePeg := [], rightPeg := [] })
  { leftPeg := [], middlePeg := [], rightPeg := List.range (n + 1) }
```
-/
macro "split_as" bs:term : tactic =>
  `(tactic| refine SimpleGraph.Walk.copy (u := $bs) ?_ (by grind [List.range_succ]) rfl)

/-- The opposite of `split_as` -/
macro "merge_split" : tactic =>
  `(tactic| simp only [BoardState.append, List.append, List.append_nil, List.nil_append, ← List.range_succ, Nat.succ_eq_add_one])

/-!
Reduces proving
```
BoardState.TransitionGraph.Walk (bs ⧏ β) (bs' ⧏ β)
```
to
```
BoardState.TransitionGraph.Walk bs bs'
```
-/
macro "clear_append" : tactic =>
  `(tactic| refine BoardState.TransitionGraph.Walk_append_of_Walk ?_ _)

attribute [local grind] List.sortedLT_range List.mem_range in
def puzzle (n : Nat) : BoardState.TransitionGraph.Walk
    { leftPeg := .range n, middlePeg := [], rightPeg := [] }
    { leftPeg := [], middlePeg := [], rightPeg := .range n } := by
  match n with
  | 0 => finish
  | n + 1 =>
    have ind_solution := puzzle n
    split_as { leftPeg := .range n, middlePeg := [], rightPeg := [] } ⧏ { leftPeg := [n], middlePeg := [], rightPeg := [] }
    trans ({ leftPeg := [], middlePeg := .range n, rightPeg := [] } ⧏ { leftPeg := [n], middlePeg := [], rightPeg := [] })
    · clear_append
      swap_middle_right
      exact ind_solution
    · merge_split
      left_to_right
      split_as { leftPeg := [], middlePeg := .range n, rightPeg := [] } ⧏ { leftPeg := [], middlePeg := [], rightPeg := [n] }
      trans ({ leftPeg := [], middlePeg := [], rightPeg := .range n } ⧏ { leftPeg := [], middlePeg := [], rightPeg := [n] })
      · clear_append
        swap_left_middle
        exact ind_solution
      · merge_split
        finish

end TowersOfHanoi
