import LeanLangur.Basic -- imports definitions and theorems used below

/-!
## Prerequisite files

* None in the README dependency diagram.

## Main concepts introduced

* stack-machine instructions.
* safe evaluators.
* validity predicates.
-/

/-!
# Stack Machine

This module defines a simple stack-based machine with instructions for pushing values,
popping values, and performing addition. It includes both unsafe and safe (option-returning)
execution engines, as well as a verified evaluator that uses a `ValidProgram` predicate.
-/

namespace langur -- starts a namespace to group the tutorial definitions

namespace stack_machine -- starts a namespace to group the tutorial definitions

/--
Instructions for the stack machine.
-/
inductive Instr -- declares the inductive type or proposition `Instr`
  | push (n : Nat) -- declares another constructor or syntax alternative
  | pop -- declares another constructor or syntax alternative
  | add -- declares another constructor or syntax alternative
  deriving Repr -- asks Lean to generate standard instances automatically

open Instr -- opens names so constructors or helpers can be written unqualified

/-- A stack is represented as a list of natural numbers. -/
abbrev Stack := List Nat -- introduces `Stack` as a reducible abbreviation

/-- A program is a list of instructions. -/
abbrev Program := List Instr -- introduces `Program` as a reducible abbreviation

/--
Unsafe evaluation of a program.
Assumes the stack has enough elements for `pop` and `add` operations.
-/
def eval! (p: Program) (s: Stack) : Stack := -- defines `eval!`
  match p with -- splits computation into cases by pattern matching
  | [] => s -- matches the empty list and returns `s`
  | push n :: p' => eval! p' (n :: s) -- matches a program beginning with `push n` and evaluates the rest with `n` pushed on the stack
  | pop :: p' => -- matches a program beginning with `pop` and evaluates the rest after dropping the stack top
      eval! p' s.tail!
  | add :: p' => -- matches a program beginning with `add` and evaluates the rest after replacing the top two stack entries by their sum
      let x := s.head! -- binds an intermediate value for the following expression
      let y := s.tail!.head! -- binds an intermediate value for the following expression
      eval! p' ((x + y) :: s.tail!.tail!)

/--
Safe evaluation of a program using `Option`.
Returns `none` if an instruction is executed on an insufficient stack.
-/
def eval? (p: Program) (s: Stack) : Option Stack := -- defines `eval?`
  match p with -- splits computation into cases by pattern matching
  | [] => some s -- matches the empty list and returns `some s`
  | push n :: p' => eval? p' (n :: s) -- matches a program beginning with `push n` and safely evaluates the rest with `n` pushed on the stack
  | add :: p' => -- matches a program beginning with `add` and checks whether the stack has two entries to add
      match s with -- splits computation into cases by pattern matching
      | x :: y :: zs => eval? p' ((x + y) :: zs) -- matches a list with at least two elements and returns `eval? p' ((x + y) :: zs)`
      | _ => none -- matches any remaining form and returns `none`
  | pop :: p' => -- matches a program beginning with `pop` and checks whether the stack has an entry to remove
      match s with -- splits computation into cases by pattern matching
      | _ :: ys => eval? p' ys -- matches a nonempty list and returns `eval? p' ys`
      | _ => none -- matches any remaining form and returns `none`

/--
Inductive predicate for a valid program given an initial stack size.
Ensures that the stack will never underflow during execution.
-/
@[grind cases] -- annotation controlling elaboration, simplification, or automation
inductive ValidProgram : (initStackSize : Nat) → (p : Program) → Prop -- declares the inductive type or proposition `ValidProgram`
  /-- The empty program is valid with any initial stack -/
  | nil : ValidProgram n [] -- declares another constructor or syntax alternative
  /-- If the first instruction is a push and the rest of the program is valid  with initial stack size `s + 1` then the program is valid with initial stack size `s` -/
  | push  {p : Program} : -- declares another constructor or syntax alternative
      ValidProgram (n + 1) p →
      ValidProgram n (push k :: p)
  /-- If the first instruction is a pop and the rest of the program is valid with initial stack size `s` then the program is valid with initial stack size `s + 1` -/
  | pop  {p : Program} : -- declares another constructor or syntax alternative
      ValidProgram n p →
      ValidProgram (n + 1) (pop :: p)
  /-- If the first instruction is an add and the rest of the program is valid with initial stack size `s + 2` then the program is valid with initial stack size `s + 1` -/
  | add {p : Program} : -- declares another constructor or syntax alternative
      ValidProgram (n + 1) p →
      ValidProgram (n + 2) (add :: p)

/-- The empty program is always valid. -/
@[simp, grind .] -- annotation controlling elaboration, simplification, or automation
theorem valid_program_nil : ValidProgram n [] := ValidProgram.nil -- states and proves theorem `valid_program_nil`

/-- Pushing a value to a stack of size `n` results in a valid program if the rest is valid for `n+1`. -/
@[simp, grind .] -- annotation controlling elaboration, simplification, or automation
theorem valid_program_push (n: Nat) (h : ValidProgram (n + 1) p') : -- states and proves theorem `valid_program_push`
    ValidProgram n (push k :: p') :=    ValidProgram.push h -- applies `ValidProgram.push`, reducing the goal to the supplied tail-validity proof `h`

/-- Adding values on a stack of size `k+2` is valid if the rest is valid for `k+1`. -/
@[simp, grind .] -- annotation controlling elaboration, simplification, or automation
theorem valid_program_add (k: Nat) (h : ValidProgram (k + 1) p') : -- states and proves theorem `valid_program_add`
  ValidProgram (k + 2) (add :: p') := -- states the goal that an `add` program is valid from a stack with two extra entries
  ValidProgram.add h -- applies `ValidProgram.add`, reducing the goal to the supplied tail-validity proof `h`

/-- Popping from a stack of size `n+1` is valid if the rest is valid for `n`. -/
@[simp] -- annotation controlling elaboration, simplification, or automation
theorem valid_program_pop (h : ValidProgram n p') : -- states and proves theorem `valid_program_pop`
  ValidProgram (n + 1) (pop :: p') := -- states the goal that a `pop` program is valid from a nonempty stack
  ValidProgram.pop h -- applies `ValidProgram.pop`, reducing the goal to the supplied tail-validity proof `h`

example (a b: Nat) : ValidProgram n [push a, push b, add] := by -- starts tactic mode; the goal is validity of a two-push-and-add program from any stack size
  grind -- repeatedly applies the validity constructors until the remaining goal is the empty program

example (a b c : Nat) : ValidProgram 0 [push a, push b, add, push c, add] := by -- starts tactic mode; the goal is validity of a concrete stack program from an empty stack
  grind (ematch := 7) -- gives `grind` a larger search budget so it can chain the validity constructors

/-- If a program starting with `push` is valid, then the rest of the program is valid for a larger stack. -/
@[simp] -- annotation controlling elaboration, simplification, or automation
theorem valid_program_of_push {k: Nat} (h : ValidProgram k (push a :: p')) : ValidProgram (k + 1) p' := by -- starts tactic mode; the goal extracts tail validity from validity of a push program
  cases h -- inverts the `ValidProgram` proof; only the `push` constructor can match this program shape
  assumption -- uses the tail-validity hypothesis exposed by constructor inversion

/-- An `add` instruction is never valid on an empty stack. -/
@[simp] -- annotation controlling elaboration, simplification, or automation
theorem invalid_program_add_zero: ¬ ValidProgram 0 (add :: p')  := by -- starts tactic mode; the goal is to derive contradiction from validity of `add` at stack size zero
  intro h -- turns the negated goal into a hypothesis `h : ValidProgram 0 (add :: p')`
  cases h -- no `ValidProgram.add` constructor can produce stack size `0`, so all cases are impossible

/-- An `add` instruction is never valid on a stack with only one element. -/
@[simp] -- annotation controlling elaboration, simplification, or automation
theorem invalid_program_add_one: ¬ ValidProgram 1 (add :: p')  := by -- starts tactic mode; the goal is to rule out `add` with only one stack entry
  grind -- inverts possible validity constructors and solves the resulting impossible arithmetic constraint
  -- intro h
  -- cases h

/-- If a program starting with `add` is valid, then the rest is valid for a smaller stack. -/
@[simp] -- annotation controlling elaboration, simplification, or automation
theorem valid_program_of_add {k: Nat} (h : ValidProgram (k + 2) (add :: p')) : ValidProgram (k + 1) p' := by -- starts tactic mode; the goal extracts tail validity after an `add`
  grind -- inverts the `add` validity constructor and returns the proof for the remaining program

/-- A `pop` instruction is never valid on an empty stack. -/
@[simp] -- annotation controlling elaboration, simplification, or automation
theorem invalid_program_pop_zero: ¬ ValidProgram 0 (pop :: p')  := by -- starts tactic mode; the goal is to rule out `pop` on an empty stack
  grind -- inverts possible validity constructors and solves the impossible stack-size constraint

/-- If a program starting with `pop` is valid, then the rest is valid for a smaller stack. -/
@[simp] -- annotation controlling elaboration, simplification, or automation
theorem valid_program_of_pop {k: Nat} (h : ValidProgram (k +1) (pop :: p')) : ValidProgram k p' := by -- starts tactic mode; the goal extracts tail validity after a `pop`
  grind -- inverts the `pop` validity constructor and returns the proof for the remaining program

/--
Evaluates a program that is guaranteed to be valid for the initial stack size.
This function is total and does not need to return `Option`.
-/
def evaluate (p: Program) (initStack: Stack) (h: ValidProgram initStack.length p) : Stack := -- defines `evaluate`
  match p with -- splits computation into cases by pattern matching
  | [] => initStack -- matches the empty list and returns `initStack`
  | push n :: p' => -- matches a program beginning with `push n` and evaluates the rest with `n` pushed on the stack
      evaluate p' (n :: initStack) (valid_program_of_push h)
  | add :: p' => -- matches a program beginning with `add` and checks the initial stack shape before adding the top two entries
      match initStack with -- splits computation into cases by pattern matching
      | x :: y :: zs => -- matches a stack with at least two entries and evaluates the rest with `x + y` pushed above `zs`
        evaluate p' ((x + y) :: zs) (valid_program_of_add h)
      | [x] => by -- matches a one-entry stack; validity makes this `add` case impossible
        simp at h -- simplifies the current goal or hypotheses
  | pop :: p' => -- matches a program beginning with `pop` and checks the initial stack shape before removing its top
      match initStack with -- splits computation into cases by pattern matching
      | [] => by -- matches an empty stack; validity makes this `pop` case impossible
        simp at h -- simplifies the current goal or hypotheses
      | x :: ys => evaluate p' ys (valid_program_of_pop h) -- matches a nonempty stack and evaluates the rest after removing `x`

#eval evaluate [push 2, push 3, add] [] (by grind) -- runs this expression as a tutorial check

#eval evaluate [push 2, add] [3] (by grind) -- runs this expression as a tutorial check

/--
error: `grind` failed
case grind
h : ¬ValidProgram [].length [push 2, add]
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬ValidProgram [].length [push 2, add]
    [prop] [].length = 0
    [prop] ValidProgram ([].length + 1) [add] → ValidProgram [].length [push 2, add]
  [eqc] True propositions
    [prop] [].length = 0
    [prop] ValidProgram ([].length + 1) [add] → ValidProgram [].length [push 2, add]
  [eqc] False propositions
    [prop] ValidProgram [].length [push 2, add]
    [prop] ValidProgram ([].length + 1) [add]
  [eqc] Equivalence classes
    [eqc] {[].length, 0}
    [eqc] others
      [eqc] {↑[].length, ↑0}
  [ematch] E-matching patterns
    [thm] List.eq_nil_of_length_eq_zero: [@List.length #2 #1]
    [thm] List.length_nil: [@List.length #0 (@List.nil _)]
    [thm] List.length_cons: [@List.length #2 (@List.cons _ #1 #0)]
    [thm] valid_program_nil: [ValidProgram #0 `[[]]]
    [thm] valid_program_push: [ValidProgram #1 (@List.cons `[Instr] (push #2) #3)]
    [thm] valid_program_add: [ValidProgram (#1 + 2) (@List.cons `[Instr] `[add] #2)]
  [cutsat] Assignment satisfying linear constraints
    [assign] [].length := 0
  [ring] Rings
    [ring] Ring `Lean.Grind.Ring.OfSemiring.Q Nat`
      [basis] Basis
        [_] ↑[].length = 0
    [ring] Ring `Int`
      [basis] Basis
        [_] ↑[].length = 0
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] List.eq_nil_of_length_eq_zero ↦ 1
    [thm] List.length_nil ↦ 1
    [thm] valid_program_push ↦ 1
-/
#guard_msgs in -- checks that the following command produces the expected message
#eval evaluate [push 2, add] [] (by grind) -- runs this expression as a tutorial check

macro "evaluate%" p:term  : term => -- declares a custom macro form
  `(evaluate $p [] (by grind))

#eval evaluate% [push 2, push 3, add] -- runs this expression as a tutorial check

/--
A program is valid for a given stack size if and only if its safe evaluation
on a stack of that size succeeds (returns `some`).
-/
theorem valid_iff_eval?_some (p: Program) (s: Stack) : ValidProgram s.length p ↔ (eval? p s) ≠ none := by -- starts tactic mode; the goal is an iff between static validity and safe evaluation success
  constructor -- splits the iff into forward and backward implication goals
  · intro h -- in the forward direction, assumes validity and changes the goal to `eval? p s ≠ none`
    match p with -- splits computation into cases by pattern matching
    | [] => grind [eval?] -- matches the empty list and asks `grind` to solve this case
    | push n :: p' => -- matches a program beginning with `push n` and proves success for the rest with the larger stack
        have h' : ValidProgram (s.length + 1) p' := valid_program_of_push h -- extracts validity of the remaining program after the push
        have ih := (valid_iff_eval?_some p' (n ::s)) -- gets the equivalence for the rest of the program on the pushed stack
        grind [eval?] -- unfolds safe evaluation for `push` and uses `ih` to prove the result is not `none`
    | add :: p' => -- matches a program beginning with `add` and proves success after checking the stack has two entries
        match s with -- splits computation into cases by pattern matching
        | x :: y :: zs => -- matches a stack with at least two entries and proves success for the summed stack
           have h' := valid_program_of_add h -- extracts validity of the remaining program after adding the top two stack entries
           have ih := (valid_iff_eval?_some p' ((x + y) :: zs)) -- gets the equivalence for the rest of the program on the summed stack
           grind [eval?] -- unfolds the successful `add` case and uses `ih` to prove evaluation does not fail
    | pop :: p' => -- matches a program beginning with `pop` and proves success after checking the stack is nonempty
        match s with -- splits computation into cases by pattern matching
        | x :: ys => -- matches a nonempty stack and proves success for the tail stack
            have h' : ValidProgram ys.length p' := valid_program_of_pop h -- extracts validity of the remaining program after popping the stack
            have ih := (valid_iff_eval?_some p' ys) -- gets the equivalence for the rest of the program on the tail stack
            grind [eval?] -- unfolds the successful `pop` case and uses `ih` to prove evaluation does not fail
  · intro h -- in the backward direction, assumes safe evaluation succeeds and changes the goal to `ValidProgram s.length p`
    match p with -- splits computation into cases by pattern matching
    | [] => grind [eval?] -- matches the empty list and asks `grind` to solve this case
    | push n :: p' => -- matches a program beginning with `push n` and derives validity of the rest from safe evaluation
        have ih := (valid_iff_eval?_some p' (n ::s)) -- gets the equivalence for the remaining program after pushing `n`
        grind [eval?] -- unfolds the `push` evaluator case and uses `ih` to build `ValidProgram.push`
    | add :: p' => -- matches a program beginning with `add` and derives validity after checking the stack has two entries
        match s with -- splits computation into cases by pattern matching
        | x :: y :: zs => -- matches a stack with at least two entries and derives validity for the summed stack
           have ih := (valid_iff_eval?_some p' ((x + y) :: zs)) -- gets the equivalence for the remaining program after summing the stack top
           grind [eval?] -- unfolds the successful `add` evaluator case and builds the matching validity proof
    | pop :: p' => -- matches a program beginning with `pop` and derives validity after checking the stack is nonempty
        match s with -- splits computation into cases by pattern matching
        | x :: ys => -- matches a nonempty stack and derives validity for the tail stack
            have ih := (valid_iff_eval?_some p' ys) -- gets the equivalence for the remaining program after popping the stack
            simp -- simplifies the validity goal to the constructor form for a `pop`
            apply valid_program_pop -- reduces the goal to validity of the remaining program on the tail stack
            simp [eval?] at h -- unfolds safe evaluation in the hypothesis, leaving success of the tail program
            grind -- uses `ih` and the simplified hypothesis to finish the tail-validity goal

end stack_machine -- closes the current namespace or section

end langur -- closes the current namespace or section
/-!
## Next files

* None in the README dependency diagram.
-/
