import Lean -- imports definitions and theorems used below
import Std -- imports definitions and theorems used below

/-!
## Prerequisite files

* `PyFor.lean` - syntax extensions and Python-style list comprehensions.

## Main concepts introduced

* domain-specific language syntax.
* shallow embeddings.
* imperative programs.
-/

namespace langur -- starts a namespace to group the tutorial definitions

open Lean Meta Elab Term -- opens names so constructors or helpers can be written unqualified

/-!
# LangurLang: A tiny imperative language

Inspired by the IMP language in Software Foundations. We have only natural number variables, and the following statements:
* Assignment: `x := expr`
* Conditional: `if (cond) { ... } else { ... }`
* While loops: `while (cond) { ... }`
* Print statements: `print expr`

We use a *shallow embedding*, so natural numbers are represented using Lean's `Nat` type and Booleans using Lean's `Bool` type.

We skip at first extracting natural numbers from expressions, and directly evaluate expressions to `Nat`, `Bool` or `String` in a context of variable bindings.
-/
def exprRelVars (vars: List (Name × Nat)) (stx: Syntax.Term) : MetaM Syntax.Term := -- defines `exprRelVars`
  match vars with -- splits computation into cases by pattern matching
  | [] => return stx -- matches the empty list and returns stx
  | (n, val) :: tail => do -- matches a nonempty variable assignment list and returns syntax with that variable substituted into the expression
    let nId := mkIdent n -- binds an intermediate value for the following expression
    let nat := mkIdent ``Nat -- binds an intermediate value for the following expression
    let inner ← -- binds an intermediate value for the following expression
      exprRelVars tail stx
    let arg := Syntax.mkNumLit <| toString val -- binds an intermediate value for the following expression
    `((fun ($nId : $nat) => $inner) $arg) -- maps this case or syntax pattern to its result


def getNatRelVarsM (vars: List (Name × Nat)) -- defines `getNatRelVarsM`
  (t: Syntax.Term) : TermElabM Nat := do
  let stx ← exprRelVars vars t -- binds an intermediate value for the following expression
  let e ← withoutErrToSorry do -- binds an intermediate value for the following expression
    elabTermEnsuringType stx (mkConst ``Nat)
  Term.synthesizeSyntheticMVarsNoPostponing
  unsafe evalExpr Nat (mkConst ``Nat) e

def getBoolRelVarsM (vars: List (Name × Nat)) -- defines `getBoolRelVarsM`
  (t: Syntax.Term) : TermElabM Bool := do
  let stx ← exprRelVars vars t -- binds an intermediate value for the following expression
  let e ← elabTermEnsuringType stx (mkConst ``Bool) -- binds an intermediate value for the following expression
  Term.synthesizeSyntheticMVarsNoPostponing
  unsafe evalExpr Bool (mkConst ``Bool) e

def getStrRelVarsM (vars: List (Name × Nat)) -- defines `getStrRelVarsM`
  (t: Syntax.Term) : TermElabM String := do
  let stx ← exprRelVars vars t -- binds an intermediate value for the following expression
  let e ← withoutErrToSorry do -- binds an intermediate value for the following expression
    elabTermEnsuringType stx (mkConst ``String)
  Term.synthesizeSyntheticMVarsNoPostponing
  unsafe evalExpr String (mkConst ``String) e

namespace LangurLang -- starts a namespace to group the tutorial definitions

-- variables with name
abbrev State := Std.HashMap Name Nat -- introduces `State` as a reducible abbreviation

abbrev LangurLangM := -- introduces `LangurLangM` as a reducible abbreviation
  StateT State TermElabM

def getVar (name: Name) : LangurLangM Nat := do -- defines `getVar`
  let m ← get -- binds an intermediate value for the following expression
  return m.get! name -- returns this value from the monadic block

def setVar (name : Name) (value : Nat) : -- defines `setVar`
  LangurLangM Unit := do
  modify (fun m => m.insert name value) -- maps this case or syntax pattern to its result

def getNatInCtxM (stx: Syntax.Term) : LangurLangM Nat := do -- defines `getNatInCtxM`
  let m ← get -- binds an intermediate value for the following expression
  getNatRelVarsM m.toList stx

def getBoolInCtxM (stx: Syntax.Term) : LangurLangM Bool := do -- defines `getBoolInCtxM`
  let m ← get -- binds an intermediate value for the following expression
  getBoolRelVarsM m.toList stx

def getStrInCtxM (stx: Syntax.Term) : LangurLangM String := do -- defines `getStrInCtxM`
  let m ← get -- binds an intermediate value for the following expression
  getStrRelVarsM m.toList stx

declare_syntax_cat langur_statement

syntax langur_block := "{" sepBy(langur_statement, ";", ";", allowTrailingSep) "}" -- declares new parser syntax

syntax langur_program := sepBy(langur_statement, ";", ";", allowTrailingSep) -- declares new parser syntax

syntax langur_block : langur_statement -- declares new parser syntax

syntax ident ":=" term : langur_statement -- declares new parser syntax

syntax "if" ppSpace "(" term ")" ppSpace langur_block "else" langur_block : langur_statement -- declares new parser syntax

syntax "while" "(" term ")" ppSpace langur_block : langur_statement -- declares new parser syntax

syntax "print" term  : langur_statement -- declares new parser syntax

partial def interpretM : -- defines the partial function `interpretM`
  TSyntax `langur_statement → LangurLangM Unit
| `(langur_statement| {$s;*}) => do -- matches a braced statement block and interprets each statement in order
    let stmts := s.getElems -- binds an intermediate value for the following expression
    for stmt in stmts do -- iterates through these values in the monadic block
      interpretM stmt
| `(langur_statement| $name:ident := $val) => do -- matches an assignment statement and stores the evaluated natural number in that variable
  let value ← getNatInCtxM val -- binds an intermediate value for the following expression
  let n := name.getId -- binds an intermediate value for the following expression
  setVar n value
| `(langur_statement| if ($p) $t else $e) => do -- matches an if-else statement and runs the branch selected by the evaluated condition
  let c ← getBoolInCtxM p -- binds an intermediate value for the following expression
  if c -- branches on this decidable condition
    then runBlockM t
    else runBlockM e -- handles the alternative branch
| `(langur_statement| while ($p) $b) => do -- matches a while loop and repeats the body while the evaluated condition is true
  let rec loop : LangurLangM Unit := do -- binds an intermediate value for the following expression
    let c ← getBoolInCtxM p -- binds an intermediate value for the following expression
    if c then -- branches on this decidable condition
      runBlockM b
      loop
  loop
| stat@`(langur_statement| print $s) => do -- matches a print statement and logs the evaluated string at the statement location
  let str ← getStrInCtxM s -- binds an intermediate value for the following expression
  logInfoAt stat str
| _ => throwUnsupportedSyntax -- matches any remaining form and reports unsupported syntax
where runBlockM (bs : TSyntax ``langur_block): LangurLangM Unit := -- begins the local implementation block for this declaration
  match bs with -- splits computation into cases by pattern matching
  | `(langur_block| {$s;*}) => -- matches a braced block and interprets each statement in order
    let stmts := s.getElems -- binds an intermediate value for the following expression
    for stmt in stmts do -- iterates through these values in the monadic block
      interpretM stmt
  | _ => throwUnsupportedSyntax -- matches any remaining form and reports unsupported syntax

def interpretProgramM (pgm: TSyntax ``langur_program) : LangurLangM Unit := do -- defines `interpretProgramM`
  match pgm with -- splits computation into cases by pattern matching
  | `(langur_program| $s;*) => -- matches a sequence of program statements and interprets them in order
    let stmts := s.getElems -- binds an intermediate value for the following expression
    for stmt in stmts do -- iterates through these values in the monadic block
      interpretM stmt
  | _ => throwUnsupportedSyntax -- matches any remaining form and reports unsupported syntax

def climbProgramM -- defines `climbProgramM`
  (pgm: TSyntax ``langur_program) (init: State) : TermElabM (State) := do
  let (_, m) ← interpretProgramM pgm |>.run init -- binds an intermediate value for the following expression
  return m -- returns this value from the monadic block

elab "#leap" ss:langur_program r:"return" : command  => -- declares an elaborator for custom syntax
  Command.liftTermElabM do
  let (_, m) ← interpretProgramM ss |>.run {} -- binds an intermediate value for the following expression
  logInfoAt r m!"Final variable state: {m.toList}"

elab "climb%" ss:langur_program -- declares an elaborator for custom syntax
    "return" v:term : term  => do -- maps this case or syntax pattern to its result
    let (_, m) ← interpretProgramM ss |>.run {} -- binds an intermediate value for the following expression
    let t ← exprRelVars m.toList v -- binds an intermediate value for the following expression
    elabTerm t none

macro "climb%" ss:langur_program "from%" init:langur_program -- declares a custom macro form
    "return" v:term : term  => do -- maps this case or syntax pattern to its result
    match init, ss with -- splits computation into cases by pattern matching
    | `(langur_program| $s;*), `(langur_program| $t;*) => do -- matches the initialization and main program fragments and returns a combined `climb%` term
      let lines := s.getElems ++ t.getElems -- binds an intermediate value for the following expression
      let prog ← `(langur_program| $lines;*) -- binds an intermediate value for the following expression
      `(climb% $prog return $v)
    | _, _ => Macro.throwError "Invalid syntax in climb% from% ... return ..." -- matches any remaining form and raises an error

end LangurLang -- closes the current namespace or section

end langur -- closes the current namespace or section
/-!
## Next files

* `LangurLeaps.lean` - examples using `LangurLang`; custom commands.
-/
