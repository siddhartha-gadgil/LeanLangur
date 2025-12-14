import Lean
import Std

open Lean Meta Elab Term

/-!
# LangurLang: A tiny imperative language

Inspired by the IMP language in Software Foundations.
-/
def exprRelVars (vars: List (Name × Nat)) (stx: Syntax.Term) : MetaM Syntax.Term :=
  match vars with
  | [] => return stx
  | (n, val) :: tail => do
    let nId := mkIdent n
    let nat := mkIdent ``Nat
    let inner ←
      exprRelVars tail stx
    let arg := Syntax.mkNumLit <| toString val
    `((fun ($nId : $nat) => $inner) $arg)


def getNatRelVarsM (vars: List (Name × Nat))
  (t: Syntax.Term) : TermElabM Nat := do
  let stx ← exprRelVars vars t
  let e ← elabTermEnsuringType stx (mkConst ``Nat)
  Term.synthesizeSyntheticMVarsNoPostponing
  unsafe evalExpr Nat (mkConst ``Nat) e


elab "get_nat_rel_n%" t:term : term => do
  let n ← getNatRelVarsM [(`n, 3)] t
  return toExpr n

#eval get_nat_rel_n% (3 * 5 + n)

def getBoolRelVarsM (vars: List (Name × Nat))
  (t: Syntax.Term) : TermElabM Bool := do
  let stx ← exprRelVars vars t
  let e ← elabTermEnsuringType stx (mkConst ``Bool)
  Term.synthesizeSyntheticMVarsNoPostponing
  unsafe evalExpr Bool (mkConst ``Bool) e

def getStrRelVarsM (vars: List (Name × Nat))
  (t: Syntax.Term) : TermElabM String := do
  let stx ← exprRelVars vars t
  let e ← elabTermEnsuringType stx (mkConst ``String)
  Term.synthesizeSyntheticMVarsNoPostponing
  unsafe evalExpr String (mkConst ``String) e

namespace LangurLang

-- variables with name
abbrev State := Std.HashMap Name Nat

abbrev LangurLangM :=
  StateT State TermElabM

def getVar (name: Name) : LangurLangM Nat := do
  let m ← get
  return m.get! name

def setVar (name : Name) (value : Nat) :
  LangurLangM Unit := do
  modify (fun m => m.insert name value)

def getNatInCtxM (stx: Syntax.Term) : LangurLangM Nat := do
  let m ← get
  getNatRelVarsM m.toList stx

def getBoolInCtxM (stx: Syntax.Term) : LangurLangM Bool := do
  let m ← get
  getBoolRelVarsM m.toList stx

def getStrInCtxM (stx: Syntax.Term) : LangurLangM String := do
  let m ← get
  getStrRelVarsM m.toList stx

declare_syntax_cat langur_statement

syntax langur_block := "{" sepBy(langur_statement, ";", ";", allowTrailingSep) "}"

syntax langur_program := sepBy(langur_statement, ";", ";", allowTrailingSep)

syntax langur_block : langur_statement

syntax ident ":=" term : langur_statement

syntax "if" ppSpace "(" term ")" ppSpace langur_block "else" langur_block : langur_statement

syntax "while" "(" term ")" ppSpace langur_block : langur_statement

syntax "print" term  : langur_statement

partial def interpretM :
  TSyntax `langur_statement → LangurLangM Unit
| `(langur_statement| {$s;*}) => do
    let stmts := s.getElems
    for stmt in stmts do
      interpretM stmt
| `(langur_statement| $name:ident := $val) => do
  let value ← getNatInCtxM val
  let n := name.getId
  setVar n value
| `(langur_statement| if ($p) $t else $e) => do
  let c ← getBoolInCtxM p
  if c
    then runBlockM t
    else runBlockM e
| `(langur_statement| while ($p) $b) => do
  let rec loop : LangurLangM Unit := do
    let c ← getBoolInCtxM p
    if c then
      runBlockM b
      loop
  loop
| stat@`(langur_statement| print $s) => do
  let str ← getStrInCtxM s
  logInfoAt stat str
| _ => throwUnsupportedSyntax
where runBlockM (bs : TSyntax ``langur_block): LangurLangM Unit :=
  match bs with
  | `(langur_block| {$s;*}) =>
    let stmts := s.getElems
    for stmt in stmts do
      interpretM stmt
  | _ => throwUnsupportedSyntax

def interpretProgramM (pgm: TSyntax ``langur_program) : LangurLangM Unit := do
  match pgm with
  | `(langur_program| $s;*) =>
    let stmts := s.getElems
    for stmt in stmts do
      interpretM stmt
  | _ => throwUnsupportedSyntax

elab "#leap" ss:langur_program r:"return" : command  =>
  Command.liftTermElabM do
  let (_, m) ← interpretProgramM ss |>.run {}
  logInfoAt r m!"Final variable state: {m.toList}"


#leap
  n := 3; m := 4 + 5;
  if (n ≤ 4) {n := (5 + 3 + (2 * 7));} else {n := 2; m := 7}
  return

#leap
  n := 10; sum := 0;
  i := 1;
  while (i ≤ n) {sum := sum + i; i := i + 1} return

def eg.n := 59

open eg in
#leap
  i := 2;
  is_prime := 1;
  while (i < n && is_prime = 1) {
    if (i ∣ n) {
      is_prime := 0
    } else {};
    i := i + 1
  };
  if (is_prime = 1) {
    print s!"{n} is prime"
  } else {
    print s!"{n} is not prime; divisor: {i - 1}"
  }
  return

end LangurLang
