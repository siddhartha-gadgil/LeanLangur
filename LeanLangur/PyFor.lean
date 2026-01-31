import Lean
import Mathlib
open Lean Elab Meta Term

/-!
# Python-style for Comprehensions in Lean

In Python, we have:
* `[x * x for x in [1, 2, 3, 4, 5]]`
and more complex comprehensions like:
* `[x * y for l in [[1, 2], [3, 4]] for x in l for y in l]`

In Lean, we can use `do` notation to express similar comprehensions over lists.
-/
def eg₀ : List Nat := do
  let x ← [1, 2, 3, 4]
  return x * x

#eval eg₀
/-!
This is equivalent to:
-/
#eval List.map (fun x => x * x) [1, 2, 3, 4]

/-!
The more complex comprehension can be expressed as:
-/
def eg₁ : List Nat := do
  let l ← [[1, 2], [3, 4]]
  let x ← l
  let y ← l
  return x * y

#eval eg₁

/-!
If we use `List.map` naively, we get:
-/
#eval List.map (fun l =>
  List.map (fun x =>
    List.map (fun y => x * y) l
  ) l
) [[1, 2], [3, 4]]

/-!
This is equivalent to:
-/
def eg : List Nat :=
  List.flatMap (fun l =>
    List.flatMap (fun x =>
      List.map (fun y => x * y) l
    ) l
  ) [[1, 2], [3, 4]]
#eval eg


/-!
We can define a custom syntax for Python-style for comprehensions.
-/

section PyForComprehension

macro "[" t:term "pyfor" x:ident "in" l:term  "]" : term => do
  let fn ← `(fun $x => $t)
  `(List.map $fn $l)

#eval [x * x pyfor x in [1,2,3,4,5]]

#check Expr.isAppOf

elab "[" t:term "py_for" x:ident "in" l:term  "]" : term => do
  let fnStx ← `(fun $x => $t)
  let lExpr ← elabTerm l none
  let fn ← elabTerm fnStx none
  let ltype ← inferType lExpr
  Term.synthesizeSyntheticMVarsNoPostponing
  if ltype.isAppOf ``List then
    mkAppM ``List.map #[fn, lExpr]
  else
    if ltype.isAppOf ``Array then
      mkAppM ``Array.map #[fn, lExpr]
    else
      throwError "Expected a List or Array in py_for comprehension, got {ltype}"


#eval [x + 1 py_for x in [10,20,30]]

#eval [x * 2 py_for x in #[1,2,3,4]]

declare_syntax_cat for_range
syntax "pyFor" ident "in" term : for_range

syntax "[" term for_range* "]" : term

macro_rules
| `([ $y:term pyFor $x:ident in $l ]) => do
    `(List.map (fun $x => $y) $l)
| `([ $y:term  pyFor $x:ident in $l $ls:for_range*]) => do
    let tail ← `([ $y:term $ls:for_range* ])
    `(List.flatMap (fun $x => $tail) $l)

#eval [x * x pyFor x in [1, 2, 3, 4, 5]]
#eval [x * x pyFor l in [[1, 5, 2], [3, 4, 5]] pyFor x in l]

/-!
## Exercise

Using `List.filter` modify the `pyfor` syntax to support `if` conditions in for comprehensions.
-/
end PyForComprehension
