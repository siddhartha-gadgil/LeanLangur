import Lean -- imports definitions and theorems used below
import Mathlib -- imports definitions and theorems used below

/-!
## Prerequisite files

* `FibM.lean` - memoization and the `State` monad.

## Main concepts introduced

* syntax extensions.
* Python-style list comprehensions.
-/

namespace langur -- starts a namespace to group the tutorial definitions

open Lean Elab Meta Term -- opens names so constructors or helpers can be written unqualified

/-!
# Python-style for Comprehensions in Lean

In Python, we have:
* `[x * x for x in [1, 2, 3, 4, 5]]`
and more complex comprehensions like:
* `[x * y for l in [[1, 2], [3, 4]] for x in l for y in l]`

In Lean, we can use `do` notation to express similar comprehensions over lists.
-/
def eg₀ : List Nat := do -- defines `eg`
  let x ← [1, 2, 3, 4] -- binds an intermediate value for the following expression
  return x * x -- returns this value from the monadic block

#eval eg₀ -- runs this expression as a tutorial check
/-!
This is equivalent to:
-/
#eval List.map (fun x => x * x) [1, 2, 3, 4] -- runs this expression as a tutorial check

/-!
The more complex comprehension can be expressed as:
-/
def eg₁ : List Nat := do -- defines `eg`
  let l ← [[1, 2], [3, 4]] -- binds an intermediate value for the following expression
  let x ← l -- binds an intermediate value for the following expression
  let y ← l -- binds an intermediate value for the following expression
  return x * y -- returns this value from the monadic block

#eval eg₁ -- runs this expression as a tutorial check

/-!
If we use `List.map` naively, we get:
-/
#eval List.map (fun l => -- runs this expression as a tutorial check
  List.map (fun x => -- maps this case or syntax pattern to its result
    List.map (fun y => x * y) l -- maps this case or syntax pattern to its result
  ) l
) [[1, 2], [3, 4]]

/-!
This is equivalent to:
-/
def eg : List Nat := -- defines `eg`
  List.flatMap (fun l => -- maps this case or syntax pattern to its result
    List.flatMap (fun x => -- maps this case or syntax pattern to its result
      List.map (fun y => x * y) l -- maps this case or syntax pattern to its result
    ) l
  ) [[1, 2], [3, 4]]
#eval eg -- runs this expression as a tutorial check

#eval [2, 3, 4].map (fun x => [x * 2, x* x]) -- runs this expression as a tutorial check

#eval [2, 3, 4].flatMap (fun x => [x * 2, x* x]) -- runs this expression as a tutorial check

/-!
We can define a custom syntax for Python-style for comprehensions.
-/

section PyForComprehension

macro "[" t:term "pyfor" x:ident "in" l:term  "]" : term => do -- declares a custom macro form
  let fn ← `(fun $x => $t) -- binds an intermediate value for the following expression
  `(List.map $fn $l)

#eval [x * x pyfor x in [1,2,3,4,5]] -- runs this expression as a tutorial check

#check Expr.isAppOf -- asks Lean to display the inferred type

elab "[" t:term "py_for" x:ident "in" l:term  "]" : term => do -- declares an elaborator for custom syntax
  let fnStx ← `(fun $x => $t) -- binds an intermediate value for the following expression
  let lExpr ← elabTerm l none -- binds an intermediate value for the following expression
  let fn ← elabTerm fnStx none -- binds an intermediate value for the following expression
  let ltype ← inferType lExpr -- binds an intermediate value for the following expression
  Term.synthesizeSyntheticMVarsNoPostponing
  if ltype.isAppOf ``List then -- branches on this decidable condition
    mkAppM ``List.map #[fn, lExpr]
  else -- handles the alternative branch
    if ltype.isAppOf ``Array then -- branches on this decidable condition
      mkAppM ``Array.map #[fn, lExpr]
    else -- handles the alternative branch
      throwError "Expected a List or Array in py_for comprehension, got {ltype}"


#eval [x + 1 py_for x in [10,20,30]] -- runs this expression as a tutorial check

#eval [x * 2 py_for x in #[1,2,3,4]] -- runs this expression as a tutorial check

declare_syntax_cat for_range
syntax "pyFor" ident "in" term : for_range -- declares new parser syntax

syntax "[" term for_range* "]" : term -- declares new parser syntax

macro_rules -- adds a macro expansion rule
| `([ $y:term pyFor $x:ident in $l ]) => do -- matches a one-generator `pyFor` comprehension and returns a `List.map` over that generator
    `(List.map (fun $x => $y) $l) -- maps this case or syntax pattern to its result
| `([ $y:term  pyFor $x:ident in $l $ls:for_range*]) => do -- matches a comprehension with another generator and returns a `flatMap` over the first generator
    let tail ← `([ $y:term $ls:for_range* ]) -- binds an intermediate value for the following expression
    `(List.flatMap (fun $x => $tail) $l) -- maps this case or syntax pattern to its result

#eval [x * x pyFor x in [1, 2, 3, 4, 5]] -- runs this expression as a tutorial check
#eval [x * x pyFor l in [[1, 5, 2], [3, 4, 5]] pyFor x in l] -- runs this expression as a tutorial check

/-!
## Exercise

Using `List.filter` modify the `pyfor` syntax to support `if` conditions in for comprehensions.
-/
end PyForComprehension -- closes the current namespace or section

end langur -- closes the current namespace or section
/-!
## Next files

* `LoadFile.lean` - file I/O; syntax quotations; commands for loading data.
* `LangurLang.lean` - domain-specific language syntax; shallow embeddings; imperative programs.
-/
