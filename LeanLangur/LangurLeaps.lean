import LeanLangur.LangurLang -- imports definitions and theorems used below

/-!
## Prerequisite files

* `LangurLang.lean` - domain-specific language syntax, shallow embeddings, and imperative programs.

## Main concepts introduced

* examples using `LangurLang`.
* custom commands.
-/

/-!
# LangurLeaps: LangurLang Examples

This module provides examples of programs written in `LangurLang` using the `#leap` command
and the `climb%` macro. It includes implementations of summation and primality testing.
-/

namespace langur -- starts a namespace to group the tutorial definitions

open LangurLang -- opens names so constructors or helpers can be written unqualified

/-!
A simple `LangurLang` program illustrating assignments and conditionals.
-/
#leap -- runs this LangurLang example through the custom command
  n := 3; m := 4 + 5;
  if (n ≤ 4) {n := (5 + 3 + (2 * 7));} else {n := 2; m := 7} -- branches on this decidable condition
  return

/-!
A program to calculate the sum of the first `n` natural numbers.
-/
#leap -- runs this LangurLang example through the custom command
  n := 10; sum := 0;
  i := 1;
  while (i ≤ n) {sum := sum + i; i := i + 1} return

/--
A simple value for testing primality.
-/
def eg.n := 59 -- defines `eg.n`

/-!
Primality test for `n = 59` in `LangurLang`.
-/
open eg in -- opens names so constructors or helpers can be written unqualified
#leap -- runs this LangurLang example through the custom command
  i := 2;
  is_prime := 1;
  while (i < n && is_prime = 1) {
    if (i ∣ n) { -- branches on this decidable condition
      is_prime := 0
    } else {};
    i := i + 1
  };
  if (is_prime = 1) { -- branches on this decidable condition
    print s!"{n} is prime"
  } else {
    print s!"{n} is not prime; divisor: {i - 1}"
  }
  return


/--
A `climb%` macro usage to check the primality of `n = 57`.
-/
def primality  := -- defines `primality`
  climb%
    n := 57;
    i := 2;
    is_prime := 1;
    while (i < n && is_prime = 1) {
    if (i ∣ n) { -- branches on this decidable condition
      is_prime := 0
    } else {};
    i := i + 1
    };
    return s!"Primality of {n}: {is_prime == 1}" -- returns this value from the monadic block

#eval primality -- runs this expression as a tutorial check

/-!
Another `climb%` example checking the primality of `n = 59`.
-/
#eval climb% -- runs this expression as a tutorial check
    i := 2;
    is_prime := 1;
    while (i < n && is_prime = 1) {
    if (i ∣ n) { -- branches on this decidable condition
      is_prime := 0
    } else {};
    i := i + 1
    }
    from%
    n := 59;
    return s!"Primality of {n}: {is_prime == 1}" -- returns this value from the monadic block

/-!
## Exercise

Implement a `for` loop construct in LangurLang following `C` syntax:
```c
for (init; cond; step) { body }
```
-/

end langur -- closes the current namespace or section
/-!
## Next files

* None in the README dependency diagram.
-/
