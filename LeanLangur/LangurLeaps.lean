import LeanLangur.LangurLang

open LangurLang

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


def primality  :=
  climb%
    n := 57;
    i := 2;
    is_prime := 1;
    while (i < n && is_prime = 1) {
    if (i ∣ n) {
      is_prime := 0
    } else {};
    i := i + 1
    };
    return s!"Primality of {n}: {is_prime == 1}"

#eval primality

#eval climb%
    i := 2;
    is_prime := 1;
    while (i < n && is_prime = 1) {
    if (i ∣ n) {
      is_prime := 0
    } else {};
    i := i + 1
    }
    from%
    n := 59;
    return s!"Primality of {n}: {is_prime == 1}"

/-!
## Exercise

Implement a `for` loop construct in LangurLang following `C` syntax:
```c
for (init; cond; step) { body }
```
-/
