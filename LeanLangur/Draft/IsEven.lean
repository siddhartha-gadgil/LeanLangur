import Mathlib

inductive IsEven : Nat → Prop
  | zero : IsEven 0
  | addTwo (h : IsEven n) : IsEven (n + 2)

theorem IsEven_two_mul (n : Nat) : IsEven (2 * n) := by
  induction n with
  | zero => simp [IsEven.zero]
  | succ n ih =>
    apply IsEven.addTwo ih

theorem succ_odd_of_isEven {n : Nat}
  (h : IsEven n) :
    ¬ IsEven (n + 1) := by
  induction h with
  | zero =>
    intro h'
    cases h'
  | addTwo h ih =>
    intro h'
    cases h' with
    | addTwo h'' =>
      contradiction
