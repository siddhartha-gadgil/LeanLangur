/-!
# Propositions and Proofs

As we have mentioned, proofs and propositions are terms, with propositions as types. The universe `Prop` is the type of propositions.
To start with, it is best to ignore the difference between `Prop` and `Type` and treat them as the same.

A logical statement like `1 ≤ 2` is a proposition and has type `Prop`.
-/
#check 1 ≤ 2 -- Prop

-- The type `Prop` is itself a term of type `Type`.
#check Prop -- Type
#check Type -- Type 1

#check Nat.le

/-!
Proofs build on other proofs. We will see eventually what are the most basic proofs. For now, we will see some proofs and see how they can be used and combined.
-/
#check Nat.zero_le -- Nat → 0 ≤ n

#check Nat.le.refl -- ∀ {n : Nat}, n.le n

#check Nat.le.step -- ∀ {n m : Nat}, n ≤ m → n ≤ m.succ

/-!
The proposition `0 ≤ 2` is true and has proof `Nat.zero_le 2`.
-/
#check Nat.zero_le 2 -- 0 ≤ 2

/-!
The proposition `1 ≤ 3` is true and has proof `Nat.succ_le_succ (Nat.zero_le 2)`.
-/
#check Nat.succ_le_succ (Nat.zero_le 2) -- 1 ≤ 3

/-!
The notation `· ≤ ·` is for the `Nat.le` relation, which is defined inductively.
-/
#check Nat.le -- Nat → Nat → Prop

/-!
Two basic propotions are `False` and `True`. `False` is the proposition that is never true, and `True` is the proposition that is always true.
-/
#check False -- Prop
#check True -- Prop

/-!
We can combine propositions to make propositions:

* If `P` and `Q` are propositions, then `P ∧ Q` is the proposition "P and Q".
* If `P` and `Q` are propositions, then `P ∨ Q` is the proposition "P or Q".
* If `P` and `Q` are propositions, then `P → Q` is the proposition "if P then Q".
* If `P` is a proposition, then `¬ P` is the proposition "not P", which is `P → False`.

The key idea in *propositions as types* is that function application is exactly analogous to the logical rule of inference called *modus ponens*.
-/
def modus_ponens {P Q: Prop} (h₁ : P) (h₂ : P → Q) : Q :=
  h₂ h₁

/- We define a function `functionApplication` that applies a function to an argument. This is the same as modus ponens, but for arbitrary types rather than propositions.
The arguments are reversed to match the usual order of modus ponens.
-/
def functionApplication {α β : Type} (a: α) (f: α → β) : β :=
  f a

#check Nat.succ -- Nat → Nat
#eval functionApplication 1 Nat.succ -- 2

#check Nat.succ_le_succ -- ∀ {n m : Nat}, n ≤ m → n.succ ≤ m.succ

/-!
We apply modus-ponens with `P` being `0 ≤ 2` and `P → Q` being `Nat.succ_le_succ` applied to `0` and `2`. We need to use `@Nat.succ_le_succ` to specify the *implicit* arguments.
-/
#check @Nat.succ_le_succ 0 2 -- 0 ≤ 2 → 1 ≤ 3

#check modus_ponens (Nat.zero_le 2)
  (@Nat.succ_le_succ 0 2) -- 1 ≤ 3


theorem one_plus_one_eq_two : 1 + 1 = 2 := by
  rfl

/--
error: Tactic `rfl` failed: The left-hand side
  1 + 1
is not definitionally equal to the right-hand side
  3

⊢ 1 + 1 = 3
-/
#guard_msgs in
example : 1 + 1 = 3 := by
  rfl

#print one_plus_one_eq_two -- prints Lean's generated declaration for inspection

#check Eq.refl -- ∀ {α : Sort u_1} {a : α}, a = a

example : 1 ≤ 4 := by
  -- apply Nat.le_refl
  apply Nat.le.step
  apply Nat.le.step
  apply Nat.le.step
  apply Nat.le.refl

theorem one_le_four : 1 ≤ 4 := by
  -- apply Nat.le_refl
  repeat (first | apply Nat.le_refl | apply Nat.le.step)

#print one_le_four -- prints Lean's generated declaration for inspection

example : Nat → Nat :=
  fun n ↦ n + 1

macro "nat_le" : tactic =>
  `(tactic| repeat (first | apply Nat.le_refl | apply Nat.le.step))

theorem twelve_le_eighteen : 12 ≤ 18 :=
  by
  nat_le

#print twelve_le_eighteen -- prints Lean's generated declaration for inspection

/-!
Some proofs at *term level*.
-/
theorem one_le_three : 1 ≤ 3 :=
  Nat.le.step (Nat.le.step (Nat.le.refl ))
/-!
A type family of propositions `ZeroLe` is defined, with a proof `pf_zero_le` that `0 ≤ n` for any natural number `n`.
-/
def ZeroLe (n: Nat) : Prop := 0 ≤ n

/--
A dependent function `pf_zero_le` that takes a natural number `n` and returns a proof that `0 ≤ n`.
-/
def pf_zero_le (n: Nat) : ZeroLe n := Nat.zero_le n

#check Nat.le.step
#check Nat.le_step

example : 1 ≤ 3 :=
  Nat.le.step (Nat.le.step (@Nat.le.refl _))

theorem two_le_five : 2 ≤ 5 :=
  Nat.le.step (Nat.le.step (Nat.le.step (Nat.le.refl)))

example : 2 ≤ 5 := by
  exact Nat.le.step (Nat.le.step (Nat.le.step (Nat.le.refl)))

#check @Nat.succ_le_succ 0 2 (Nat.zero_le 2) -- 1 ≤ 3

theorem wrong_three_le_one (h : 2 ≤ 0) : 3 ≤ 1 :=
  Nat.succ_le_succ h

theorem n_le_n_plus_two (n : Nat) : n ≤ n + 2 :=
  Nat.le.step (Nat.le.step (Nat.le.refl))

def nat_le_n_plus_m (n m : Nat) : n ≤ n + m :=
  match m with
  | 0   => Nat.le.refl
  | m+1 => Nat.le.step (nat_le_n_plus_m n m)

/-!
## Proof Irrelevance

In Lean, any two proof terms of the same proposition are equal by definition. This is called *proof irrelevance*.
-/
theorem proof_irrelevance {P: Prop} (h₁ h₂: P) :
  h₁ = h₂ := rfl

/-!
## Universes

* Universes in Lean are called `Sort`s, they are `Sort 0`, `Sort 1`, etc.
* `Prop` is `Sort 0`.
* `Type` is `Sort 1`.
* `Type n` is `Sort n.succ`.
* Strictly speaking, the `n` here is a universe level, not a natural number.
-/

example : 1 < 2 := sorry

#check sorryAx
