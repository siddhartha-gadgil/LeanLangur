import Mathlib

variable {α : Type}[LinearOrder α]

inductive LabelledTree (α : Type) where
  | leaf : α → LabelledTree α
  | node : α → LabelledTree α → LabelledTree α → LabelledTree α
deriving Repr, Inhabited

open LabelledTree

@[grind ., simp]
def LabelledTree.mem {α : Type} : LabelledTree α → α → Prop
  | leaf x, y => x = y
  | node _ l r, y => LabelledTree.mem l y ∨ LabelledTree.mem r y

@[grind .]
instance {α : Type} : Membership α (LabelledTree α) where
  mem := LabelledTree.mem

@[grind ., simp]
theorem mem_leaf {α : Type} (x y : α) :
    y ∈ leaf x ↔ x = y := by
    simp [Membership.mem]

@[grind ., simp]
theorem mem_node {α : Type} (x: α) (l r : LabelledTree α) (y : α) :
    y ∈ node x l r ↔ y ∈ l ∨ y ∈ r := by
    simp [LabelledTree.mem, Membership.mem]


@[grind ., simp]
def isOrdered : LabelledTree α → Prop
  | leaf _ => True
  | node v l r =>
    (∀ x ∈ l, x ≤ v) ∧ (∀ x ∈ r, v ≤ x) ∧ isOrdered l ∧ isOrdered r

@[grind .]
theorem isOrdered_leaf (x: α) :
  isOrdered (leaf x) := by
  simp [isOrdered]

@[grind .]
theorem isOrdered_left_below (v: α) (l r: LabelledTree α) (h: isOrdered (node v l r)) :
  ∀ x ∈ l, x ≤ v := by
  simp [isOrdered, Membership.mem] at h
  rcases h with ⟨h₁, h₂, h₃, h₄⟩
  exact h₁

@[grind .]
theorem isOrdered_right_above (v: α) (l r: LabelledTree α) (h: isOrdered (node v l r)) :
  ∀ x ∈ r, v ≤ x := by
  simp  at h
  rcases h with ⟨h₁, h₂, h₃, h₄⟩
  exact h₂

@[grind .]
theorem isOrdered_left_subtree (v: α) (l r: LabelledTree α) (h: isOrdered (node v l r)) :
  isOrdered l := by
  grind

@[grind .]
theorem isOrdered_right_subtree (v: α) (l r: LabelledTree α) (h: isOrdered (node v l r)) :
  isOrdered r := by
  grind

@[grind .]
def LabelledTree.addLabel (t: LabelledTree α) (label: α) : LabelledTree α :=
  match t with
  | leaf x =>
    if label ≤ x then
      node label (leaf label) (leaf x)
    else
      node label (leaf x) (leaf label)
  | node v l r =>
    if label ≤ v then
      node v (LabelledTree.addLabel l label) r
    else
      node v l (LabelledTree.addLabel r label)

@[grind .]
theorem mem_addLabel (t: LabelledTree α) (label: α) (x : α) :
    x ∈ LabelledTree.addLabel t label ↔ x = label ∨ x ∈ t := by
  induction t with
  | leaf v =>
    by_cases h: label ≤ v
    · grind
    · grind
  | node v l r ihl ihr =>
    simp [LabelledTree.addLabel]
    by_cases h: label ≤ v
    · simp [h]
      grind
    · simp [h]
      grind


theorem ordered_addLabel (t: LabelledTree α) (label: α)
  (h: isOrdered t) :
    isOrdered (LabelledTree.addLabel t label) := by
  induction t with
  | leaf x =>
    if h1: label ≤ x then
      grind
    else
      grind
  | node v l r ihl ihr =>
    if h1: label ≤ v then
      simp [LabelledTree.addLabel, h1]
      grind
    else
      simp [LabelledTree.addLabel, h1]
      grind

-- Copied and adapted from BinTree.lean, not needed

@[grind .]
def LabelledTree.toList {α : Type} : LabelledTree α → List α
  | leaf x => [x]
  | node _ l r =>
    LabelledTree.toList l ++ LabelledTree.toList r

def exampleTree : LabelledTree Nat :=
  node 0 (node 0 (leaf 1) (leaf 2)) (leaf 3)

#eval exampleTree.toList  -- Output: [1, 2, 3]


theorem mem_iff_mem_toList {α : Type} (t : LabelledTree α) (x : α) :
    x ∈ t ↔ x ∈ LabelledTree.toList t := by
    apply Iff.intro
    · induction t with
    | leaf a => grind
    | node _ l r ihl ihr => grind
    · induction t with
    | leaf a => grind
    | node _ l r ihl ihr => grind
