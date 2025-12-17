import Mathlib

/-!
## Exercise: Labelled Binary Search Tree

In this exercise, we define a labelled binary search tree (BST) and use it to implement efficient membership checking with proofs of correctness.

### Given Code

* We define a labelled binary tree where each node and leaf has a label of type `α`.
* We define a membership predicate for the tree.
* We define a predicate `IsOrdered` that captures the BST property.
* We implement an efficient membership check function `fastCheckMem` that uses the BST property.
* We define an `addLabel` function to insert labels while maintaining the BST property.

### Exercises

Our ultimate goal is to prove the correctness of `fastCheckMem` when a tree is built using `addLabel`. For this, the results we need to prove are:

* Prove that `addLabel` maintains the `IsOrdered` property.
* Prove that `fastCheckMem` correctly decides membership for ordered trees.
* Define a BST associated with a list of labels.
* Show that `fastCheckMem` works correctly for this BST.

These main goals are stated with `sorry` as placeholders. It will be helpful to prove some intermediate lemmas along the way (and label with `grind`).

* Characterize membership in leaves and nodes.
* Prove that the left subtree of an ordered tree contains only labels less than or equal to the root label.
* Prove that the right subtree of an ordered tree contains only labels greater than or equal to the root label.
* Prove that the left and right subtrees of an ordered tree are themselves ordered.
* Characterize membership after adding a label.
* Define the pivot (root label) of an ordered tree and prove it is a member of the tree.

-/
variable {α : Type}[LinearOrder α]

inductive LabelledTree (α : Type) where
  | leaf : α → LabelledTree α
  | node : α → LabelledTree α → LabelledTree α → LabelledTree α
deriving Repr, Inhabited

open LabelledTree

@[grind .]
def LabelledTree.addLabel (t: LabelledTree α) (label: α) : LabelledTree α :=
  match t with
  | leaf x =>
    if label = x then leaf x
    else if label < x then
      node label (leaf label) (leaf x)
    else
      node label (leaf x) (leaf label)
  | node v l r =>
    if label ≤ v then
      node v (LabelledTree.addLabel l label) r
    else
      node v l (LabelledTree.addLabel r label)


@[grind ., simp]
def LabelledTree.mem {α : Type} : LabelledTree α → α → Prop
  | leaf x, y => x = y
  | node _ l r, y => LabelledTree.mem l y ∨ LabelledTree.mem r y

@[grind .]
instance {α : Type} : Membership α (LabelledTree α) where
  mem := LabelledTree.mem


@[grind ., simp]
def IsOrdered : LabelledTree α → Prop
  | leaf _ => True
  | node v l r =>
    (∀ x ∈ l, x ≤ v) ∧ (∀ x ∈ r, v ≤ x) ∧ IsOrdered l ∧ IsOrdered r ∧ (v ∈ l ∨ v ∈ r)

@[grind .]
def fastCheckMem (label : α)(l: LabelledTree α) : Bool := match l with
  | leaf l => l == label
  | node l left right =>
    if l == label then true
    else if label < l then fastCheckMem label left
    else fastCheckMem label right


-- The above are definitions. Below are theorems about them.

@[grind ., simp]
theorem mem_leaf {α : Type} (x y : α) :
    y ∈ leaf x ↔ x = y := by
    simp [Membership.mem]

@[grind ., simp]
theorem mem_node {α : Type} (x: α) (l r : LabelledTree α) (y : α) :
    y ∈ node x l r ↔ y ∈ l ∨ y ∈ r := by
    simp [LabelledTree.mem, Membership.mem]


@[grind .]
theorem IsOrdered_leaf (x: α) :
  IsOrdered (leaf x) := by
  simp [IsOrdered]

@[grind .]
theorem IsOrdered_left_below (v: α) (l r: LabelledTree α) (h: IsOrdered (node v l r)) :
  ∀ x ∈ l, x ≤ v := by
  grind

@[grind .]
theorem IsOrdered_right_above (v: α) (l r: LabelledTree α) (h: IsOrdered (node v l r)) :
  ∀ x ∈ r, v ≤ x := by grind

@[grind .]
theorem IsOrdered_left_subtree (v: α) (l r: LabelledTree α) (h: IsOrdered (node v l r)) :
  IsOrdered l := by
  grind

@[grind .]
theorem IsOrdered_right_subtree (v: α) (l r: LabelledTree α) (h: IsOrdered (node v l r)) :
  IsOrdered r := by
  grind


@[grind .]
theorem mem_addLabel (t: LabelledTree α) (label: α) (x : α) :
    x ∈ LabelledTree.addLabel t label ↔ x = label ∨ x ∈ t := by
  induction t with
  | leaf v =>
    by_cases h: label ≤ v <;> grind
  | node v l r ihl ihr =>
    by_cases h: label ≤ v <;> grind


theorem ordered_addLabel (t: LabelledTree α) (label: α)
  (h: IsOrdered t) :
    IsOrdered (LabelledTree.addLabel t label) := by
  induction t with
  | leaf x =>
    by_cases h1: label ≤ x <;> grind
  | node v l r ihl ihr =>
    by_cases h1: label ≤ v <;> grind

def pivot : LabelledTree α → α
| node l .. => l
| leaf l => l

@[grind .]
theorem pivot_member (l: LabelledTree α) (h₀ : IsOrdered l) :
  pivot l ∈ l := by
  induction l with
  | leaf l => grind [pivot]
  | node label left right ihl ihr =>
    grind [pivot]


theorem fastCheckMem_correct (label : α)(l: LabelledTree α)(h : IsOrdered l):
  fastCheckMem label l = true ↔ label ∈ l := by
  induction l with
  | leaf label' =>
    grind
  | node label' left right ihl ihr =>
    grind
