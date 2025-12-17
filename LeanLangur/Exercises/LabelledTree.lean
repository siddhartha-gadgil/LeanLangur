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


/-! The above are definitions. Below are the main theorems about them. You will need to prove some lemmas along the way.
-/

theorem ordered_addLabel (t: LabelledTree α) (label: α)
  (h: IsOrdered t) :
    IsOrdered (LabelledTree.addLabel t label) := by
  sorry

theorem fastCheckMem_correct (label : α)
    (l: LabelledTree α)(h : IsOrdered l):
    fastCheckMem label l = true ↔ label ∈ l := by
  sorry

def buildBST : List α → LabelledTree α
  | _ => sorry

theorem buildBST_ordered (labels : List α) :
    IsOrdered (buildBST labels) := by
  sorry

theorem buildBST_mem_correct (labels : List α)
    (label : α) :
    fastCheckMem label (buildBST labels) = true ↔ label ∈ labels := by
  sorry
