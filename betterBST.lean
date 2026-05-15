import Mathlib

/-!
# Binary Search Trees

This module provides a basic implementation of Binary Search Trees (BSTs) in Lean 4.
It includes definitions for the tree structure, membership, order properties,
and basic operations like adding labels and searching.
-/

namespace langur

variable {α : Type}[LinearOrder α]

namespace better_binary_search_tree

/--
A binary search tree structure.
Each node contains a value and two children (left and right).
A leaf contains a single value.
empty is the empty tree.
-/
inductive Better_BinarySearchTree (α : Type) where
  | empty: Better_BinarySearchTree α
  | leaf : α → Better_BinarySearchTree α
  | node : α → Better_BinarySearchTree α → Better_BinarySearchTree α → Better_BinarySearchTree α
deriving Repr, Inhabited, DecidableEq

open Better_BinarySearchTree

/--
Membership relation for Binary Search Trees.
-/
@[grind ., simp]
def Better_BinarySearchTree.mem {α : Type} : Better_BinarySearchTree α → α → Prop
  | empty ,y => False
  | leaf x, y => x = y
  | node _ l r, y => Better_BinarySearchTree.mem l y ∨ Better_BinarySearchTree.mem r y

/--
Instance for using the `∈` notation with `BinarySearchTree`.
-/
@[grind .]
instance {α : Type} : Membership α (Better_BinarySearchTree α) where
  mem := Better_BinarySearchTree.mem

/--
A leaf contains an element `y` if and only if `y` is equal to the element in the leaf.
-/
@[grind ., simp]
theorem mem_leaf {α : Type} (x y : α) :
    y ∈ leaf x ↔ x = y := by
    simp [Membership.mem]

/--
A node contains an element `y` if and only if `y` is in the left or right subtree.
-/
@[grind ., simp]
theorem mem_node {α : Type} (x: α) (l r : Better_BinarySearchTree α) (y : α) :
    y ∈ node x l r ↔ y ∈ l ∨ y ∈ r := by
    simp [Better_BinarySearchTree.mem, Membership.mem]

/--
Predicate for checking if a binary tree satisfies the Binary Search Tree property:
for any node with value `v`, all elements in the left subtree are `≤ v` and
all elements in the right subtree are `≥ v`.
Also requires the value `v` to be present in one of the subtrees (for nodes).
-/
@[grind ., simp]
def IsOrdered : Better_BinarySearchTree α → Prop
  | empty => True
  | leaf _ => True
  | node v l r =>
    (∀ x ∈ l, x ≤ v) ∧ (∀ x ∈ r, v ≤ x) ∧ IsOrdered l ∧ IsOrdered r ∧ (v ∈ l ∨ v ∈ r)

/- empty tree is always ordered -/
@[grind .]
theorem IsOrdered_empty :
  IsOrdered (empty : Better_BinarySearchTree α) := by
  simp [IsOrdered]

/--
A leaf is always ordered.
-/
@[grind .]
theorem IsOrdered_leaf (x: α) :
  IsOrdered (leaf x) := by
  simp [IsOrdered]

/--
If a node is ordered, all elements in its left subtree are less than or equal to the node's value.
-/
@[grind .]
theorem IsOrdered_left_below (v: α) (l r: Better_BinarySearchTree α) (h: IsOrdered (node v l r)) :
  ∀ x ∈ l, x ≤ v := by
  grind

/--
If a node is ordered, all elements in its right subtree are greater than or equal to the node's value.
-/
@[grind .]
theorem IsOrdered_right_above (v: α) (l r: Better_BinarySearchTree α) (h: IsOrdered (node v l r)) :
  ∀ x ∈ r, v ≤ x := by grind

/--
If a node is ordered, its left subtree must also be ordered.
-/
@[grind .]
theorem IsOrdered_left_subtree (v: α) (l r: Better_BinarySearchTree α) (h: IsOrdered (node v l r)) :
  IsOrdered l := by
  grind

/--
If a node is ordered, its right subtree must also be ordered.
-/
@[grind .]
theorem IsOrdered_right_subtree (v: α) (l r: Better_BinarySearchTree α) (h: IsOrdered (node v l r)) :
  IsOrdered r := by
  grind

/--
Adds a label to the binary search tree while maintaining the tree structure.
-/
@[grind .]
def BinarySearchTree.addLabel (t: Better_BinarySearchTree α) (label: α) : Better_BinarySearchTree α :=
  match t with
  | empty => leaf label
  | leaf x =>
    if label = x then
      leaf x
    else
    if label < x then
      node label (leaf label) (leaf x)
    else
      node label (leaf x) (leaf label)
  | node v l r =>
    if label ≤ v then
      node v (BinarySearchTree.addLabel l label) r
    else
      node v l (BinarySearchTree.addLabel r label)

/--
An element is in the tree after adding a label if and only if it was already there or it is the new label.
-/
@[grind .]
theorem mem_addLabel (t: Better_BinarySearchTree α) (label: α) (x : α) :
    x ∈ BinarySearchTree.addLabel t label ↔ x = label ∨ x ∈ t := by
  induction t with
  | empty =>   simp[BinarySearchTree.addLabel,Membership.mem,Better_BinarySearchTree.mem,eq_comm]
  | leaf v =>
    by_cases label ≤ v <;> grind
  | node v l r ihl ihr =>
    by_cases label ≤ v <;> grind

/--
Adding a label to an ordered tree results in an ordered tree.
-/
theorem ordered_addLabel (t: Better_BinarySearchTree α) (label: α)
  (h: IsOrdered t) :
    IsOrdered (BinarySearchTree.addLabel t label) := by
  induction t with
  | empty => simp[BinarySearchTree.addLabel]
  | leaf x =>
    by_cases label ≤ x <;> grind
  | node v l r ihl ihr =>
    by_cases label ≤ v <;> grind

/--
Returns the value at the root of a node, or the value in a leaf.
-/
def pivot  (T:Better_BinarySearchTree α)(h : T ≠ empty) :  α:= match T with
| node l .. =>  l
| leaf l =>  l

/--
The pivot of an ordered tree is always a member of the tree.
-/
@[grind .]
theorem pivot_member (l: Better_BinarySearchTree α)(h: l ≠ empty) (h₀ : IsOrdered l) :
  pivot l h ∈ l := by
  induction l with
  | empty =>  contradiction
  | leaf l => grind [pivot]
  | node label left right ihl ihr =>
    grind [pivot]

/--
Efficiently checks if a label is in an ordered binary search tree.
-/
@[grind .]
def fastCheckMem (label : α)(l: Better_BinarySearchTree α) : Bool := match l with
  | empty => False
  | leaf l => l == label
  | node l left right =>
    if l == label then true
    else if label < l then fastCheckMem label left
    else fastCheckMem label right

/--
`fastCheckMem` correctly determines membership in an ordered tree.
-/
theorem fastCheckMem_correct (label : α)(l: Better_BinarySearchTree α)(h : IsOrdered l):
  fastCheckMem label l = true ↔ label ∈ l := by
  induction l with
  | empty => simp[fastCheckMem,Better_BinarySearchTree.mem,Membership.mem]
  | leaf label' =>
    grind
  | node label' left right ihl ihr =>
    if p:label' = label
      then
        grind
    else
      if p':label < label'
      then
        grind
      else
        grind


/-!
## Exercise: Deletion

Define a function `deleteLabel` that removes a label from an ordered binary search tree while maintaining the tree structure and order properties. Prove that after deletion, the label is no longer in the tree, and that all other labels are still present.
-/



end better_binary_search_tree

end langur
