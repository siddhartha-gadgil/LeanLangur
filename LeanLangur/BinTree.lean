import Mathlib -- imports definitions and theorems used below
/-!
## Prerequisite files

* `ListOps.lean` - implicit and explicit parameters and monadic `do` notation for lists.

## Main concepts introduced

* inductive types.
* recursive functions on trees.
* membership proofs.
-/

/-!
## Binary Trees

We consider an example of a data structure: binary trees. We define a binary tree datatype, a function to convert a binary tree to a list, and prove that membership in the tree corresponds to membership in the list.

This is our first example of defining an *inductive type*.
-/

namespace langur -- starts a namespace to group the tutorial definitions

variable {α : Type}

/--
A simple binary tree where each leaf carries a value of type `α`,
and nodes represent branches with two subtrees.
-/
inductive BinTree (α : Type) where -- declares the inductive type or proposition `BinTree`
  | leaf : α → BinTree α -- declares another constructor or syntax alternative
  | node : BinTree α → BinTree α → BinTree α -- declares another constructor or syntax alternative
deriving Repr, Inhabited -- asks Lean to generate standard instances automatically

open BinTree -- opens names so constructors or helpers can be written unqualified

/--
Converts a binary tree to a list by performing an in-order traversal.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
def BinTree.toList {α : Type} : BinTree α → List α -- defines `BinTree.toList`
  | leaf x => [x] -- matches a leaf tree and returns `[x]`
  | node l r => -- matches an internal tree node and returns the concatenation of the left and right subtree lists
    BinTree.toList l ++ BinTree.toList r

/-- An example binary tree containing natural numbers. -/
def exampleTree : BinTree Nat := -- defines `exampleTree`
  node (node (leaf 1) (leaf 2)) (leaf 3)

#eval exampleTree.toList  -- Output: [1, 2, 3]

/--
Inductive predicate for membership in a binary tree.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
def Bintree.mem {α : Type} : BinTree α → α → Prop -- defines `Bintree.mem`
  | leaf x, y => x = y -- matches a leaf tree and returns `x = y`
  | node l r, y => Bintree.mem l y ∨ Bintree.mem r y -- matches an internal tree node and returns `Bintree.mem l y ∨ Bintree.mem r y`

/--
Instance for using the `∈` notation with `BinTree`.
-/
@[grind ., simp] -- annotation controlling elaboration, simplification, or automation
instance {α : Type} : Membership α (BinTree α) where -- provides an instance for typeclass search
  mem := Bintree.mem

/--
An element `y` is in a leaf carrying `x` if and only if `x = y`.
-/
@[grind ., simp] -- annotation controlling elaboration, simplification, or automation
theorem mem_leaf {α : Type} (x y : α) : -- states and proves theorem `mem_leaf`
    y ∈ leaf x ↔ x = y := by -- starts tactic mode; the following tactics prove the proposition just stated
    simp [Bintree.mem, Membership.mem] -- simplifies the current goal or hypotheses

/--
An element `y` is in a node if and only if it is in either the left or the right subtree.
-/
@[grind ., simp] -- annotation controlling elaboration, simplification, or automation
theorem mem_node {α : Type} (l r : BinTree α) (y : α) : -- states and proves theorem `mem_node`
    y ∈ node l r ↔ y ∈ l ∨ y ∈ r := by -- starts tactic mode; the following tactics prove the proposition just stated
    simp [Bintree.mem, Membership.mem] -- simplifies the current goal or hypotheses

/--
Theorem stating that an element is in the tree if and only if it is in the list
produced by `toList`.
-/
theorem mem_iff_mem_toList {α : Type} (t : BinTree α) (x : α) : -- states and proves theorem `mem_iff_mem_toList`
    x ∈ t ↔ x ∈ BinTree.toList t := by -- starts tactic mode; the following tactics prove the proposition just stated
    apply Iff.intro -- applies `Iff.intro` backwards, replacing the current goal by its premises
    · induction t with -- focuses the next proof branch
    | leaf a => grind -- matches a leaf tree and asks `grind` to solve this case
    | node l r ihl ihr => grind -- matches an internal tree node and asks `grind` to solve this case
    · induction t with -- focuses the next proof branch
    | leaf a => grind -- matches a leaf tree and asks `grind` to solve this case
    | node l r ihl ihr => grind -- matches an internal tree node and asks `grind` to solve this case

/-!
## Exercise: List to BinTree

Define a function `listToBinTree : List α → BinTree α` that converts a list to a binary tree (this is not unique). Then, prove that for any list `l` and element `x`, `x ∈ listToBinTree l` if and only if `x ∈ l`.
-/
end langur -- closes the current namespace or section
/-!
## Next files

* `BinarySearchTree.lean` - binary search trees; order invariants; search operations.
* `FunEquality.lean` - equality of functions; decision procedures; proof irrelevance.
* `IsEven.lean` - inductive propositions; basic use of `grind`.
-/
