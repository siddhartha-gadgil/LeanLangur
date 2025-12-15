import Mathlib

variable {α : Type}

inductive BinTree (α : Type) where
  | leaf : α → BinTree α
  | node : BinTree α → BinTree α → BinTree α
deriving Repr, Inhabited

open BinTree

@[grind .]
def BinTree.toList {α : Type} : BinTree α → List α
  | leaf x => [x]
  | node l r =>
    BinTree.toList l ++ BinTree.toList r

def exampleTree : BinTree Nat :=
  node (node (leaf 1) (leaf 2)) (leaf 3)

#eval exampleTree.toList  -- Output: [1, 2, 3]

def Bintree.mem {α : Type} : BinTree α → α → Prop
  | leaf x, y => x = y
  | node l r, y => Bintree.mem l y ∨ Bintree.mem r y

@[grind ., simp]
instance {α : Type} : Membership α (BinTree α) where
  mem := Bintree.mem

@[grind ., simp]
theorem mem_leaf {α : Type} (x y : α) :
    y ∈ leaf x ↔ x = y := by
    simp [Bintree.mem]

@[grind ., simp]
theorem mem_node {α : Type} (l r : BinTree α) (y : α) :
    y ∈ node l r ↔ y ∈ l ∨ y ∈ r := by
    simp [Bintree.mem]


theorem mem_iff_mem_toList {α : Type} (t : BinTree α) (x : α) :
    x ∈ t ↔ x ∈ BinTree.toList t := by
    apply Iff.intro
    · induction t with
    | leaf a => grind
    | node l r ihl ihr => grind
    · induction t with
    | leaf a => grind
    | node l r ihl ihr => grind
