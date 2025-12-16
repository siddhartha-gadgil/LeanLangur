import Mathlib
import Qq

namespace TowersOfHanoi

abbrev Disk := Nat

@[grind cases, grind ext, ext]
structure Peg where
  disks : List Disk
  disks_sorted : disks.Pairwise (· < ·) := by first | decide | grind
deriving Repr

structure BoardState where
  leftPeg : Peg
  middlePeg : Peg
  rightPeg : Peg
deriving Repr

abbrev egState : BoardState := {
  leftPeg := { disks := [] }
  middlePeg := { disks := [] },
  rightPeg := { disks := [1, 2, 3] }
}

@[grind]
def isCompatibleWith (disk : Disk) (peg : Peg) : Prop :=
  match peg.disks with
  | [] => True
  | headDisk :: _peg => disk < headDisk

infix:50 " ≺ " => isCompatibleWith

attribute [grind =] List.pairwise_cons

@[match_pattern, grind]
abbrev Peg.nil : Peg := { disks := [] }

notation " ∥ " => Peg.nil

@[match_pattern, grind]
abbrev Peg.cons (disk : Disk) (peg : Peg) (compat : disk ≺ peg := by grind) : Peg :=
  { disks := disk :: peg.disks }

infixr:65 " ⤳ " => Peg.cons

#eval 3 ⤳ 5 ⤳ egState.middlePeg

theorem Peg.nil_eq_nil (sorted : ([] : List Disk).Pairwise (· < ·)) : { disks := [], disks_sorted := sorted } = ∥ := by grind

theorem Peg.cons_eq_cons (disk : Disk) (disks : List Disk) (disks_sorted : (disk :: disks).Pairwise (· < ·)) :
  { disks := disk :: disks, disks_sorted := disks_sorted } = disk ⤳ { disks := disks, disks_sorted := .of_cons disks_sorted } := by grind

theorem Peg.cons_eq_cons' (disk : Disk) (peg : Peg) (compat : disk ≺ peg := by grind) :
  disk ⤳ peg = { disks := disk :: peg.disks } := by grind

def Peg.normalize (peg : Peg) : { peg' : Peg // peg = peg' } :=
  match peg with
  | ⟨[], nil_sorted⟩ => { val := ∥, property := Peg.nil_eq_nil nil_sorted }
  | ⟨disk :: disks, peg_sorted⟩ =>
    let peg' : Peg := { disks := disks, disks_sorted := .of_cons peg_sorted }
    let ⟨peg'_norm, peg'_norm_eq⟩ := peg'.normalize
    { val := disk ⤳ peg'_norm,
      property := by rw [Peg.cons_eq_cons]; congr }

theorem Peg.normalize_eq (peg : Peg) : peg = ↑peg.normalize :=
  peg.normalize.property

inductive MoveRel : BoardState → BoardState → Prop where
  | leftToMiddle (leftPeg middlePeg rightPeg : Peg) (disk : Disk) (compat_src : disk ≺ leftPeg := by grind) (compat_tgt : disk ≺ middlePeg := by grind) :
      MoveRel { leftPeg := disk ⤳ leftPeg, middlePeg, rightPeg } { leftPeg, middlePeg := disk ⤳ middlePeg, rightPeg }

  | leftToRight (leftPeg middlePeg rightPeg : Peg) (disk : Disk) (compat_src : disk ≺ leftPeg := by grind) (compat_tgt : disk ≺ rightPeg := by grind) :
      MoveRel { leftPeg := disk ⤳ leftPeg, middlePeg, rightPeg } { leftPeg, middlePeg, rightPeg := disk ⤳ rightPeg }

  | middleToLeft (leftPeg middlePeg rightPeg : Peg) (disk : Disk) (compat_src : disk ≺ middlePeg := by grind) (compat_tgt : disk ≺ leftPeg := by grind) :
      MoveRel { leftPeg, middlePeg := disk ⤳ middlePeg, rightPeg } { leftPeg := disk ⤳ leftPeg, middlePeg, rightPeg }

  | middleToRight (leftPeg middlePeg rightPeg : Peg) (disk : Disk) (compat_src : disk ≺ middlePeg := by grind) (compat_tgt : disk ≺ rightPeg := by grind) :
      MoveRel { leftPeg, middlePeg := disk ⤳ middlePeg, rightPeg } { leftPeg, middlePeg, rightPeg := disk ⤳ rightPeg }

  | rightToLeft (leftPeg middlePeg rightPeg : Peg) (disk : Disk) (compat_src : disk ≺ rightPeg := by grind) (compat_tgt : disk ≺ leftPeg := by grind) :
      MoveRel { leftPeg, middlePeg, rightPeg := disk ⤳ rightPeg } { leftPeg := disk ⤳ leftPeg, middlePeg, rightPeg }

  | rightToMiddle (leftPeg middlePeg rightPeg : Peg) (disk : Disk) (compat_src : disk ≺ rightPeg := by grind) (compat_tgt : disk ≺ middlePeg := by grind) :
      MoveRel { leftPeg, middlePeg, rightPeg := disk ⤳ rightPeg } { leftPeg, middlePeg := disk ⤳ middlePeg, rightPeg }

abbrev MoveReachable := Relation.ReflTransGen MoveRel

section Tactics

open Lean Elab Meta Term Tactic Simp Qq

-- def normalizePegSimprocQ : SimprocQ := fun u α e ↦ do
--   let .succ .zero := u | return .continue
--   let ~q(Peg) := α | return .continue
--   let ~q(Subtype.mk $peg $peg_eq) := q(Peg.normalize $e) | return .continue
--   return .done <| .mk peg (some peg_eq) true

-- simproc ↓ normalizePeg (Peg.mk _ _) := .ofQ normalizePegSimprocQ

macro "normalize_pegs" : tactic => `(tactic| (
  simp (config := { singlePass := true }) only [Peg.normalize_eq]
  simp only [Peg.normalize] ))

macro "board_move_template" move:term : tactic => do
  `(tactic| (
    trans
    · apply Relation.ReflTransGen.single
      apply $move
      · grind
      · grind
  ))

macro "left_to_middle" : tactic => `(tactic| board_move_template MoveRel.leftToMiddle)

macro "left_to_right" : tactic => `(tactic| board_move_template MoveRel.leftToRight)

macro "middle_to_left" : tactic => `(tactic| board_move_template MoveRel.middleToLeft)

macro "middle_to_right" : tactic => `(tactic| board_move_template MoveRel.middleToRight)

macro "right_to_left" : tactic => `(tactic| board_move_template MoveRel.rightToLeft)

macro "right_to_middle" : tactic => `(tactic| board_move_template MoveRel.rightToMiddle)

macro "finish" : tactic => `(tactic| rfl)

end Tactics

example : MoveReachable egState ⟨ { disks := [1, 2, 3] }, .nil, .nil ⟩ := by
  rw [egState]
  normalize_pegs
  right_to_left
  right_to_middle
  left_to_middle
  right_to_left
  middle_to_right
  middle_to_left
  right_to_left
  finish

end TowersOfHanoi
