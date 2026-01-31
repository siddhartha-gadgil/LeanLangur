import Lean
import ProofWidgets
import Mathlib

open Lean

namespace TacTicToe

inductive Player where
  | X
  | O
deriving Repr, DecidableEq, ToJson, FromJson

def Player.opponent : Player → Player
  | .X => .O
  | .O => .X

abbrev Board := Matrix (Fin 3) (Fin 3) (Option Player)

abbrev emptyBoard : Board :=
  !![none, none, none; none, none, none; none, none, none]

structure BoardState where
  currentPlayer : Player := .X
  board : Board := emptyBoard
deriving Repr, TypeName

inductive MoveRel : BoardState → BoardState → Prop where
  | place (row col : Fin 3) (state : BoardState) (condition : state.board row col = none := by decide) :
      MoveRel state
        { currentPlayer := state.currentPlayer.opponent,
          board := fun r c ↦ if r = row ∧ c = col then some state.currentPlayer else state.board r c }

abbrev MoveReachable : BoardState → BoardState → Prop :=
  Relation.ReflTransGen MoveRel

abbrev isWinningPositionFor (player : Player) (state : BoardState) : Prop :=
  (∃ i : Fin 3, (∀ j : Fin 3, state.board.row i j = some player)) ∨
  (∃ i : Fin 3, (∀ j : Fin 3, state.board.col i j = some player)) ∨
  (∀ i : Fin 3, state.board i i = some player) ∨
  (∀ i : Fin 3, state.board i (3 - i) = some player)

def findWinningPositionFor (player : Player) {board : BoardState} (gameTrace : MoveReachable {} board) :=
  ∃ state, isWinningPositionFor player state ∧ MoveReachable {} state

theorem findWinningPositionFor.ofUpdate {player : Player} {board : BoardState} {gameTrace : MoveReachable {} board}
    (row : Fin 3) (col : Fin 3) (condition : board.board row col = none := by decide) :
    findWinningPositionFor player (.tail gameTrace (MoveRel.place row col board condition)) →
    findWinningPositionFor player gameTrace := id

theorem findWinningPositionFor.ofWinningPosition {player : Player} {board : BoardState} {gameTrace : MoveReachable {} board}
    (winningPosition : isWinningPositionFor player board := by dsimp; decide) : findWinningPositionFor player gameTrace :=
  ⟨board, winningPosition, gameTrace⟩

open Lean Elab Meta Tactic

macro "play" row:num col:num : tactic => `(tactic| apply findWinningPositionFor.ofUpdate $row $col)

macro "finish" : tactic => `(tactic| exact findWinningPositionFor.ofWinningPosition)

section Widget

open ProofWidgets Server Jsx

@[server_rpc_method]
def Renderer.rpcMethod (props : PanelWidgetProps) : RequestM (RequestTask Html) := RequestM.asTask do
  let docMeta := (← read).doc.meta
  if props.goals.isEmpty then
        return <span>No goals.</span>
  let some g := props.goals[0]? | unreachable!

  g.ctx.val.runMetaM {} do
    let md ← g.mvarId.getDecl
    let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
    Meta.withLCtx lctx md.localInstances do
      let goal := md.type
      match goal with
      | .app (.app (.app (.const ``findWinningPositionFor _) player) board) _ =>
        let board : BoardState ← unsafe evalExpr BoardState (.const ``BoardState []) board
        -- let player ← unsafe evalExpr Player (.const ``Player []) player
        -- let finishButton : Html := if isWinningPositionFor player board then
        --   let range : Lsp.Range := ⟨props.pos, props.pos⟩
        --   let newPos := {props.pos with line := props.pos.line + 1 }
        --   let editProps := MakeEditLinkProps.ofReplaceRange' docMeta range s!"finish" (some ⟨newPos, newPos⟩)
        --   .ofComponent MakeEditLink editProps #[.text "🏆 Finish!"]
        -- else
        --   <p></p>
        return renderBoard docMeta board
      | _ => return <span>Goal is not a `findWinningPositionFor` goal.</span>
  where
    renderCell (docMeta : DocumentMeta) (cell : Option Player) (row col : Fin 3) : Html :=
      let display :=
        match cell with
        | none => "□"
        | some .X => "❌"
        | some .O => "🟢"
      let range : Lsp.Range := ⟨props.pos, props.pos⟩
      -- let newPos := { line := props.pos.line + 1, character := 2 }
      let editProps := MakeEditLinkProps.ofReplaceRange' docMeta range s!"\n  play {row} {col}" -- (some ⟨newPos, newPos⟩)
      .ofComponent MakeEditLink editProps #[.text display]
    renderBoard (docMeta : DocumentMeta) (board : BoardState) : Html :=
      let cellStyle := json% {width: "3em", height: "3em", textAlign: "center", border: "2px solid #333", fontSize: "1.5em", cursor: "pointer", transition: "background-color 0.2s"};
      let cell r c := <td style={cellStyle}>{renderCell docMeta (board.board r c) r c}</td>;
      <table style={json% {borderCollapse: "collapse", margin: "10px auto", boxShadow: "0 4px 6px rgba(0,0,0,0.1)"}}>
        <tr>{cell 0 0}{cell 0 1}{cell 0 2}</tr>
        <tr>{cell 1 0}{cell 1 1}{cell 1 2}</tr>
        <tr>{cell 2 0}{cell 2 1}{cell 2 2}</tr>
      </table>

@[widget_module]
def Renderer : Component PanelWidgetProps :=
  mk_rpc_widget% Renderer.rpcMethod

end Widget

show_panel_widgets [Renderer]

example : findWinningPositionFor .X .refl := by
  play 0 0
  play 0 1
  play 1 2
  play 2 0
  play 1 1
  play 1 0
  play 2 2
  finish


end TacTicToe
