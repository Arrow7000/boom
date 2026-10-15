import TreeCalculus.Redex
import ProofWidgets.Component.HtmlDisplay

/-!
# Infoview trees

`#tree t` evaluates the Lean expression `t : Term` and displays its syntax as
an ordered tree. It does not perform Tree Calculus reductions. Nodes with
three or more children are displayed in full, without assuming normal form.
Branch colours change at each split and are shared with the linked expression.
Redex colours mark local rewrite sites independently, including under stems.
The widget uses React supplied by the infoview; no npm build is needed.
-/

namespace Term

/-- A nested JSON array encodes the ordered children of each node. -/
def treeJson : Term → Lean.Json
  | .term children => .arr (children.map treeJson).toArray

/-- Local rule labels, in the same preorder as the diagram's node IDs. -/
def redexLabels : Term → List String
  | t@(.term children) =>
    (t.redexRule.map RedexRule.label |>.getD "") :: children.flatMap redexLabels

structure TreeProps where
  tree : Lean.Json
  label : String
  redexRules : Array String
  deriving Lean.Server.RpcEncodable

@[widget_module]
def treeWidget : ProofWidgets.Component TreeProps where
  javascript := include_str "tree.js"

/-- Render syntax directly, including any unapplied or excess arguments. -/
def toHtml (t : Term) (label : String := "Tree Calculus") : ProofWidgets.Html :=
  .ofComponent treeWidget ⟨t.treeJson, label, t.redexLabels.toArray⟩ #[]

instance : ProofWidgets.HtmlEval Term where
  eval t := pure t.toHtml

end Term

/-- Display a `Term` as an info message containing an interactive tree. -/
syntax (name := treeCmd) "#tree " term : command

open Lean Elab Command in
@[command_elab treeCmd]
def elabTreeCmd : CommandElab := fun
  | `(#tree%$tk $t:term) => do
    let label := (t.raw.getSubstring? false false).map (·.toString) |>.getD "Tree Calculus"
    let action ← liftTermElabM <| ProofWidgets.HtmlCommand.evalCommandMHtml
      (← `(ProofWidgets.HtmlEval.eval (_root_.Term.toHtml ($t : _root_.Term) $(quote label))))
    let html ← action
    -- A real message gives #tree the same editor information marker as #eval,
    -- and makes its output available in Messages without a separate panel.
    logInfoAt tk (← liftCoreM <| MessageData.ofHtml html s!"Tree Calculus: {label}")
  | _ => throwUnsupportedSyntax
