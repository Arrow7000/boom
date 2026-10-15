/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TreeCalculus.Redex
import ProofWidgets.Component.HtmlDisplay

/-!
# Infoview trees

`#tree t` evaluates the Lean expression `t : Term` and displays its syntax as
an ordered tree. Nodes with three or more children are displayed in full,
without assuming normal form. Local rewrite sites are coloured, including under
stems. The widget can step through reductions as a preview, calling
`Term.rewriteAt?` over RPC; the Lean term itself is never changed.
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

/-- Inverse of `treeJson`, for trees sent back by the widget. -/
partial def ofJson? : Lean.Json → Except String Term
  | .arr children => return .term (← children.toList.mapM ofJson?)
  | _ => throw "expected a tree of nested arrays"

structure TreeProps where
  tree : Lean.Json
  label : String
  redexRules : Array String
  deriving Lean.Server.RpcEncodable

@[widget_module]
def treeWidget : ProofWidgets.Component TreeProps where
  javascript := include_str "tree.js"

section Rpc
open Lean (Json)
open Lean.Server

structure StepParams where
  tree : Json
  /-- Child indices from the root; `none` selects the leftmost-outermost redex. -/
  path : Option (Array Nat)
  deriving RpcEncodable

structure StepResult where
  tree : Json
  redexRules : Array String
  path : Array Nat
  rule : String
  deriving RpcEncodable

structure RunParams where
  tree : Json
  maxSteps : Nat
  maxNodes : Nat
  deriving RpcEncodable

structure RunResult where
  tree : Json
  redexRules : Array String
  steps : Nat
  deriving RpcEncodable

private def decode (json : Json) : RequestM Term :=
  match Term.ofJson? json with
  | .ok t => pure t
  | .error e => throw (RequestError.invalidParams e)

/-- One rewrite with `Term.rewriteAt?`, which is proved sound for `Reduces`. -/
@[server_rpc_method]
def stepRpc (p : StepParams) : RequestM (RequestTask StepResult) := RequestM.asTask do
  let t ← decode p.tree
  let some path := (p.path.map Array.toList).orElse fun _ => t.firstRedex?
    | throw (RequestError.invalidParams "no redex to rewrite")
  let some t' := t.rewriteAt? path | throw (RequestError.invalidParams "no redex at this node")
  let rule := (t.subtermAt? path).bind redexRule |>.map RedexRule.label |>.getD ""
  return { tree := t'.treeJson, redexRules := t'.redexLabels.toArray, path := path.toArray, rule }

/-- Leftmost-outermost reduction until normal form or a limit is reached. -/
@[server_rpc_method]
def runRpc (p : RunParams) : RequestM (RequestTask RunResult) := RequestM.asTask do
  let (t', steps) := (← decode p.tree).runOutermost p.maxSteps p.maxNodes
  return { tree := t'.treeJson, redexRules := t'.redexLabels.toArray, steps }

end Rpc

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
