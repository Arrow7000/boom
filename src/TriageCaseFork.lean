import TriageContinuations

/-! Concrete Case/Fork continuation construction. -/

namespace TriageCaseFork
open TriageRuleModel (Kind Rule)
open TriageMachine (Syntax Frame)
open TriageContinuations TriageDispatch
open TriageConcrete TriageBoundary TriagePreservation TriageResidual TriageReduction TriageEncoding TriageLocalSemantics

def caseForkRule : Rule := TriageRules.rules[9]
theorem caseForkRule_mem : caseForkRule ∈ TriageRules.rules := by decide

/-- Case/Fork starts evaluating the scrutinized argument and stores the
three exact raw branches in a new Triage frame above the original stack. -/
theorem case_fork {net : Net} (hv : net.valid = true)
    {caseId forkId : Nat} {continuation : End} {w x y arg : Syntax} {frames : List Frame}
    (ha : net.Active caseId forkId) (hcase : net.kind? caseId = some .case_)
    (hfork : net.kind? forkId = some .fork)
    (hcont : Linked net (.agent caseId 1) continuation)
    (hstack : Continuation net [] continuation frames)
    (hw : Source net [] (.agent forkId 1) w) (hx : Source net [] (.agent forkId 2) x)
    (hy : Source net [] (.agent caseId 2) y) (harg : Source net [] (.agent caseId 3) arg) :
    ∃ final input, Step net final ∧ final.valid = true ∧ EvalTask final arg input ∧
      Continuation final [] input (.triage w x y :: frames) := by
  have hc := Net.redexChoice_complete caseForkRule_mem ha hcase hfork
  let core := net.replace caseForkRule caseId forkId
  have hcore : core.valid = true := Net.redexChoice_preserves_valid hv hc
  have hwNew : Source core [] (.agent (net.nextId + 1) 2) w := by
    apply hw.replace_right_aux hv hc
    simp [caseForkRule, TriageRules.rules, ruleLayer, Node.fromRule, layerNeighbor]
  have hxNew : Source core [] (.agent (net.nextId + 1) 3) x := by
    apply hx.replace_right_aux (slot := 1) hv hc
    simp [caseForkRule, TriageRules.rules, ruleLayer, Node.fromRule, layerNeighbor]
  have hyNew : Source core [] (.agent (net.nextId + 1) 4) y := by
    apply hy.replace_left_aux (slot := 1) hv hc
    simp [caseForkRule, TriageRules.rules, ruleLayer, Node.fromRule, layerNeighbor]
  have hargNew : Source core [] (.agent net.nextId 0) arg := by
    apply harg.replace_left_aux (slot := 2) hv hc
    simp [caseForkRule, TriageRules.rules, ruleLayer, Node.fromRule, layerNeighbor]
  have hcontOut := continuation_child_outside (valid_wellFormed hv) ha hcont hstack
  have hstackCore : Continuation core [] continuation frames := hstack.replace hv hc hcontOut
  have hcontWire : core.neighbor (.agent (net.nextId + 1) 1) = some continuation := by
    apply Net.replace_left_aux (slot := 0) hv hc (hcont.neighbor (valid_wellFormed hv)) hcontOut
    simp [caseForkRule, TriageRules.rules, ruleLayer, Node.fromRule, layerNeighbor]
  have heval : core.kind? net.nextId = some .eval := by
    simpa using Net.replace_created_kind hv hc (index := 0) (kind := .eval) (by rfl)
  have htriage := Net.replace_created_kind hv hc (index := 1) (kind := .triage) (by rfl)
  have hnewStack : Continuation core [] (.agent (net.nextId + 1) 0) (.triage w x y :: frames) :=
    .triage htriage (neighborIn_sound hcontWire) hwNew hxNew hyNew hstackCore
  have hwire := Net.replace_internal_wire hv hc
    (first := 0) (firstSlot := 1) (second := 1) (secondSlot := 0) (by decide)
  rcases hargNew.complete with ⟨root, hl, hr⟩
  exact ⟨core, .agent (net.nextId + 1) 0, .chosen hc, hcore,
    ⟨net.nextId, root, heval, hr, hl.neighbor (valid_wellFormed hcore), by simpa using hwire⟩,
    hnewStack⟩

end TriageCaseFork
