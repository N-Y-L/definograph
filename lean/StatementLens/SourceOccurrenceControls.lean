import StatementLens.Context

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace StatementLens.SourceOccurrenceControls
open Lean Meta Elab StatementLens.SourceSnapshot

private def require (ok : Bool) (message : String) : MetaM Unit :=
  unless ok do throwError "source occurrence control failed: {message}"
private def field (value : Json) (key : String) : Json :=
  (value.getObjVal? key).toOption.getD .null
private def parentId := "12345678-1234-4234-8234-123456789abc"
private def childId := "22345678-1234-4234-8234-123456789abc"
private def selection : Selection := ⟨0, 1, 0, 1⟩
private def raw (e : Expr) : Json := (Definograph.rawExprJson e).toOption.getD .null
private def info (expression : Expr) : MetaM (TermInfo × ContextInfo) := do
  let lctx ← getLCtx
  let env ← getEnv
  let mctx ← getMCtx
  let options ← getOptions
  let ngen := (← getThe Core.State).ngen
  let term : TermInfo := { elaborator := .anonymous, stx := .missing, lctx := lctx, expectedType? := none, expr := expression }
  let context : ContextInfo := { env, mctx, options, ngen, fileMap := default, parentDecl? := some `OccurrenceControl }
  return (term, context)
private def request (snapshot : Json) (path : List String) : Json := Json.mkObj [
  ("schema", toJson "definograph.source-occurrence-request.v1"), ("parentCaptureId", toJson parentId),
  ("selection", field snapshot "selection"), ("prepared", field snapshot "prepared"), ("path", toJson path)]
private def checks (record : Json) : Array Json :=
  (field (field record "checking") "checks").getArr?.toOption.getD #[]
private def completed (record : Json) : Bool :=
  field (field (field record "checking") "action") "status" == toJson "completed"
private def test (term : TermInfo) (context : ContextInfo) (path : List String) : MetaM Json := do
  let parent ← capture term context parentId selection
  let fresh ← capture term context childId selection
  captureOccurrence term context childId selection (request parent path) fresh

def ordinary : MetaM Unit := do
  let expression := .app (.lam `same (mkConst ``Nat) (.bvar 0) .default) (mkRawNatLit 7)
  let (term, context) ← info expression
  for (path, expected, arity) in [([], expression, 0), (["appFun"], expression.appFn!, 0),
      (["appArg"], mkRawNatLit 7, 0), (["appFun", "lamDomain"], mkConst ``Nat, 0),
      (["appFun", "lamBody"], .bvar 0, 1)] do
    let result ← test term context path
    require (completed result && (checks result).size == 6 &&
      (checks result).all (fun c => field (field c "outcome") "tag" == toJson "accepted"))
      "ordinary occurrence did not receive six accepted outcomes"
    let selected := field (field result "checking") "selected"
    require (field selected "term" == raw expected && field (field selected "home") "arity" == toJson arity)
      "selected component or binder home changed"
    require (!(← getEnv).contains (.str `StatementLens.SourceOccurrence childId ++ `source ++ `context))
      "extraction leaked diagnostic declarations"
  let invalid ← test term context ["letBody"]
  require (!completed invalid && (checks invalid).size == 2 &&
    field (field invalid "checking") "selected" == .null) "invalid path lost partial receipts or fabricated selection"
  IO.println "PASS occurrence ordinary: root/function/argument/domain/body, exact home, invalid path prefix and isolation"

def dependent : MetaM Unit := do
  let expression := V6Structured.dec OccurrenceDecomposition.HomeControls.dependentLet
  let (term, context) ← info expression
  for (path, arity) in [(["lamBody", "letType"], 1), (["lamBody", "letValue"], 1),
      (["lamBody", "letBody", "lamDomain"], 2), (["lamBody", "letBody", "lamBody"], 3)] do
    let result ← test term context path
    require (completed result && field (field (field (field result "checking") "selected") "home") "arity" == toJson arity)
      "dependent let occurrence acquired the wrong home"
  let owned : Expr := .letE `same (mkConst ``Nat) (mkRawNatLit 7) (.bvar 0) true
  let (term, context) ← info owned
  let selected ← test term context ["letBody"]
  let telescope := field (field (field (field selected "checking") "selected") "home") "telescope"
  require (completed selected && ((telescope.getArr?).toOption.getD #[])[3]?.getD .null == toJson true)
    "owned nondep source let lost its original flag"
  withLetDecl `same (mkConst ``Nat) (.mdata ⟨[(`ignored, .ofBool true)]⟩ (mkConst ``True.intro))
      (nondep := true) fun x => do
    let (term, context) ← info x
    let result ← test term context []
    require (completed result && ((field (field (field (field result "checking") "selected") "home") "telescope").getArr?.toOption.getD #[])[0]?.getD .null == toJson "port")
      "ignored external value became a defining equation"
  let u := .param `controlU
  let poly : Expr := .lam `A (.sort u) (.lam `x (.bvar 0) (.bvar 0) .default) .implicit
  let (term, context) ← info poly
  require (completed (← test term context ["lamBody", "lamBody"])) "universe parameters were lost"
  IO.println "PASS occurrence dependent homes: repeated names, domain/value/body, owned have, opaque external value and universe parameters"

def boundaries : MetaM Unit := do
  let (term, context) ← info (mkRawNatLit 7)
  let parent ← capture term context parentId selection
  let fresh ← capture term context childId selection
  let good := request parent []
  for bad in [good.setObjVal! "selection" ((field good "selection").setObjVal! "endByte" (toJson (2 : Nat))),
      good.setObjVal! "prepared" ((field good "prepared").setObjVal! "checkerUniverseParams" (toJson ["changed"])),
      good.setObjVal! "prepared" ((field good "prepared").setObjVal! "frame"
        ((field (field good "prepared") "frame").setObjVal! "sourceTerm" (raw (mkRawNatLit 8)))),
      good.setObjVal! "selection" ((field good "selection").setObjVal! "parentDeclaration" (Definograph.nameJson `Other))] do
    let result ← captureOccurrence term context childId selection bad fresh
    require (field (field result "checking") "phase" == toJson "parent-match" &&
      field (field result "checking") "attempted" == toJson false && (checks result).isEmpty)
      "stale parent fields reached extraction"
  let wrongPolicy := fresh.setObjVal! "policy" .null
  let result ← captureOccurrence term context childId selection good wrongPolicy
  require (field (field result "checking") "attempted" == toJson false) "changed policy reached extraction"
  -- Supplying matching parent JSON does not replace the actual captured term.
  let (changed, _) ← info (mkRawNatLit 8)
  let result ← captureOccurrence changed context childId selection good fresh
  require (field (field result "checking") "phase" == toJson "parent-match" &&
    field (field result "checking") "attempted" == toJson false) "fresh reprepare mismatch reached extraction"
  for bad in [good.setObjVal! "path" (toJson ["instBody"]), good.setObjVal! "path" (toJson (List.replicate 65 "appFun")),
      good.setObjVal! "unexpected" .null] do
    let refused ← try
      let _ ← captureOccurrence term context childId selection bad fresh
      pure false
    catch _ => pure true
    require refused "invalid request did not fail before forming an occurrence"
  let (annotated, context) ← info (.mdata {} (mkRawNatLit 0))
  let result ← test annotated context []
  require (field (field result "checking") "status" == toJson "unavailable" &&
    field (field result "checking") "attempted" == toJson true) "semantic metadata was erased or misreported"
  let placeholder ← mkSorry (mkConst ``Nat) false
  let (term, context) ← info placeholder
  let result ← test term context []
  require (field (field result "checking") "phase" == toJson "source-policy" &&
    field (field result "checking") "attempted" == toJson false) "placeholder entered source checks"
  IO.println "PASS occurrence boundaries: parent/frame/params/range/policy/reprepare mismatch, path limits, raw metadata and sorry policy"

def inferenceAndOutcomes : MetaM Unit := do
  let product : Expr := .forallE `same (mkConst ``Nat) (.app (mkConst ``Fin) (.bvar 0)) .default
  let (term, context) ← info product
  for (path, home) in [(["piDomain"], 0), (["piBody"], 1)] do
    let result ← test term context path
    require (completed result && field (field (field (field result "checking") "selected") "home") "arity" == toJson home)
      "dependent product domain/body selected the wrong home"
  let pair := mkApp4 (mkConst ``Prod.mk [.succ .zero, .succ .zero])
    (mkConst ``Nat) (mkConst ``Nat) (mkRawNatLit 3) (mkRawNatLit 4)
  let (term, context) ← info (.proj ``Prod 0 pair)
  let projected ← test term context ["projValue"]
  require (completed projected && field (field (field projected "checking") "selected") "term" == raw pair)
    "projection traversal changed its exact projected value"
  -- Root inference supplies Nat without checking this deliberately wrong argument.
  -- The valid function selection must not conceal either rejected root component.
  let badRoot := .app (.lam `same (mkConst ``Nat) (.bvar 0) .default) (mkConst ``True.intro)
  let (term, context) ← info badRoot
  let mixed ← test term context ["appFun"]
  let outcomes := (checks mixed).map fun c => field (field c "outcome") "tag"
  require (completed mixed && outcomes == #[toJson "accepted", toJson "rejected", toJson "accepted",
      toJson "rejected", toJson "accepted", toJson "accepted"])
    "successful inferred selection concealed rejected original/root typing"
  let assigned ← mkFreshExprMVar (some (.forallE `x (mkConst ``Nat) (mkConst ``Nat) .default))
  assigned.mvarId!.assign (.lam `x (mkConst ``Nat) (mkRawNatLit 9) .default)
  let (term, context) ← info (.app assigned (mkRawNatLit 7))
  let parent ← capture term context parentId selection
  let fresh ← capture term context childId selection
  require (field (field (field parent "original") "frame") "sourceTerm" !=
    field (field (field parent "prepared") "frame") "sourceTerm") "assigned-beta topology control did not differ"
  let selected ← captureOccurrence term context childId selection (request parent []) fresh
  require (completed selected && field (field (field selected "checking") "selected") "term" == raw (mkRawNatLit 9))
    "prepared selection reused original application topology"
  let invalid ← captureOccurrence term context childId selection (request parent ["appFun"]) fresh
  require (!completed invalid && (checks invalid).size == 2) "original path was accepted on changed prepared topology"
  -- inferType on this forall creates assignments and a universe metavariable;
  -- fresh inference state must be retained even though finished admission fails.
  let body ← mkFreshExprMVar none
  let (term, context) ← info (.forallE `x (mkConst ``Nat) body .default)
  let unresolved ← test term context []
  require (field (field unresolved "checking") "phase" == toJson "occurrence-capture" &&
    field (field unresolved "checking") "attempted" == toJson true)
    "fresh inference state was lost before source admission"
  IO.println "PASS occurrence inference/outcomes: products, projection, mixed rejection/success, assigned beta topology and fresh inference state"

def transport : MetaM Unit := do
  let (term, context) ← info (mkRawNatLit 7)
  let parent ← capture term context parentId selection
  let fresh ← capture term context childId selection
  let occurrence ← captureOccurrence term context childId selection (request parent []) fresh
  let legacy := Json.mkObj [("ok", toJson false), ("error", toJson "guided unavailable"), ("diagnostics", Json.arr #[])]
  let response := legacy.setObjVal! "sourceSnapshot" fresh |>.setObjVal! "sourceOccurrence" occurrence
  let serialized := StatementLens.Context.serializeContextResponse response
  let decoded ← IO.ofExcept (Json.parse serialized)
  require (field decoded "sourceSnapshot" == fresh && field decoded "sourceOccurrence" == occurrence &&
    serialized.startsWith ((StatementLens.Response.serializeResponse legacy).dropEnd 1).toString)
    "occurrence attachment changed legacy bytes or the source snapshot"
  let huge := toJson (String.ofList (List.replicate (2200 * 1024) 'x'))
  let oversized := (response.setObjVal! "source" huge).setObjVal! "sourceOccurrence"
    (occurrence.setObjVal! "checking" ((field occurrence "checking").setObjVal! "oversizedControl" huge))
  let decoded ← IO.ofExcept (Json.parse (StatementLens.Context.serializeContextResponse oversized))
  require (field decoded "sourceSnapshot" == fresh) "guided/occurrence limits discarded original snapshot"
  -- Exercise the combined cap independently: a just-under-limit legacy field
  -- and a bounded-sized simulated snapshot plus complete occurrence body.
  let text := fun count => toJson (String.ofList (List.replicate count 'x'))
  let combined := Json.mkObj [("ok", toJson true), ("diagnostics", Json.arr #[]),
    ("source", text (1900 * 1024)), ("sourceSnapshot", text (1500 * 1024)),
    ("sourceOccurrence", occurrence.setObjVal! "checking"
      ((field occurrence "checking").setObjVal! "oversizedControl" (text (750 * 1024))))]
  let limitedText := StatementLens.Context.serializeContextResponse combined
  let limited ← IO.ofExcept (Json.parse limitedText)
  let kept := field limited "sourceOccurrence"
  require (limitedText.utf8ByteSize ≤ 4 * 1024 * 1024 && field kept "path" == field occurrence "path" &&
    field (field kept "checking") "phase" == toJson "occurrence-output" &&
    field (field kept "checking") "attempted" == toJson true && (checks kept).isEmpty)
    "combined transport limit truncated receipts or dropped association"
  let mut lctx ← getLCtx
  for i in [:122] do lctx := lctx.mkLocalDecl ⟨.num `occurrenceLocal i⟩ `same (mkConst ``Nat) .default
  withLCtx' lctx do
    let (term, context) ← info (mkRawNatLit 7)
    let deep ← test term context []
    require (field (field deep "checking") "phase" == toJson "occurrence-output" &&
      field (field deep "checking") "attempted" == toJson true && (checks deep).isEmpty)
      "deep actual closures were not omitted as one complete record"
  IO.println "PASS occurrence transport: unchanged guided prefix, independent attachments, combined cap and actual deep closure omission"

end StatementLens.SourceOccurrenceControls

#eval StatementLens.SourceOccurrenceControls.ordinary
#eval StatementLens.SourceOccurrenceControls.dependent
#eval StatementLens.SourceOccurrenceControls.boundaries
#eval StatementLens.SourceOccurrenceControls.inferenceAndOutcomes
#eval StatementLens.SourceOccurrenceControls.transport
