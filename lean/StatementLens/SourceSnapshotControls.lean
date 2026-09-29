import StatementLens.Context

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace StatementLens.SourceSnapshotControls
open Lean Meta Elab
open StatementLens.SourceSnapshot

private def require (ok : Bool) (message : String) : MetaM Unit :=
  unless ok do throwError "source snapshot control failed: {message}"

private def field (value : Json) (key : String) : Json :=
  (value.getObjVal? key).toOption.getD .null

private def item (value : Json) (index : Nat) : Json :=
  ((value.getArr?).toOption.getD #[])[index]?.getD .null

private def same (left right : Json) : Bool := left.compress == right.compress

private def raw (expression : Expr) : Json := (Definograph.rawExprJson expression).toOption.getD .null

private def captureId := "12345678-1234-4234-8234-123456789abc"
private def selection : Selection := ⟨0, 1, 0, 1⟩

private def info (expression : Expr) (expectedType? : Option Expr := none) : MetaM (TermInfo × ContextInfo) := do
  let lctx ← getLCtx
  let env ← getEnv
  let mctx ← getMCtx
  let options ← getOptions
  let ngen := (← getThe Core.State).ngen
  let term : TermInfo := { elaborator := .anonymous, stx := .missing, lctx := lctx, expectedType? := expectedType?, expr := expression }
  let context : ContextInfo := { env, mctx, options, ngen, fileMap := default }
  return (term, context)

private def captureExpr (expression : Expr) (expectedType? : Option Expr := none) : MetaM Json := do
  let (term, context) ← info expression expectedType?
  capture term context captureId selection

def assignments : MetaM Unit := do
  let level ← mkFreshLevelMVar
  assignLevelMVar level.mvarId! (.succ .zero)
  withLocalDecl `same .implicit (.sort level) fun A =>
    withLocalDeclD `same A fun x => do
      let assigned ← mkFreshExprMVar A
      assigned.mvarId!.assign x
      withLetDecl `same A assigned fun _ =>
        withLetDecl `same A (.mdata ⟨[(`note, .ofString "retained")]⟩ assigned)
            (nondep := true) fun _ => do
          let (term, context) ← info assigned (some (.mdata ⟨[(`expected, .ofBool true)]⟩ A))
          let snapshot ← capture term context captureId selection
          require (same (field (field snapshot "expectedType") "expression") (raw term.expectedType?.get!))
            "expected type was instantiated or stripped"
          let original := field (field snapshot "original") "frame"
          let prepared := field (field snapshot "prepared") "frame"
          require (same (field original "sourceTerm") (raw assigned) &&
            same (field prepared "sourceTerm") (raw x)) "assigned expression did not retain original and prepared forms"
          let before := field original "originalDeclarations"
          let after := field prepared "originalDeclarations"
          require (!same (field (item before 0) "type") (field (item after 0) "type"))
            "assigned universe was not instantiated in the prepared local type"
          require (same (field (item before 2) "value") (raw assigned) &&
            same (field (item after 2) "value") (raw x)) "genuine defining value was not prepared"
          require (same (field (item before 3) "value") (field (item after 3) "value"))
            "ignored stored value was instantiated"
          for i in [0, 1, 2, 3] do
            for key in ["index", "fvarId", "userName", "kind", "nondep", "binderInfo"] do
              require (same (field (item before i) key) (field (item after i) key))
                "preparation changed declaration identity or annotations"
          let checking := field snapshot "checking"
          require (same (field checking "status") (toJson "captured") &&
            same (field (field checking "action") "status") (toJson "completed")) "prepared input was not captured"
          let checks := (field checking "checks").getArr?.toOption.getD #[]
          require (checks.size == 2 && checks.all fun c => same (field (field c "outcome") "tag") (toJson "accepted"))
            "assigned source did not receive two accepted checks"
          let binding := field checking "binding"
          require (same (field binding "sourceTerm") (field prepared "sourceTerm") &&
            same (field binding "sourceType") (field prepared "sourceType")) "binding differs from prepared frame"
          require (!(← getEnv).contains (declarationPrefix captureId ++ `context)) "capture leaked a diagnostic declaration"
          require (same snapshot (← capture term context captureId selection)) "repeating the same snapshot changed exact output"
  -- Inference precedes preparation: an assigned metavariable can have an
  -- annotated declared type different from re-inference of its assigned value.
  let annotated : Expr := .mdata ⟨[(`note, .ofString "declared type")]⟩ (mkConst ``Nat)
  let expression ← mkFreshExprMVar (some annotated)
  expression.mvarId!.assign (mkRawNatLit 0)
  let snapshot ← captureExpr expression
  require (same (field (field (field snapshot "original") "frame") "sourceType") (raw annotated) &&
    same (field (field (field snapshot "prepared") "frame") "sourceType") (raw annotated))
    "prepared type was re-inferred or metadata was erased"
  require (same (field (field snapshot "checking") "status") (toJson "unavailable"))
    "metadata in a semantic type crossed source admission"
  -- Inference of a forall body with an unknown type creates a universe and
  -- assigns that type. A second isolated inference must retain its own state.
  let body ← mkFreshExprMVar none
  let unresolved ← captureExpr (.forallE `x (mkConst ``Nat) body .default)
  require (same (field (field unresolved "original") "status") (toJson "available") &&
    same (field (field unresolved "prepared") "status") (toJson "available") &&
    same (field (field unresolved "checking") "status") (toJson "unavailable") &&
    same (field (field unresolved "checking") "attempted") (toJson true))
    "repeated inference lost newly allocated inference state"
  IO.println "PASS snapshot assignments: original identity, exact expectation, expression/universe assignments, genuine versus ignored values, inference-first type, checks and isolation"

def boundaries : MetaM Unit := do
  let expected := .mdata {} (mkConst ``Nat)
  let failed ← captureExpr (.fvar ⟨`notInContext⟩) (some expected)
  require (same (field (field failed "expectedType") "expression") (raw expected) &&
    same (field (field failed "original") "status") (toJson "unavailable") &&
    same (field (field failed "prepared") "status") (toJson "unavailable") &&
    same (field (field failed "checking") "attempted") (toJson false))
    "inference failure used the expected type as a fallback"
  let metadata ← captureExpr (.mdata {} (mkRawNatLit 0))
  require (same (field (field metadata "original") "status") (toJson "available") &&
    same (field (field metadata "prepared") "status") (toJson "available") &&
    same (field (field metadata "checking") "attempted") (toJson true))
    "raw metadata disappeared or was rejected before capture invocation"
  let placeholder ← mkSorry (mkConst ``Nat) false
  let refused ← captureExpr placeholder
  require (same (field (field refused "original") "status") (toJson "available") &&
    same (field (field refused "prepared") "status") (toJson "available") &&
    same (field (field refused "checking") "phase") (toJson "source-policy") &&
    same (field (field refused "checking") "attempted") (toJson false)) "sorry was promoted to finished-source checking"
  withLetDecl `ignored (mkConst ``Nat) placeholder (nondep := true) fun x => do
    let accepted ← captureExpr x
    require (same (field (field accepted "checking") "status") (toJson "captured"))
      "ignored placeholder metadata was treated as a semantic definition"
  let hugeText := String.ofList (List.replicate (130 * 1024) 'x')
  let limited ← captureExpr (.lit (.strVal hugeText))
  require (same (field (field limited "prepared") "kind") (toJson "limit") &&
    same (field (field limited "checking") "attempted") (toJson false))
    "unretainable prepared frame started checking"
  let assignedFunction ← mkFreshExprMVar (some (.forallE `text (mkConst ``String) (mkConst ``Nat) .default))
  assignedFunction.mvarId!.assign (.lam `text (mkConst ``String) (mkRawNatLit 0) .default)
  let shrunk ← captureExpr (.app assignedFunction (.lit (.strVal hugeText)))
  require (same (field (field shrunk "original") "kind") (toJson "limit") &&
    same (field (field shrunk "prepared") "status") (toJson "available") &&
    same (field (field shrunk "checking") "status") (toJson "captured"))
    "original serialization failure discarded an independently retainable prepared input"
  let mut context ← getLCtx
  for i in [:129] do context := context.mkLocalDecl ⟨.num `local i⟩ `same (mkConst ``Nat) .default
  withLCtx' context do
    let limited ← captureExpr (mkRawNatLit 0)
    require (same (field (field limited "prepared") "status") (toJson "available") &&
      same (field (field limited "checking") "phase") (toJson "context-policy") &&
      same (field (field limited "checking") "attempted") (toJson false)) "oversized context started semantic checking"
  IO.println "PASS snapshot boundaries: no inferred-type fallback, semantic metadata retained, placeholder policy, raw size/context limits and attempted-invocation distinction"

def parametersAndSerialization : MetaM Unit := do
  let u := Name.num `same 9007199254740993
  let v := Name.str `same "9007199254740993"
  let c := ({} : LocalContext).mkLocalDecl ⟨`A⟩ `same (.sort (.max (.param u) (.param v))) .default
    |>.mkLetDecl ⟨`opaque⟩ `same (.sort (.param v)) (.sort (.param `ignored)) true
  require (checkerUniverseParams c (.const `f [.param v, .param `term]) (.sort (.param `type)) ==
    [u, v, `term, `type]) "parameter collection reordered/merged names or read opaque metadata"
  let snapshot ← captureExpr (mkRawNatLit 0)
  let legacy := Json.mkObj [("ok", toJson true), ("diagnostics", Json.arr #[]), ("source", toJson "source")]
  let attached := legacy.setObjVal! "sourceSnapshot" snapshot
  let text := StatementLens.Context.serializeContextResponse attached
  let parsed ← match Json.parse text with | .ok value => pure value | .error reason => throwError "{reason}"
  require (same (field parsed "sourceSnapshot") snapshot) "serialization changed the exact attachment"
  let marker := ",\"sourceSnapshot\":"
  require (text.startsWith ((StatementLens.Response.serializeResponse legacy).dropEnd 1 |>.toString) &&
    (text.splitOn marker).length == 2) "legacy response bytes changed before attachment"
  let large := Json.mkObj [("ok", toJson true), ("diagnostics", Json.arr #[]),
    ("source", toJson (String.ofList (List.replicate (2100 * 1024) 'x'))), ("sourceSnapshot", snapshot)]
  let parsed ← match Json.parse (StatementLens.Context.serializeContextResponse large) with
    | .ok value => pure value | .error reason => throwError "{reason}"
  require (same (field parsed "ok") (toJson false) && same (field parsed "sourceSnapshot") snapshot)
    "oversized guided response discarded the source snapshot"
  require (validCaptureId captureId && !validCaptureId "invalid" && !validCaptureId (captureId ++ "x"))
    "capture UUID validation changed"
  IO.println "PASS snapshot parameters/transport: exact universe order and Name distinctions, unchanged legacy prefix, oversized-guided fallback retaining snapshot"

end StatementLens.SourceSnapshotControls

#eval StatementLens.SourceSnapshotControls.assignments
#eval StatementLens.SourceSnapshotControls.boundaries
#eval StatementLens.SourceSnapshotControls.parametersAndSerialization
