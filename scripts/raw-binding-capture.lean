import SourceCapture

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace RawBindingCorpus
open Lean Meta DerivedViewSyntax V6Structured V6Compose Definograph DefinographAdmission

private def policy : SourceCheckPolicy := {
  declarationPrefix := `RawBindingCorpus.checked
  heartbeatFor := fun _ => H
  retainedMetadata := .rawV1
}

private def metadata (word : String) : MData := ⟨[
  (`duplicate, .ofString "first"), (`duplicate, .ofString word),
  (`natural, .ofNat 9007199254740993), (`integer, .ofInt (.negSucc 18446744073709551616)),
  (`name, .ofName (.num `same 9007199254740993)), (`flag, .ofBool true),
  (`syntax, .ofSyntax (.ident (.synthetic ⟨9007199254740993⟩ ⟨0⟩ false)
    ⟨"α backing string", ⟨1⟩, ⟨999999999999999999999⟩⟩ `same
    [.namespace `same, .decl `same ["field", "field"]]))]⟩

private def record {α : Type} (label : String) (source : Except String (CapturedSource α)) : MetaM Json := do
  let captured ← match source with
    | .ok captured => pure captured
    | .error reason => throwError "unexpected unsupported corpus source: {reason}"
  let outcome := match captured.capture.value with
    | .ok _ => Json.mkObj [("kind", toJson "completed")]
    | .error message => Json.mkObj [("kind", toJson "actionError"), ("message", toJson message)]
  return Json.mkObj [("label", toJson label), ("binding", captured.binding),
    ("checks", Json.arr captured.capture.checks), ("audits", Json.arr captured.capture.audits),
    ("outcome", outcome), ("environmentSnapshotCount", toJson captured.capture.environments.size)]

def run : MetaM Unit := do
  let a : FVarId := ⟨.num `RawBindingCorpus.same 9007199254740992⟩
  let b : FVarId := ⟨.num `RawBindingCorpus.same 9007199254740993⟩
  let x : FVarId := ⟨.num `RawBindingCorpus.same 9007199254740994⟩
  let stored : Expr := .mdata (metadata "second") (.app (.fvar ⟨`unregistered⟩) (.sort (.mvar ⟨`unresolved⟩)))
  let context := (← getLCtx).mkLocalDecl a `same (mkConst ``Nat) .implicit
    |>.mkLetDecl b `same (mkConst ``Nat) (.fvar a) false
    |>.mkLetDecl x `same (mkConst ``Nat) stored true .implDetail
  let first ← withLCtx' context do
    record "schema3 opaque metadata original" (← captureNamedSource "raw-corpus" "opaque" policy (.fvar x) (mkConst ``Nat))
  let changed := context.modifyLocalDecl x (·.setValue (.mdata (metadata "changed") (.bvar 17)))
  let second ← withLCtx' changed do
    record "schema3 changed ignored value same semantic checks" (← captureNamedSource "raw-corpus" "opaque" policy (.fvar x) (mkConst ``Nat))
  let failedSelection ← withLCtx' context do
    record "schema3 failed extraction retains source receipts"
      (← captureNamedExtraction "raw-corpus" "extraction" policy (.fvar x) (mkConst ``Nat) [.appFun])
  let ordinary := context.modifyLocalDecl x (·.setValue (mkRawNatLit 0))
  let normalized ← withLCtx' ordinary do
    record "schema2 ordinary comparison" (← captureNamedSource "raw-corpus" "ordinary"
      { policy with retainedMetadata := .normalizedV2 } (.fvar x) (mkConst ``Nat))
  IO.println (Json.arr #[first, second, failedSelection, normalized]).compress

end RawBindingCorpus

#eval RawBindingCorpus.run
