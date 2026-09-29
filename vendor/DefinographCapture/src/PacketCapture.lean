import ExactJson
import CheckedComposition

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Definograph
open Lean Meta DerivedViewSyntax V6BinderShared V6Structured V6Compose
open ContextualViewDAG (Occ Args)

def outcomeJson : KOut → Json
  | .accepted => Json.mkObj [("tag", toJson "accepted")]
  | .notConvertible => Json.mkObj [("tag", toJson "rejected"), ("kind", toJson "notConvertible")]
  | .typeError k => Json.mkObj [("tag", toJson "rejected"), ("kind", toJson "typeError"), ("detail", toJson k)]
  | .unknown s => Json.mkObj [("tag", toJson "unknown"), ("message", toJson s)]

def formationJson : Formation → Json
  | .formed => Json.mkObj [("tag", toJson "formed")]
  | .unsupported s => Json.mkObj [("tag", toJson "unsupported"), ("reason", toJson s)]
  | .refused rs => Json.mkObj [("tag", toJson "refused"), ("reasons", toJson rs)]
  | .rejected c k => Json.mkObj [("tag", toJson "rejected"), ("check", toJson c), ("outcome", outcomeJson k)]
  | .unknown c s => Json.mkObj [("tag", toJson "unknown"), ("check", toJson c), ("message", toJson s)]

def evidenceJson : EvStatus → Json
  | .notFormed => Json.mkObj [("tag", toJson "notFormed")]
  | .missing => Json.mkObj [("tag", toJson "missing")]
  | .certified => Json.mkObj [("tag", toJson "certified")]
  | .rejected c k => Json.mkObj [("tag", toJson "rejected"), ("check", toJson c), ("outcome", outcomeJson k)]
  | .unknown c s => Json.mkObj [("tag", toJson "unknown"), ("check", toJson c), ("message", toJson s)]

def reportJson (r : Report) : Json := Json.mkObj
  [("formation", formationJson r.formation), ("evidence", evidenceJson r.evidence),
   ("checks", .arr (r.checks.map fun (label, k) => Json.mkObj [("label", toJson label), ("outcome", outcomeJson k)]))]

structure CheckReceipt where
  id : Nat
  pair : String
  displayLabel : String
  declaration : Json
  before : Nat
  after : Nat
  heartbeatBound : Nat
  outcome : KOut

structure Capture where
  checks : Array CheckReceipt := #[]
  audits : Array Json := #[]
  environments : Array Environment := #[]

def Capture.envId (s : Capture) : Nat := s.environments.size - 1

def declName : Declaration → Name
  | .thmDecl d => d.name
  | .defnDecl d => d.name
  | _ => .anonymous

def auditCategory (label : String) : String :=
  if label.startsWith "certificate" then "derivedProofCheck"
  else if label.startsWith "F.evidence" || label.startsWith "G.evidence" then "suppliedProofCheck"
  else if label.startsWith "F.route" || label.startsWith "G.route" then "routeCertificate"
  else if label.endsWith "is a proposition" then "statementFormation"
  else if label.contains '=' then "conversion"
  else "interfaceFormation"

/-- Existing declarations are audited separately in the initial environment.
These are declaration dependency audits, not new evidence certifications. -/
def auditSource (state : IO.Ref Capture) (category pair slot : String) (name : Name) : MetaM Unit := do
  let info ← getConstInfo name
  let d ← match info with
    | .thmInfo val => pure (Declaration.thmDecl val)
    | .defnInfo val => pure (Declaration.defnDecl val)
    | _ => throwError "source declaration is outside the captured profile: {name}"
  let exact ← match declarationJson d with
    | .ok j => pure j
    | .error e => throwError "source {name}: {e}"
  let axioms ← collectAxioms name
  let audit := Json.mkObj [("checkId", .null), ("subject", exact), ("environment", toJson (0 : Nat)),
    ("category", toJson category), ("association", Json.mkObj [("pair", toJson pair), ("slot", toJson slot)]),
    ("result", Json.mkObj [("tag", toJson "available"), ("axioms", arr (axioms.toList.map nameJson))])]
  state.modify fun s => { s with audits := s.audits.push audit }

def auditInputSources (state : IO.Ref Capture) (pair slot : String) (b : Bank) {m : Nat}
    (p : MapIn b.homes m) : MetaM Unit := do
  if let some (_, o) := p.ev then
    match (dec (ev b.table o)).getAppFn with
    | .const name _ => auditSource state "existingSuppliedProof" pair slot name
    | _ => throwError "supplied proof is outside the fixed constant-headed source profile"
  for j in List.finRange 6 do
    match (p.certs j).base with
    | .exact => pure ()
    | .classB name _ _ => auditSource state "existingRouteCertificate" pair s!"{slot}.route{j.val}" name

/-- Serialization precedes the real kernel call. Accepted environments are retained
as immutable snapshots; rejected and unknown calls keep the same environment. -/
def capturedCheck (state : IO.Ref Capture) (tl : TRef) (pair label : String)
    (hb : Nat) (d : Declaration) : MetaM KOut := do
  if hb == 0 || hb >= USize.size then
    throwError "kernel heartbeat bound must be positive and fit in USize"
  let exact ← match declarationJson d with
    | .ok j => pure j
    | .error e => throwError "{e}"
  let s ← state.get
  let id := s.checks.size
  let before := s.envId
  let k ← kDecide tl hb d
  let after := before + if kAccepted k then 1 else 0
  if kAccepted k then
    let current ← getEnv
    state.modify fun s => { s with environments := s.environments.push current }
  let audit ← if kAccepted k then do
    let names ← collectAxioms (declName d)
    pure (Json.mkObj [("tag", toJson "available"), ("axioms", arr (names.toList.map nameJson))])
  else pure (Json.mkObj [("tag", toJson "unavailable"), ("reason", toJson "declaration was not installed")])
  state.modify fun s => { s with
    checks := s.checks.push ⟨id, pair, label, exact, before, after, hb, k⟩
    audits := s.audits.push (Json.mkObj [("checkId", toJson id), ("subject", exact),
      ("environment", toJson after), ("category", toJson (auditCategory label)), ("result", audit)]) }
  return k

def receiptJson (attempt reportLabel : String) (c : CheckReceipt) : Json := Json.mkObj
  [("id", toJson c.id), ("pair", toJson c.pair), ("label", toJson reportLabel),
   ("displayLabel", toJson c.displayLabel), ("declaration", c.declaration),
   ("subject", Json.mkObj [("attempt", toJson attempt), ("pair", toJson c.pair),
     ("sequence", toJson c.id), ("target", toJson c.displayLabel), ("declaration", c.declaration)]),
   ("envBefore", toJson c.before), ("envAfter", toJson c.after),
   ("heartbeatBound", exactNatJson c.heartbeatBound), ("outcome", outcomeJson c.outcome)]

/-- The caller's typed return value and the declarations actually submitted through
the capture callback. This structure carries no admission or authenticity flag. -/
structure CapturedChecks (α : Type) where
  value : α
  checks : Array Json
  audits : Array Json
  environments : Array Environment

/-- Run a caller-defined sequence of declaration checks in an isolated environment
chain. Each callback starts from the initial caller environment extended only by
earlier accepted callback declarations; other environment changes made by `action`
are not included in that chain. Receipts retain the actual submitted declaration,
label, kernel outcome and bounded resource policy. The exact serializer accepts
theorem/definition declarations; other declaration kinds fail explicitly. Generic
audits use `declarationCheck` without inferring a mathematical role from a label.

The caller's environment and metavariable state are restored on success or failure.
The callback is inactive after this function returns, even if `action` returns it.
The action's return value and other effects are not certified: in particular, zero
checks do not establish admission, and neither the initial environment's source
validity nor the semantics of an admission/extraction action are established here. -/
def captureChecks {α : Type} (attempt operation : String)
    (heartbeatFor : String → Nat)
    (action : (String → Declaration → MetaM KOut) → MetaM α) : MetaM (CapturedChecks α) := do
  if attempt.isEmpty || operation.isEmpty then
    throwError "attempt and operation identifiers must be nonempty"
  let saved ← Meta.saveState
  let active ← IO.mkRef true
  try
    let state ← IO.mkRef ({ environments := #[← getEnv] } : Capture)
    let tally ← IO.mkRef ({} : Tally)
    let check (label : String) (declaration : Declaration) : MetaM KOut := do
      unless ← active.get do throwError "capture callback is no longer active"
      if label.isEmpty then throwError "check display label must be nonempty"
      let some environment := (← state.get).environments.back?
        | throwError "capture environment chain is empty"
      setEnv environment
      capturedCheck state tally operation label (heartbeatFor label) declaration
    let value ← action check
    let captured ← state.get
    return {
      value := value
      checks := captured.checks.map fun receipt => receiptJson attempt receipt.displayLabel receipt
      audits := captured.audits.map fun audit =>
        audit.setObjVal! "category" (toJson "declarationCheck")
      environments := captured.environments
    }
  finally
    active.set false
    saved.restore

def candidateJson {b : Bank} (k : Comp b) : Json := Json.mkObj
  [("m", toJson k.m), ("ctx", ownerJson k.ctx), ("F", inputJson k.F), ("G", inputJson k.G),
   ("sigma", argsJson k.σ), ("ev", match k.ev with | none => .null | some c => certUJson c),
   ("construction", toJson "compose / mkComp")]

def selectedJson (pair role : String) (r : SRec) (ls : Nat → Option (List ULevel)) : List Json :=
  r.body.uses.map fun u => Json.mkObj
    [("pair", toJson pair), ("role", toJson role), ("oid", exactNatJson u.use.oid),
     ("path", pathJson u.path), ("entry", entryJson u),
     ("sourceLevels", levelsJson u.use.srcCert (ls u.use.oid)),
     ("viewLevels", levelsJson u.use.viewCert (ls u.use.oid))]

/-- Explicit caller-owned checking policy. No fixture name or UI state is consulted. -/
structure PairCheckPolicy where
  declarationPrefix : Name
  universeParams : List Name := []
  heartbeatFor : String → Nat

def runPairWith (state : IO.Ref Capture) (tl : TRef) (policy : PairCheckPolicy) (pair : String)
    (b : Bank) {m : Nat} (ctx : OTel b.homes m) (f g : MapIn b.homes m) : MetaM (Json × List Json × Report) := do
  match compose b ctx f g with
  | none =>
    let reasons := ((midReasons b ctx f g).filter fun p => !p.2).map (·.1)
    let report : Report := ⟨.refused reasons, .notFormed, #[]⟩
    return (Json.mkObj [("id", toJson pair), ("candidate", .null), ("report", reportJson report),
      ("records", Json.mkObj [("retained", .null), ("derived", .null)])], [], report)
  | some k =>
    let report ← checkFormedWith (fun label d => capturedCheck state tl pair label (policy.heartbeatFor label) d)
      policy.declarationPrefix policy.universeParams b k
    let retained := k.lawsIn
    let derived := k.law
    -- This construction only installs source certificates. A future extension
    -- must give view certificates their own universe association.
    for r in [retained, derived] do
      for u in r.body.uses do
        match u.use.viewCert with
        | .exact => pure ()
        | .classB .. => throwError "class B view certificate is outside the worker profile"
    let ls (oid : Nat) := if oid == 0 || oid == 1 then some (k.useLvls oid) else none
    let result := Json.mkObj [("id", toJson pair), ("candidate", candidateJson k), ("report", reportJson report),
      ("records", Json.mkObj [("retained", recordJson retained ls), ("derived", recordJson derived (fun _ => none))])]
    return (result, selectedJson pair "retained" retained ls ++ selectedJson pair "derived" derived (fun _ => none), report)

/-- A local Lean result. Its JSON fields are exact captured data, not a signed receipt
or a browser trust token. Environment snapshots belong to this call only. -/
structure CapturedPair where
  result : Json
  uses : List Json
  report : Report
  checks : Array Json
  audits : Array Json
  environments : Array Environment

/-- Check already represented components in the caller's current Lean environment.
The caller supplies the actual typed bank/context/components and is responsible for
source admission; this function neither elaborates source strings nor infers them
from names. It restores Lean's environment and metavariable state even on failure.
Generated declarations remain available only in the returned environment snapshots.
No joint law, arbitrary dependent source typing, or producer authenticity is inferred. -/
def capturePair (attempt pair : String) (policy : PairCheckPolicy)
    (b : Bank) {m : Nat} (ctx : OTel b.homes m) (f g : MapIn b.homes m) : MetaM CapturedPair := do
  if attempt.isEmpty || pair.isEmpty || policy.declarationPrefix == .anonymous then
    throwError "attempt, pair and declaration prefix must be nonempty"
  let saved ← Meta.saveState
  try
    let state ← IO.mkRef ({ environments := #[← getEnv] } : Capture)
    let tally ← IO.mkRef ({} : Tally)
    let (result, uses, report) ← runPairWith state tally policy pair b ctx f g
    let captured ← state.get
    unless captured.checks.size == report.checks.size do
      throwError "receipt/report length mismatch"
    let checks := captured.checks.mapIdx fun i receipt =>
      receiptJson attempt report.checks[i]!.1 receipt
    return {
      result := result
      uses := uses
      report := report
      checks := checks
      audits := captured.audits
      environments := captured.environments
    }
  finally
    saved.restore

end Definograph
