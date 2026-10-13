import Lean

/-!
Axiom audit of compiled Lean modules.

Run by `scripts/axiom-audit.mjs` as

    lean --run scripts/axiom-audit.lean <policy.json> <import roots> <audited modules>

where the last two arguments are comma-separated module names. The program loads the compiled
modules from `LEAN_PATH`, never elaborates their sources, and prints one JSON object. It exits
with 0 when the policy holds, 1 when it is violated and 2 when the audit itself could not run.

For a constant `c`, "the axioms of `c`" are the axioms reachable from `c` through the constants
named in types and bodies. That is what `#print axioms` reports, and every theorem's result is
compared with `Lean.CollectAxioms.collect`. "The axioms of the statement of `c`" are the axioms
reachable from the constants named in the type of `c` alone, so they do not depend on its proof.
-/
open Lean

namespace AxiomAudit

structure Policy where
  /-- Axioms any audited constant may depend on. -/
  allowed : Array String
  /-- An axiom tolerated only under the theorems listed in `exceptions`. -/
  ratcheted : String
  /-- Theorem name and where the ratcheted axiom enters: `statement` or `proof`. -/
  exceptions : Array (String × String)
  /-- Theorem name and the exact axioms it must depend on. -/
  certificates : Array (String × Array String)
  expectedTheorems : Option Nat

def parsePolicy (text : String) : Except String Policy := do
  let json ← Json.parse text
  unless (← json.getObjValAs? Nat "schema") == 1 do throw "unsupported policy schema"
  let allowed ← json.getObjValAs? (Array String) "allowedAxioms"
  let ratcheted ← json.getObjValAs? String "ratchetedAxiom"
  let exceptions ← (← json.getObjValAs? (Array Json) "ratchetExceptions").mapM fun entry => do
    let kind ← entry.getObjValAs? String "kind"
    unless kind == "statement" || kind == "proof" do throw s!"unknown exception kind: {kind}"
    pure (← entry.getObjValAs? String "name", kind)
  let certificates ← (← json.getObjValAs? (Array Json) "certificates").mapM fun entry => do
    pure (← entry.getObjValAs? String "name", ← entry.getObjValAs? (Array String) "axioms")
  let expectedTheorems := (json.getObjValAs? Nat "expectedTheoremConstants").toOption
  pure { allowed, ratcheted, exceptions, certificates, expectedTheorems }

def typeDeps (info : ConstantInfo) : Array Name := info.type.getUsedConstants

def bodyDeps : ConstantInfo → Array Name
  | .defnInfo value => value.value.getUsedConstants
  | .thmInfo value => value.value.getUsedConstants
  | .opaqueInfo value => value.value.getUsedConstants
  | .inductInfo value => value.ctors.toArray
  | _ => #[]

/-- The edges `Lean.CollectAxioms.collect` follows. -/
def deps : ConstantInfo → Array Name
  | .quotInfo _ => #[]
  | info => typeDeps info ++ bodyDeps info

def reachableFrom (env : Environment) (start : Array Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut stack := start
  while !stack.isEmpty do
    let name := stack.back!
    stack := stack.pop
    if seen.contains name then continue
    seen := seen.insert name
    if let some info := env.find? name then
      for dependency in deps info do
        unless seen.contains dependency do stack := stack.push dependency
  return seen

def reverseEdges (env : Environment) (names : Std.HashSet Name) :
    Std.HashMap Name (Array Name) := Id.run do
  let mut reverse : Std.HashMap Name (Array Name) := {}
  for name in names do
    if let some info := env.find? name then
      for dependency in deps info do
        reverse := reverse.insert dependency ((reverse.getD dependency #[]).push name)
  return reverse

/-- Every constant from which `target` is reachable. -/
def dependentsOf (reverse : Std.HashMap Name (Array Name)) (target : Name) :
    Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut stack := #[target]
  while !stack.isEmpty do
    let name := stack.back!
    stack := stack.pop
    if seen.contains name then continue
    seen := seen.insert name
    for user in reverse.getD name #[] do
      unless seen.contains user do stack := stack.push user
  return seen

def sorted (names : Array String) : Array String := names.qsort (· < ·)

def strings (names : Array String) : Json := Json.arr (names.map Json.str)

def violation (rule name detail : String) : Json :=
  Json.mkObj [("rule", rule), ("name", name), ("detail", detail)]

def tally (counts : Std.HashMap String Nat) (key : String) : Std.HashMap String Nat :=
  counts.insert key (counts.getD key 0 + 1)

def tallyJson (counts : Std.HashMap String Nat) : Json :=
  Json.mkObj ((counts.toArray.qsort (fun a b => a.1 < b.1)).toList.map fun (key, n) => (key, toJson n))

def setKey (axioms : Array String) : String :=
  if axioms.isEmpty then "none" else " + ".intercalate axioms.toList

def audit (policy : Policy) (roots : Array Name) (auditedModules : Array String) : IO Json := do
  initSearchPath (← getBuildDir)
  let env ← importModules (roots.map fun module => { module }) {} (trustLevel := 0)
  let moduleNames := env.header.moduleNames
  let mut violations : Array Json := #[]
  let mut auditedIndexes : Std.HashSet Nat := {}
  for module in auditedModules do
    match moduleNames.findIdx? (·.toString == module) with
    | some index => auditedIndexes := auditedIndexes.insert index
    | none =>
      violations := violations.push
        (violation "module-missing" module "the audited module is not among the imported modules")
  let audited : Array (Name × ConstantInfo) := env.constants.fold (fun found name info =>
    match env.getModuleIdxFor? name with
    | some index => if auditedIndexes.contains index.toNat then found.push (name, info) else found
    | none => found) #[]
  let reachable := reachableFrom env (audited.map (·.1))
  let reverse := reverseEdges env reachable
  let mut axiomNames : Array Name := #[]
  for name in reachable do
    if let some (.axiomInfo _) := env.find? name then axiomNames := axiomNames.push name
  axiomNames := axiomNames.qsort (fun a b => a.toString < b.toString)
  let users := axiomNames.map fun name => (name.toString, dependentsOf reverse name)
  let axiomsOf (name : Name) : Array String :=
    users.filterMap fun (used, set) => if set.contains name then some used else none
  let statementAxiomsOf (info : ConstantInfo) : Array String :=
    let inType := typeDeps info
    users.filterMap fun (used, set) => if inType.any set.contains then some used else none
  let permitted (used : String) : Bool := policy.allowed.contains used || used == policy.ratcheted
  -- Rule: no audited module declares an axiom.
  let mut declared : Array String := #[]
  for (name, info) in audited do
    if let .axiomInfo _ := info then
      declared := declared.push name.toString
      violations := violations.push
        (violation "declared-axiom" name.toString "an audited module declares this axiom")
  -- Rule: no audited constant of any kind depends on an axiom outside the policy.
  for (name, info) in audited do
    if let .axiomInfo _ := info then continue
    let outside := (axiomsOf name).filter (!permitted ·)
    unless outside.isEmpty do
      violations := violations.push
        (violation "forbidden-axiom" name.toString (", ".intercalate outside.toList))
  -- Theorems: the ratchet, the counts and the cross-check against Lean's own collector.
  let mut theorems : Std.HashMap String (Array String) := {}
  let mut ratchetUsers : Array (String × String) := #[]
  let mut bySet : Std.HashMap String Nat := {}
  let mut byStatementSet : Std.HashMap String Nat := {}
  let mut addedByProof : Std.HashMap String Nat := {}
  let mut written := 0
  let mut writtenAddingNothing := 0
  for (name, info) in audited do
    let .thmInfo _ := info | continue
    let axioms := axiomsOf name
    let collected := (((CollectAxioms.collect name).run env).run {}).2.axioms
    let official := sorted (collected.map (·.toString))
    unless official == axioms do
      violations := violations.push (violation "collector-disagreement" name.toString
        s!"Lean.collectAxioms reports {official}; the audit computed {axioms}")
    let statement := statementAxiomsOf info
    let added := axioms.filter (!statement.contains ·)
    theorems := theorems.insert name.toString axioms
    bySet := tally bySet (setKey axioms)
    byStatementSet := tally byStatementSet (setKey statement)
    addedByProof := tally addedByProof (setKey added)
    if (declRangeExt.find? (level := .server) env name).isSome then
      written := written + 1
      if added.isEmpty then writtenAddingNothing := writtenAddingNothing + 1
    if axioms.contains policy.ratcheted then
      let kind := if statement.contains policy.ratcheted then "statement" else "proof"
      ratchetUsers := ratchetUsers.push (name.toString, kind)
      match policy.exceptions.find? (·.1 == name.toString) with
      | none =>
        violations := violations.push (violation "unlisted-ratcheted-axiom" name.toString
          s!"depends on {policy.ratcheted} through its {kind} and is not a listed exception")
      | some (_, listed) =>
        unless listed == kind do
          violations := violations.push (violation "exception-kind" name.toString
            s!"listed as {listed}; {policy.ratcheted} enters through the {kind}")
  for (name, _) in policy.exceptions do
    match theorems[name]? with
    | none =>
      violations := violations.push
        (violation "stale-exception" name "not a theorem of the audited modules; remove the entry")
    | some axioms =>
      unless axioms.contains policy.ratcheted do
        violations := violations.push (violation "stale-exception" name
          s!"no longer depends on {policy.ratcheted}; remove the entry")
  -- Rule: every certificate theorem exists and depends on exactly its recorded axioms.
  let mut certificates : Array Json := #[]
  for (name, recorded) in policy.certificates do
    let outside := recorded.filter (!policy.allowed.contains ·)
    unless outside.isEmpty do
      violations := violations.push (violation "certificate-policy" name
        s!"the recorded axioms include {outside}, which a certificate may not use")
    match theorems[name]? with
    | none =>
      violations := violations.push
        (violation "certificate-missing" name "not a theorem of the audited modules")
    | some axioms =>
      certificates := certificates.push (Json.mkObj [("name", name), ("axioms", strings axioms)])
      unless axioms == sorted recorded do
        violations := violations.push (violation "certificate-axioms" name
          s!"recorded {sorted recorded}; observed {axioms}")
  if let some expected := policy.expectedTheorems then
    unless theorems.size == expected do
      violations := violations.push (violation "theorem-count" "theorem constants"
        s!"expected {expected}; observed {theorems.size}")
  let ratchetSorted := ratchetUsers.qsort (fun a b => a.1 < b.1)
  return Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("ok", toJson violations.isEmpty),
    ("lean", Lean.versionString),
    ("auditedModules", strings auditedModules),
    ("counts", Json.mkObj [
      ("constants", toJson audited.size),
      ("theoremConstants", toJson theorems.size),
      ("writtenTheorems", toJson written),
      ("writtenTheoremsWhoseProofAddsNoAxiom", toJson writtenAddingNothing),
      ("ratchetedAxiomUsers", toJson ratchetUsers.size),
      ("byAxiomSet", tallyJson bySet),
      ("byStatementAxiomSet", tallyJson byStatementSet),
      ("byAxiomsAddedByProof", tallyJson addedByProof)]),
    ("reachableAxioms", strings (axiomNames.map (·.toString))),
    ("declaredAxioms", strings (sorted declared)),
    ("ratchetedAxiomUsers", Json.arr (ratchetSorted.map fun (name, kind) =>
      Json.mkObj [("name", name), ("kind", kind)])),
    ("certificates", Json.arr certificates),
    ("violations", Json.arr violations)]

end AxiomAudit

def main (args : List String) : IO UInt32 := do
  let [policyPath, roots, modules] := args
    | IO.eprintln "usage: lean --run axiom-audit.lean <policy.json> <import roots> <audited modules>"
      return 2
  let names (list : String) : Array String := ((list.splitOn ",").filter (· != "")).toArray
  let run : IO UInt32 := do
    match AxiomAudit.parsePolicy (← IO.FS.readFile policyPath) with
    | .error reason =>
      IO.eprintln s!"axiom audit: invalid policy: {reason}"
      return 2
    | .ok policy =>
      let report ← AxiomAudit.audit policy ((names roots).map String.toName) (names modules)
      IO.println report.compress
      return if (report.getObjValAs? Bool "ok").toOption == some true then 0 else 1
  try
    run
  catch error =>
    IO.eprintln s!"axiom audit: {error}"
    pure (2 : UInt32)
