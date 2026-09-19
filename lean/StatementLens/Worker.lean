import Lean

/- StatementLens never loads source files supplied by clients. The only user-controlled
   input is parsed as one term, checked against a closed syntax allowlist, elaborated
   as Prop, and independently checked by Lean's kernel. No declaration is added. -/
open Lean Meta Elab Term

namespace StatementLens

def imports : Array Import := #[
  { module := `Mathlib.Topology.MetricSpace.Basic },
  { module := `Mathlib.Analysis.InnerProductSpace.PiL2 }
]

def obj := Json.mkObj
def str := Json.str

def permittedSyntax : Array Name := #[
  `null, `group, `hygieneInfo, `num, `fieldIdx,
  `Lean.Parser.Term.forall, `Lean.Parser.Term.explicitBinder,
  `Lean.Parser.Term.type, `Lean.Parser.Term.sort, `Lean.Parser.Term.prop,
  `Lean.Parser.Level.paren, `Lean.Parser.Level.max, `Lean.Parser.Level.imax, `Lean.Parser.Level.addLit,
  `Lean.Parser.Term.implicitBinder, `Lean.Parser.Term.strictImplicitBinder,
  `Lean.Parser.Term.instBinder, `Lean.Parser.Term.typeSpec,
  `Lean.Parser.Term.arrow, `Lean.Parser.Term.app, `Lean.Parser.Term.paren,
  `Lean.Parser.Term.hygienicLParen, `Lean.Parser.Term.typeAscription,
  `Lean.Parser.Term.fun, `Lean.Parser.Term.basicFun, `Lean.Parser.Term.proj,
  `Lean.Parser.Term.explicit, `Lean.Parser.Term.anonymousCtor, `Lean.Parser.Term.tuple,
  `Lean.explicitBinders, `Lean.unbracketedExplicitBinders, `Lean.binderIdent,
  `Lean.«term∀__,_», `Lean.«term∃__,_»,
  `Lean.«binderPred>_», `Lean.«binderPred≥_», `Lean.«binderPred<_», `Lean.«binderPred≤_»,
  `Lean.«binderPred≠_», `Lean.«binderPred∈_», `Lean.«binderPred∉_»,
  `termℝ, `termℕ, `termℤ, `termℚ,
  `«term_×_», `«term_∈_», `«term_∉_», `«term_<_», `«term_>_»,
  `«term_≤_», `«term_≥_», `«term_=_», `«term_≠_»,
  `«term_∧_», `«term_∨_», `«term_↔_», `«term¬_», `«term∃_,_»,
  `«term_+_», `«term_-_», `«term_*_», `«term_/_», `«term_^_»,
  `«term-_», `«term|___|»,
  `«term_∘_», `«term_⊆_», `«term_⊂_», `«term_∪_», `«term_∩_»,
  `«term_\_», `«term_ᶜ», `«term∅», `Mathlib.Meta.setBuilder,
  `Batteries.ExtendedBinder.extBinder
]

partial def validateSyntax (stx : Syntax) (depth : Nat := 0) : Except String Unit := do
  if depth > 128 then throw "Statement nesting exceeds the supported depth (128)."
  match stx with
  | .node _ kind args =>
    if kind == `Lean.Parser.Term.hole then throw "Placeholders are not accepted; provide an explicit mathematical term."
    unless permittedSyntax.contains kind do
      throw s!"Unsupported Lean term syntax: {kind}. Only declarative mathematical terms are accepted; tactics, commands, quotations, and custom elaboration are disabled."
    for arg in args do validateSyntax arg (depth + 1)
  | .ident _ _ name _ =>
    if name == `sorryAx || name == `sorry || name == `admit then
      throw "Placeholders and sorry are not accepted."
  | .missing => throw "Incomplete syntax."
  | _ => pure ()

structure Bound where
  fvar : FVarId
  id : String
  name : String
  type : String
  role : String

abbrev Bounds := Array Bound

def pp (e : Expr) : MetaM String := return (← ppExpr e).pretty

def realType : Expr := mkConst `Real

/-- Display names are never identities; imported macro scopes remain internal. -/
def binderName (name : Name) : String := name.eraseMacroScopes.toString

/-- Numerical classification is independent of the general typed object descriptor. -/
def domain (t : Expr) : MetaM (String × Nat) := do
  if ← isDefEq t realType then return ("real", 1)
  if ← isDefEq t (mkApp2 (mkConst `Prod [levelZero, levelZero]) realType realType) then
    return ("sup2", 2)
  if ← isDefEq t (← mkArrow realType realType) then return ("realFunction", 1)
  -- Inspect the typed dimension directly rather than enumerating a small menu.
  let head := t.getAppFn.constName?.getD .anonymous
  let args := t.getAppArgs
  if head == `EuclideanSpace && args.size == 2 then
    let index := args[1]!
    if index.isAppOfArity `Fin 1 then
      if let some n := index.appArg!.nat? then
        if ← isDefEq args[0]! realType then
          return (if n == 2 then "euclidean2" else "euclideanN", n)
  if let .forallE _ a b _ := t then
    if a.isAppOfArity `Fin 1 && !b.hasLooseBVars then
      if let some n := a.appArg!.nat? then
        if ← isDefEq b realType then return (if n == 2 then "sup2" else "supN", n)
  return ("unknown", 0)

def returnsProp : Expr → Bool
  | .forallE _ _ body _ => returnsProp body
  | .sort .zero => true
  | _ => false

/-- A finite, structural description of any typed object. Unknown constants remain
    named structures; there is no theorem-name dictionary and no geometric guess. -/
partial def describeType (t : Expr) (depth : Nat := 0) : MetaM Json := do
  let t := t.consumeMData
  let pretty ← pp t
  let head := t.getAppFn.constName?.getD .anonymous
  let args := t.getAppArgs
  let base (kind : String) (more : List (String × Json) := []) :=
    obj ([("kind", str kind), ("lean", str pretty)] ++
      (if head.isAnonymous then [] else [("head", str head.toString)]) ++ more)
  if depth > 6 then return base "unknown"
  if t.isSort then return base (if t == mkSort levelZero then "proposition" else "type")
  if head == `Real then return base "real"
  if head == `Nat then return base "natural"
  if head == `Int then return base "integer"
  if head == `Rat then return base "rational"
  if head == `Fin && args.size == 1 then
    return base "finite" (match args[0]!.nat? with | some n => [("cardinality", toJson n)] | none => [])
  if head == `Set && args.size == 1 then
    return base "set" [("element", ← describeType args[0]! (depth + 1))]
  if let .forallE name a b bi := t then
    return ← withLocalDecl name bi a fun x => do
      let body := b.instantiate1 x
      let kind := if returnsProp b then "relation" else "map"
      return base kind [("domain", ← describeType a (depth + 1)),
        ("codomain", ← describeType body (depth + 1)), ("dependent", toJson b.hasLooseBVars)]
  if ← isProp t then return base "proposition"
  let (d, n) ← domain t
  if d != "unknown" then return base "structure" [("dimension", toJson n), ("numericalDomain", str d)]
  return base (if head.isAnonymous then "unknown" else "structure")

def binderJson (b : Bound) (t : Expr) (bs : Bounds) : MetaM Json := do
  let (d, n) ← domain t
  return obj [
    ("id", str b.id), ("name", str b.name), ("type", str b.type),
    ("role", str b.role), ("domain", str d), ("dimension", toJson n),
    ("typeDescriptor", ← describeType t),
    ("dependsOn", toJson ((bs.filter (·.role != "assumption")).map (·.id))) ]

/-- Audit class arguments against canonical imported instances. Parametric set
    instance constructors are recognized structurally; numerical instances are
    synthesized in an empty local context, excluding local replacements. -/
def standardInstances (e : Expr) : MetaM Bool := do
  try
    for a in e.getAppArgs do
      let ty ← inferType a
      if (← isClass? ty).isSome then
        -- Set operations are parametric in their element type. These exact imported
        -- instance constructors have fixed membership/lattice meanings even when
        -- the element type is a local variable. Local or replacement instances do
        -- not have one of these constructor heads and still fail the audit.
        let setInstances := #[`Set.instMembership, `Set.instHasSubset, `Set.instHasSSubset,
          `Set.instInter, `Set.instUnion, `Set.instCompl, `Set.instSDiff, `Set.instEmptyCollection]
        if setInstances.contains (a.getAppFn.constName?.getD .anonymous) && a.getAppArgs.size == 1 then
          continue
        if ty.hasFVar || ty.hasMVar then return false
        let expected ← withLCtx {} {} <| synthInstance ty
        unless ← isDefEq a expected do return false
    return true
  catch _ => return false

partial def encode (e : Expr) (bs : Bounds) (path : String) (depth : Nat := 0) : MetaM Json := do
  if depth > 80 then return obj [("kind", str "opaque"), ("text", str "Expression depth limit")]
  let e := e.consumeMData
  match e with
  | .const name _ => return obj [("kind", str "const"), ("name", str name.toString),
      ("type", str (← pp (← inferType e))), ("typeDescriptor", ← describeType (← inferType e))]
  | .fvar id =>
    if let some b := bs.find? (·.fvar == id) then
      return obj [("kind", str "var"), ("id", str b.id), ("name", str b.name), ("type", str b.type), ("typeDescriptor", ← describeType (← inferType e))]
    return obj [("kind", str "opaque"), ("text", str (← pp e))]
  | .lit (.natVal n) => return obj [("kind", str "literal"), ("value", toJson n)]
  | .lit (.strVal s) => return obj [("kind", str "literal"), ("value", str s)]
  | .sort l => return obj [("kind", str "sort"), ("name", str (toString l))]
  | .forallE name ty body bi | .lam name ty body bi =>
    let kind := if e.isLambda then "lambda" else "forall"
    let prop ← isProp ty
    withLocalDecl name bi ty fun x => do
      let b : Bound := ⟨x.fvarId!, path ++ ".binder", binderName name, ← pp ty, if e.isLambda then "lambda" else if prop then "assumption" else "universal"⟩
      return obj [("kind", str kind), ("binder", ← binderJson b ty bs),
        ("binderType", ← encode ty bs (path ++ ".type") (depth + 1)),
        ("body", ← encode (body.instantiate1 x) (bs.push b) (path ++ ".body") (depth + 1))]
  | .app .. =>
    let args := e.getAppArgs
    let name := e.getAppFn.constName?.getD .anonymous
    let mut encoded := #[]
    let mut argumentKinds : Array String := #[]
    for i in [:args.size] do
      let a := args[i]!
      let aType ← inferType a
      let isInst := (← isClass? aType).isSome
      let isProof ← isProp aType
      let isType := (← whnf aType).isSort
      argumentKinds := argumentKinds.push (if isInst then "instance" else if isProof then "proof" else if isType then "type" else "value")
      if (← isClass? aType).isSome then
        encoded := encoded.push (obj [("kind", str "opaque"), ("text", str (← pp a))])
      else
        encoded := encoded.push (← encode a bs s!"{path}.{i}" (depth + 1))
    let std ← standardInstances e
    let ty ← inferType e
    let (d, n) ← domain ty
    let mut fields := [
      ("kind", str "app"), ("fn", ← encode e.getAppFn bs (path ++ ".fn") (depth + 1)),
      ("args", Json.arr encoded), ("argumentKinds", toJson argumentKinds), ("standard", toJson std), ("type", str (← pp ty)),
      ("typeDescriptor", ← describeType ty),
      ("dimension", toJson n), ("domain", str d)]
    if #[`Metric.ball, `Metric.closedBall, `Metric.sphere, `Dist.dist, `dist].contains name then
      let (metric, dim) ← if args.size > 0 then domain args[0]! else pure ("unknown", 0)
      fields := fields ++ [("metric", str (if std then metric else "unknown")),
        ("dimension", toJson dim), ("metricInstance", str (← if args.size > 1 then pp args[1]! else pure "unknown"))]
    return obj fields
  | .proj name index value =>
    return obj [("kind", str "app"), ("fn", obj [("kind", str "const"), ("name", str (if name == `Prod then (if index == 0 then "Prod.fst" else "Prod.snd") else s!"{name}.proj{index}"))]),
      ("args", Json.arr #[← encode value bs (path ++ ".value") (depth + 1)]), ("standard", toJson true), ("type", str (← pp (← inferType e)))]
  | .letE _ _ value body _ => encode (body.instantiate1 value) bs path (depth + 1)
  | _ => return obj [("kind", str "opaque"), ("text", str (← pp e))]

def node (id kind label lean : String) (children : Array Json) (expression : Json) (binder : Option Json := none) : Json :=
  obj ([("id", str id), ("kind", str kind), ("label", str label), ("lean", str lean),
    ("children", Json.arr children), ("expression", expression)] ++
    (match binder with | some b => [("binder", b)] | none => []))

def expressionOf (j : Json) : Json := (j.getObjVal? "expression").toOption.getD Json.null

structure ExportPolicy where
  constants : Array Name := #[]
  maxDepth : Nat := 2

def declarationKind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

def declarationJson (info : ConstantInfo) : MetaM Json := do
  let env ← getEnv
  let moduleName := (env.getModuleIdxFor? info.name).bind fun idx => env.allImportedModuleNames[idx.toNat]?
  return obj [("name", str info.name.toString), ("kind", str (declarationKind info)),
    ("type", str (← pp info.type)), ("module", moduleName.map (str ∘ Name.toString) |>.getD Json.null),
    ("canExpand", toJson (info.isDefinition && !info.isUnsafe && !info.isPartial)),
    ("universeParameters", toJson (info.levelParams.map Name.toString))]

def readPolicy (request : Json) : MetaM ExportPolicy := do
  let some j := (request.getObjVal? "expansion").toOption | return {}
  let names ← match j.getObjValAs? (Array String) "constants" with
    | .ok ns => pure ns
    | .error _ => throwError "expansion.constants must be an array of exact imported definition names."
  if names.size > 12 then throwError "At most 12 definitions may be selected for expansion."
  let maxDepth ← match j.getObjValAs? Nat "maxDepth" with
    | .ok n => pure n
    | .error _ =>
      if (j.getObjVal? "maxDepth").isOk then throwError "expansion.maxDepth must be an integer." else pure 2
  if maxDepth < 1 || maxDepth > 3 then throwError "Definition expansion depth must be between 1 and 3."
  let mut constants := #[]
  for name in names do
    if name.isEmpty || name.utf8ByteSize > 512 then throwError "Definition names must contain between 1 and 512 bytes."
    let n := name.toName
    let some info := (← getEnv).find? n | throwError "Unknown imported definition: {name}"
    unless info.isDefinition && !info.isUnsafe && !info.isPartial do
      throwError "Only safe imported definitions may be expanded: {name}"
    constants := constants.push n
  return { constants, maxDepth }

partial def tree (e : Expr) (bs : Bounds := #[]) (path : String := "n")
    (policy : ExportPolicy := {}) (expansionDepth : Nat := 0) (depth : Nat := 0) : MetaM Json := do
  if depth > 80 then throwError "Logical structure exceeds export depth (80)."
  let e := e.consumeMData
  let pretty ← pp e
  let finish (j : Json) := j.setObjVal! "scope" (toJson (bs.map (·.id)))
  let head := e.getAppFn.constName?.getD .anonymous
  if policy.constants.contains head && expansionDepth < policy.maxDepth then
    if let some expanded ← unfoldDefinition? e (ignoreTransparency := true) then
      unless expanded == e do
        checkWithKernel expanded
        unless ← isDefEq e expanded do throwError "Definition expansion did not preserve definitional equality."
        let result ← tree expanded bs path policy (expansionDepth + 1) (depth + 1)
        return finish <| result.setObjVal! "expansion" (obj [
          ("constant", str head.toString), ("before", str pretty), ("after", str (← pp expanded)),
          ("originalExpression", ← encode e bs path), ("definitionalEquality", toJson true),
          ("depth", toJson (expansionDepth + 1))])
  match e with
  | .lam name ty body bi =>
    withLocalDecl name bi ty fun x => do
      let b : Bound := ⟨x.fvarId!, path ++ ".binder", binderName name, ← pp ty, "parameter"⟩
      let bj ← binderJson b ty bs
      let child ← tree (body.instantiate1 x) (bs.push b) (path ++ ".body") policy expansionDepth (depth + 1)
      let expression := obj [("kind", str "lambda"), ("binder", bj),
        ("binderType", ← encode ty bs (path ++ ".type")), ("body", expressionOf child)]
      return finish <| node path "parameter" s!"Parameter {binderName name}" pretty #[child] expression (some bj)
  | .forallE name ty body bi =>
    let prop ← isProp ty
    let statement ← isProp e
    let kind := if !statement then "parameter" else if prop then "implies" else "forall"
    withLocalDecl name bi ty fun x => do
      let b : Bound := ⟨x.fvarId!, path ++ ".binder", binderName name, ← pp ty,
        if !statement then "parameter" else if prop then "assumption" else "universal"⟩
      let bj ← binderJson b ty bs
      let child ← tree (body.instantiate1 x) (bs.push b) (path ++ ".body") policy expansionDepth (depth + 1)
      let children ← if prop && statement then pure #[← tree ty bs (path ++ ".premise") policy expansionDepth (depth + 1), child] else pure #[child]
      let expression := obj [("kind", str "forall"), ("binder", bj), ("binderType", ← encode ty bs (path ++ ".type")), ("body", expressionOf child)]
      return finish <| node path kind (if !statement then s!"Parameter {binderName name}" else if prop then "If … then …" else s!"For every {binderName name}") pretty children expression (some bj)
  | _ =>
    let args := e.getAppArgs
    let head := e.getAppFn.constName?.getD .anonymous
    if head == `Exists && args.size == 2 then
      let p ← whnf args[1]!
      if let .lam name ty body bi := p then
        return ← withLocalDecl name bi ty fun x => do
          let b : Bound := ⟨x.fvarId!, path ++ ".binder", binderName name, ← pp ty, "existential"⟩
          let bj ← binderJson b ty bs
          let child ← tree (body.instantiate1 x) (bs.push b) (path ++ ".body") policy expansionDepth (depth + 1)
          let expr := obj [("kind", str "app"), ("fn", obj [("kind", str "const"), ("name", str "Exists")]),
            ("args", Json.arr #[← encode ty bs (path ++ ".type"), obj [("kind", str "lambda"), ("binder", bj), ("binderType", ← encode ty bs (path ++ ".type")), ("body", expressionOf child)]])]
          return finish <| node path "exists" s!"There exists {binderName name}" pretty #[child] expr (some bj)
    let logical := if head == `And then some ("and", "Both conditions") else if head == `Or then some ("or", "At least one condition") else if head == `Iff then some ("iff", "Equivalent conditions") else if head == `Not then some ("not", "Not") else none
    if let some (kind, label) := logical then
      let mut children := #[]
      for i in [:args.size] do children := children.push (← tree args[i]! bs s!"{path}.{i}" policy expansionDepth (depth + 1))
      let expr := obj [("kind", str "app"), ("fn", obj [("kind", str "const"), ("name", str head.toString)]),
        ("args", Json.arr (children.map expressionOf))]
      return finish <| node path kind label pretty children expr
    return finish <| node path "predicate" pretty pretty #[] (← encode e bs path)

/-- InfoTree coordinates are UTF-8 byte offsets, not JavaScript character indices.
    They are independent typed occurrences, never guessed matches to transformed nodes. -/
partial def sourceTerms (infoTree : InfoTree) (out : Array Json := #[]) : MetaM (Array Json) := do
  if out.size >= 512 then return out
  match infoTree with
  | .context _ child => sourceTerms child out
  | .hole _ => return out
  | .node info children =>
    let mut out := out
    if let .ofTermInfo term := info then
      if let some range := term.stx.getRange? (canonicalOnly := true) then
        try
          let entry ← withLCtx term.lctx {} do
            let e ← instantiateMVars term.expr
            if e.hasMVar || e.hasSorry then return Json.null
            return obj [("startByte", toJson range.start.byteIdx), ("endByte", toJson range.stop.byteIdx),
              ("lean", str (← pp e)), ("type", str (← pp (← inferType e))),
              ("isBinder", toJson term.isBinder), ("origin", str "lean-infotree")]
          if entry != Json.null && !out.contains entry then out := out.push entry
        catch _ => pure ()
    for child in children do out ← sourceTerms child out
    return out

def analyze (source : String) (request : Json) : TermElabM Json := withoutErrToSorry do
  let env ← getEnv
  let policy ← readPolicy request
  let inputMode ← match request.getObjValAs? String "inputMode" with
    | .ok mode => pure mode
    | .error _ => if (request.getObjVal? "inputMode").isOk then throwError "inputMode must be a string." else pure "term"
  unless inputMode == "term" || inputMode == "declaration" do throwError "inputMode must be term or declaration."
  let stx ← match Parser.runParserCategory env `term source "<statement>" with
    | .ok s => pure s
    | .error err => throwError "{err}"
  let mut declaration := Json.null
  let mut definitionExpression := Json.null
  let mut definitionTree := Json.null
  let mut definitionBodyStatus := "not-a-definition"
  let mut inspected := "statement"
  let expression ← if inputMode == "declaration" then do
      unless stx.isIdent do throwError "Declaration mode expects one exact imported declaration name."
      let name := stx.getId
      let some info := env.find? name | throwError "Unknown imported declaration: {name}"
      if info.isUnsafe || info.isPartial then throwError "Unsafe and partial declarations are not inspected."
      declaration ← declarationJson info
      if info.isDefinition then
        let body := info.value!
        if body.approxDepth <= 80 && body.sizeWithoutSharing <= 1500 then
          checkWithKernel body
          definitionTree ← tree body #[] "definition" policy
          definitionExpression := expressionOf definitionTree
          definitionBodyStatus := "available"
        else definitionBodyStatus := "export-size-limit"
      if info.isDefinition && info.type == mkSort levelZero then
        inspected := "proposition-definition"
        pure (Lean.mkConst name (info.levelParams.map Level.param))
      else
        inspected := if (← isProp info.type) then "statement" else "signature"
        pure info.type
    else do
      match validateSyntax stx with
      | .error err => throwError "{err}"
      | .ok _ => pure ()
      let e ← elabTermEnsuringType stx (some (mkSort levelZero))
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
  if expression.hasMVar then throwError "Unresolved metavariables remain; provide explicit types."
  if expression.hasSorry then throwError "A placeholder or sorry remains; the statement was rejected."
  let proposition ← isProp expression
  if inputMode == "term" && !proposition then throwError "Input must be a mathematical proposition (a term of type Prop)."
  checkWithKernel expression
  let result ← tree expression #[] "n" policy
  let mut terms := #[]
  let infoState ← getInfoState
  for t in infoState.trees do terms ← sourceTerms (t.substitute infoState.assignment) terms
  let mut definitions := if (declaration.getObjValAs? Bool "canExpand").toOption.getD false then #[declaration] else #[]
  for name in expression.getUsedConstants do
    if definitions.size >= 128 then break
    if let some info := env.find? name then
      if info.isDefinition && !info.isUnsafe && !info.isPartial then
        let entry ← declarationJson info
        if !definitions.contains entry then definitions := definitions.push entry
  return obj [
    ("ok", toJson true), ("schemaVersion", toJson (2 : Nat)),
    ("leanVersion", str Lean.versionString), ("source", str source),
    ("pretty", str (← pp expression)), ("type", str (← pp (← inferType expression))),
    ("validation", str (if proposition then "kernel-type-checked-statement" else "kernel-type-checked-declaration-type")),
    ("provenance", obj [("assistant", str "lean"), ("inputMode", str inputMode), ("inspected", str inspected),
      ("declaration", declaration), ("mathlibRevision", str "8f9d9cff6bd728b17a24e163c9402775d9e6a365")]),
    ("expansionPolicy", obj [("constants", toJson (policy.constants.map Name.toString)), ("maxDepth", toJson policy.maxDepth)]),
    ("definitions", Json.arr definitions), ("sourceTerms", Json.arr terms),
    ("definitionExpression", definitionExpression), ("definitionTree", definitionTree),
    ("definitionBodyStatus", str definitionBodyStatus),
    ("tree", result), ("expression", expressionOf result), ("originalExpression", ← encode expression #[] "original"),
    ("metrics", Json.arr #[]), ("diagnostics", Json.arr #[])]

def errorResult (message : String) : Json := obj [("ok", toJson false), ("schemaVersion", toJson (2 : Nat)), ("error", str message),
  ("diagnostics", Json.arr #[obj [("severity", str "error"), ("message", str message)]])]

unsafe def main : IO Unit := do
  let sysroot ← match ← IO.getEnv "STATEMENTLENS_LEAN_SYSROOT" with
    | some p => pure (System.FilePath.mk p)
    | none => findSysroot
  initSearchPath sysroot
  enableInitializersExecution
  let opts := ({} : Options).set `maxRecDepth (256 : Nat) |>.set `maxHeartbeats (400000 : Nat) |>.set `autoImplicit false
  let env ← importModules imports opts 0 (loadExts := true)
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let requestId := ((Json.parse line).toOption.bind fun request => (request.getObjVal? "requestId").toOption).getD Json.null
    let result ← try
      let request ← IO.ofExcept (Json.parse line)
      let source ← IO.ofExcept (request.getObjValAs? String "source")
      if source.utf8ByteSize > 65536 then throw (IO.userError "Statement exceeds 65536 bytes.")
      let action := MetaM.run' (TermElabM.run' (analyze source request))
      Core.CoreM.toIO' action { fileName := "<statement>", fileMap := FileMap.ofString source, options := opts } { env }
    catch err => pure (errorResult err.toString)
    let result := if requestId == Json.null then result else result.setObjVal! "requestId" requestId
    stdout.putStrLn result.compress
    stdout.flush

end StatementLens

unsafe def main : IO Unit := StatementLens.main
