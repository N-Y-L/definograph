import Lean

/- Shared read-only expression export. This module registers no environment extensions. -/
open Lean Meta Elab Term
namespace StatementLens

def obj := Json.mkObj
def str := Json.str

def permittedSyntax : Array Name := #[
  `null, `group, `hygieneInfo, `num, `fieldIdx,
  `Lean.Parser.Term.forall, `Lean.Parser.Term.explicitBinder,
  `Lean.Parser.Term.type, `Lean.Parser.Term.sort, `Lean.Parser.Term.prop,
  `Lean.Parser.Level.paren, `Lean.Parser.Level.max, `Lean.Parser.Level.imax, `Lean.Parser.Level.addLit,
  `Lean.Parser.Term.implicitBinder, `Lean.Parser.Term.strictImplicitBinder,
  `Lean.Parser.Term.instBinder, `Lean.Parser.Term.typeSpec,
  `Lean.Parser.Term.arrow, `Lean.Parser.Term.depArrow, `Lean.Parser.Term.app, `Lean.Parser.Term.paren,
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

/-- Editor exports cannot reuse the fixed worker's trusted-global-instance assumption. -/
def projectContextMode : MetaM Bool := return (← getOptions).getBool `statementLens.projectContext false

/-- Exact declaring modules for interpreted constructors. Project declarations with
    matching spellings remain opaque; this is a semantic audit, not a sandbox. -/
def canonicalModule (name : Name) : Option Name :=
  if #[`Add.add, `And, `Div.div, `Eq, `False, `Fin, `GE.ge, `GT.gt,
    `HAdd.hAdd, `HDiv.hDiv, `HMul.hMul, `HPow.hPow, `HSub.hSub, `LE.le, `LT.lt,
    `Max.max, `Membership.mem, `Min.min, `Mul.mul, `Nat, `Neg.neg, `Not,
    `OfNat.ofNat, `Or, `Pow.pow, `Prod, `Prod.fst, `Prod.mk, `Prod.snd, `Sub.sub, `True, `Function.comp, `instOfNatNat].contains name
      then some `Init.Prelude
  else if #[`Exists, `HasSubset.Subset, `Iff, `Ne, `Union.union, `Inter.inter, `SDiff.sdiff].contains name then some `Init.Core
  else if #[`Function.Injective, `Function.Surjective].contains name then some `Init.Data.Function
  else if name == `Int then some `Init.Data.Int.Basic
  else if name == `Rat then some `Init.Data.Rat.Basic
  else if name == `Real then some `Mathlib.Data.Real.Basic
  else if name == `Function.Bijective then some `Mathlib.Logic.Function.Defs
  else if #[`Dist.dist, `Metric.ball, `Metric.closedBall, `Metric.sphere].contains name
    then some `Mathlib.Topology.MetricSpace.Pseudo.Defs
  else if #[`Set, `Set.Mem, `Set.Subset, `Set.image, `Set.union, `Set.inter, `Set.diff, `Set.compl,
    `Set.instEmptyCollection, `Set.instHasSubset, `Set.instInter, `Set.instMembership,
    `Set.instSDiff, `Set.instUnion].contains name then some `Mathlib.Data.Set.Defs
  else if #[`Set.preimage, `Set.instCompl].contains name then some `Mathlib.Data.Set.Operations
  else if name == `Compl.compl then some `Mathlib.Order.Notation
  else if name == `Set.instHasSSubset then some `Mathlib.Data.Set.Basic
  else if #[`SimpleGraph, `SimpleGraph.Adj, `SimpleGraph.completeGraph].contains name then some `Mathlib.Combinatorics.SimpleGraph.Basic
  else if #[`SimpleGraph.Hom, `SimpleGraph.Embedding, `SimpleGraph.Iso].contains name then some `Mathlib.Combinatorics.SimpleGraph.Maps
  else if #[`SimpleGraph.Coloring, `SimpleGraph.Colorable].contains name then some `Mathlib.Combinatorics.SimpleGraph.Coloring
  else if #[`RelHom.toFun, `RelHom, `RelHom.instFunLike, `RelEmbedding, `RelEmbedding.instFunLike, `RelIso, `RelIso.instFunLike].contains name then some `Mathlib.Order.RelIso.Basic
  else if name == `DFunLike.coe then some `Mathlib.Data.FunLike.Basic
  else if #[`PartialEquiv, `PartialEquiv.source, `PartialEquiv.target,
    `PartialEquiv.toFun, `PartialEquiv.invFun, `PartialEquiv.symm].contains name
      then some `Mathlib.Logic.Equiv.PartialEquiv
  else if #[`OpenPartialHomeomorph, `OpenPartialHomeomorph.toPartialEquiv,
    `OpenPartialHomeomorph.toFun', `OpenPartialHomeomorph.symm].contains name
      then some `Mathlib.Topology.OpenPartialHomeomorph.Defs
  else none

def canonicalConstant (name : Name) : MetaM Bool := do
  unless ← projectContextMode do return true
  let some expected := canonicalModule name | return false
  let env ← getEnv
  let actual := (env.getModuleIdxFor? name).bind fun index => env.allImportedModuleNames[index.toNat]?
  return actual == some expected

/-- Numerical classification is independent of the general typed object descriptor. -/
def domain (t : Expr) : MetaM (String × Nat) := do
  if ← projectContextMode then return ("unknown", 0)
  unless (← getEnv).contains `Real do return ("unknown", 0)
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
  if !head.isAnonymous && !(← canonicalConstant head) then
    return base (if ← isProp t then "proposition" else "structure")
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

def basicBinderJson (b : Bound) (t : Expr) (bs : Bounds) : MetaM Json := do
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
        if setInstances.contains (a.getAppFn.constName?.getD .anonymous) && a.getAppArgs.size == 1 &&
            (← canonicalConstant (a.getAppFn.constName?.getD .anonymous)) then
          continue
        -- These exact bundled-function instances project the stored map. A local
        -- or globally replaced coercion must not inherit that interpretation.
        if #[`RelHom.instFunLike, `RelEmbedding.instFunLike].contains (a.getAppFn.constName?.getD .anonymous) &&
            a.getAppArgs.size == 4 && (← canonicalConstant (a.getAppFn.constName?.getD .anonymous)) then
          continue
        if a.isAppOfArity `instOfNatNat 1 && (← canonicalConstant `instOfNatNat) then
          continue
        if ← projectContextMode then return false
        if ty.hasFVar || ty.hasMVar then return false
        let expected ← withLCtx {} {} <| synthInstance ty
        unless ← isDefEq a expected do return false
    return true
  catch _ => return false

partial def encode (e : Expr) (bs : Bounds) (path : String) (depth : Nat := 0) : MetaM Json := do
  if depth > 80 then return obj [("kind", str "opaque"), ("text", str "Expression depth limit")]
  let e := e.consumeMData
  match e with
  | .const name levels => return obj [("kind", str "const"), ("name", str name.toString),
      ("levels", toJson (levels.map toString)), ("canonical", toJson (← canonicalConstant name)),
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
      return obj [("kind", str kind), ("binder", ← basicBinderJson b ty bs),
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

/-- A bounded type-head view exposes safe aliases without replacing their names.
    This is shared by statement binders and the editor's local-context binders.
    It neither synthesizes structure fields nor replays source commands. -/
def binderTypeExpansion (t : Expr) (bs : Bounds) (path : String) : MetaM Json := do
  let ctx ← readThe Core.Context
  let now ← IO.getNumHeartbeats
  let remaining := if ctx.maxHeartbeats == 0 then 1200000 else ctx.maxHeartbeats - (now - ctx.initHeartbeats)
  let budget := min 200000 (remaining - 1000000)
  if budget < 1000 then return Json.null
  let saved ← Meta.saveState
  try
    withTheReader Core.Context (fun state =>
      { state with initHeartbeats := now, maxHeartbeats := budget, maxRecDepth := min state.maxRecDepth 128 }) do
      if t.hasMVar || t.hasSorry || t.approxDepth > 24 || t.sizeWithoutSharing > 80 then return Json.null
      if ← isProp t then return Json.null
      let mut expanded := t
      let mut constants : Array Name := #[]
      for _ in [:2] do
        let head := expanded.getAppFn.constName?.getD .anonymous
        if head.isAnonymous then break
        -- Keep any already audited vocabulary intact. Unknown safe aliases can
        -- lead to any type, including a function type or an unfamiliar structure.
        if (canonicalModule head).isSome && (← canonicalConstant head) then break
        let some info := (← getEnv).find? head | break
        unless info.isDefinition && !info.isUnsafe && !info.isPartial do break
        let some next ← unfoldDefinition? expanded (ignoreTransparency := true) | break
        if next == expanded || next.hasMVar || next.hasSorry ||
            next.approxDepth > 24 || next.sizeWithoutSharing > 80 then break
        if next.getAppFn.constName? == expanded.getAppFn.constName? then break
        checkWithKernel next
        unless ← isDefEq t next do return Json.null
        constants := constants.push head
        expanded := next
      if constants.isEmpty then return Json.null
      let result := obj [
        ("expression", ← encode expanded bs (path ++ ".typeExpansion")),
        ("before", str (← pp t)), ("after", str (← pp expanded)),
        ("constants", toJson (constants.map Name.toString)),
        ("definitionalEquality", toJson true), ("maxDepth", toJson (2 : Nat))]
      if result.compress.utf8ByteSize > 65536 then return Json.null
      return result
  catch _ => return Json.null
  finally saved.restore

def binderJson (b : Bound) (t : Expr) (bs : Bounds) : MetaM Json := do
  let basic ← basicBinderJson b t bs
  let expansion ← binderTypeExpansion t bs b.id
  return if expansion == Json.null then basic else basic.setObjVal! "typeExpansion" expansion

/-- Generic structure reflection uses Lean's declaration metadata and checked
    projections. The callback reads law types with recursive reflection disabled. -/
def reflectBinder (b : Bound) (t : Expr) (bs : Bounds) (basic : Json)
    (lawTree : Expr → Bounds → String → MetaM Json) : MetaM Json := do
  let ctx ← readThe Core.Context
  let now ← IO.getNumHeartbeats
  let remaining := if ctx.maxHeartbeats == 0 then 3000000 else ctx.maxHeartbeats - (now - ctx.initHeartbeats)
  let budget := min 2000000 (remaining - 1000000)
  if budget < 1000 then return basic
  let saved ← Meta.saveState
  try
    withTheReader Core.Context (fun state =>
      { state with initHeartbeats := now, maxHeartbeats := budget, maxRecDepth := min state.maxRecDepth 128 }) do
      if t.hasMVar || t.hasSorry || t.approxDepth > 24 || t.sizeWithoutSharing > 120 then return basic
      let env ← getEnv
      let mut reflectedType := t
      let mut aliasSteps := 0
      -- Follow at most two safe aliases to any structure, with no vocabulary list.
      for _ in [:2] do
        let head := reflectedType.getAppFn.constName?.getD .anonymous
        if (getStructureInfo? env head).isSome then break
        let some info := env.find? head | break
        unless info.isDefinition && !info.isUnsafe && !info.isPartial do break
        let some next ← unfoldDefinition? reflectedType (ignoreTransparency := true) | break
        if next == reflectedType || next.hasMVar || next.hasSorry ||
            next.approxDepth > 24 || next.sizeWithoutSharing > 120 then break
        checkWithKernel next
        unless ← isDefEq t next do return basic
        reflectedType := next
        aliasSteps := aliasSteps + 1
      let head := reflectedType.getAppFn.constName?.getD .anonymous
      let some structureInfo := getStructureInfo? env head | do
        if aliasSteps == 2 then
          if let some info := env.find? head then
            if info.isDefinition && !info.isUnsafe && !info.isPartial then
              return basic.setObjVal! "structureOmission" (str "Type inspection stopped after two checked definition steps; the original declared type remains visible.")
        return basic
      let mut fields : Array Json := #[]
      let mut previous : Array (Name × Expr) := #[]
      let mut stopReason : Option String := none
      let extended := bs.push b
      for index in [:structureInfo.fieldNames.size] do
        if index >= 16 then
          stopReason := some "The structure has more than 16 direct fields; remaining fields are not expanded."
          break
        let fieldName := structureInfo.fieldNames[index]!
        let some info := structureInfo.fieldInfo.find? (·.fieldName == fieldName) | continue
        try
          let projection ← instantiateMVars (← mkProjection (mkFVar b.fvar) fieldName)
          let fieldType ← instantiateMVars (← inferType projection)
          if projection.hasMVar || projection.hasSorry || fieldType.hasMVar || fieldType.hasSorry ||
              projection.approxDepth > 24 || projection.sizeWithoutSharing > 120 ||
              fieldType.approxDepth > 24 || fieldType.sizeWithoutSharing > 120 then
            stopReason := some "A field exceeded the checked expression size or depth limit."
            continue
          checkWithKernel projection
          checkWithKernel fieldType
          let proof ← isProp fieldType
          let fieldPath := b.id ++ s!".structure.{index}"
          let dependsOn := previous.filterMap fun (name, expression) =>
            if (fieldType.find? (· == expression)).isSome then some name.toString else none
          let lawFields ← if proof then do
              pure [("law", ← lawTree fieldType extended (fieldPath ++ ".law"))]
            else pure []
          let typeView ← if proof then pure Json.null else binderTypeExpansion fieldType extended fieldPath
          let field ← pure <| obj ([("name", str fieldName.toString), ("projection", str info.projFn.toString),
            ("expression", ← encode projection extended (fieldPath ++ ".value")),
            ("type", str (← pp fieldType)), ("typeExpression", ← encode fieldType extended (fieldPath ++ ".type")),
            ("typeDescriptor", ← describeType fieldType), ("kind", str (if proof then "law" else "data")),
            ("dependsOn", toJson dependsOn)] ++
            (match info.subobject? with | some parent => [("parent", str parent.toString)] | none => []) ++
            (if typeView == Json.null then [] else [("typeExpansion", typeView)]) ++
            lawFields)
          if (Json.arr (fields.push field)).compress.utf8ByteSize > 120000 then
            stopReason := some "Further field readings exceed the optional structure payload budget."
            break
          fields := fields.push field
          previous := previous.push (fieldName, projection)
        catch _ =>
          stopReason := some "A field could not be reflected within its checked export budget."
      let result := obj ([("name", str head.toString), ("typeExpression", ← encode reflectedType bs (b.id ++ ".structure.type")),
        ("fields", Json.arr fields), ("omittedFields", toJson (structureInfo.fieldNames.size - fields.size)),
        ("kernelChecked", toJson true),
        ("limits", obj [("maxFields", toJson (16 : Nat)), ("maxFieldNodes", toJson (120 : Nat)), ("maxDepth", toJson (24 : Nat))])] ++
        (match stopReason with | some reason => [("stopReason", str reason)] | none => []))
      if result.compress.utf8ByteSize > 131072 then return basic
      return basic.setObjVal! "structure" result
  catch error =>
    let message ← error.toMessageData.toString
    return basic.setObjVal! "structureOmission" (str ("Structure details unavailable: " ++ (message.take 512).toString))
  finally saved.restore

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
    (policy : ExportPolicy := {}) (expansionDepth : Nat := 0) (depth : Nat := 0)
    (reflectStructures : Bool := true) : MetaM Json := do
  if depth > 80 then throwError "Logical structure exceeds export depth (80)."
  let e := e.consumeMData
  let pretty ← pp e
  let finish (j : Json) := j.setObjVal! "scope" (toJson (bs.map (·.id)))
  let head := e.getAppFn.constName?.getD .anonymous
  if policy.constants.contains head && expansionDepth < policy.maxDepth then
    if let some expanded ← unfoldDefinition? e (ignoreTransparency := true) then
      unless expanded == e do
        if expanded.hasMVar || expanded.hasSorry then throwError "The expanded definition contains unresolved metavariables or sorry."
        checkWithKernel expanded
        unless ← isDefEq e expanded do throwError "Definition expansion did not preserve definitional equality."
        let result ← tree expanded bs path policy (expansionDepth + 1) (depth + 1) reflectStructures
        return finish <| result.setObjVal! "expansion" (obj [
          ("constant", str head.toString), ("before", str pretty), ("after", str (← pp expanded)),
          ("originalExpression", ← encode e bs path), ("definitionalEquality", toJson true),
          ("depth", toJson (expansionDepth + 1))])
  match e with
  | .lam name ty body bi =>
    withLocalDecl name bi ty fun x => do
      let b : Bound := ⟨x.fvarId!, path ++ ".binder", binderName name, ← pp ty, "parameter"⟩
      let bj ← binderJson b ty bs
      let bj ← if reflectStructures then reflectBinder b ty bs bj (fun e bs path => tree e bs path {} 0 0 false) else pure bj
      let child ← tree (body.instantiate1 x) (bs.push b) (path ++ ".body") policy expansionDepth (depth + 1) reflectStructures
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
      let bj ← if reflectStructures then reflectBinder b ty bs bj (fun e bs path => tree e bs path {} 0 0 false) else pure bj
      let child ← tree (body.instantiate1 x) (bs.push b) (path ++ ".body") policy expansionDepth (depth + 1) reflectStructures
      let children ← if prop && statement then pure #[← tree ty bs (path ++ ".premise") policy expansionDepth (depth + 1) reflectStructures, child] else pure #[child]
      let expression := obj [("kind", str "forall"), ("binder", bj), ("binderType", ← encode ty bs (path ++ ".type")), ("body", expressionOf child)]
      return finish <| node path kind (if !statement then s!"Parameter {binderName name}" else if prop then "If … then …" else s!"For every {binderName name}") pretty children expression (some bj)
  | _ =>
    let args := e.getAppArgs
    let rawHead := e.getAppFn.constName?.getD .anonymous
    let head := if ← canonicalConstant rawHead then rawHead else .anonymous
    if head == `Exists && args.size == 2 then
      let p ← whnf args[1]!
      if let .lam name ty body bi := p then
        return ← withLocalDecl name bi ty fun x => do
          let b : Bound := ⟨x.fvarId!, path ++ ".binder", binderName name, ← pp ty, "existential"⟩
          let bj ← binderJson b ty bs
          let bj ← if reflectStructures then reflectBinder b ty bs bj (fun e bs path => tree e bs path {} 0 0 false) else pure bj
          let child ← tree (body.instantiate1 x) (bs.push b) (path ++ ".body") policy expansionDepth (depth + 1) reflectStructures
          let expr := obj [("kind", str "app"), ("fn", obj [("kind", str "const"), ("name", str "Exists")]),
            ("args", Json.arr #[← encode ty bs (path ++ ".type"), obj [("kind", str "lambda"), ("binder", bj), ("binderType", ← encode ty bs (path ++ ".type")), ("body", expressionOf child)]])]
          return finish <| node path "exists" s!"There exists {binderName name}" pretty #[child] expr (some bj)
    let logical := if head == `And then some ("and", "Both conditions") else if head == `Or then some ("or", "At least one condition") else if head == `Iff then some ("iff", "Equivalent conditions") else if head == `Not then some ("not", "Not") else none
    if let some (kind, label) := logical then
      let mut children := #[]
      for i in [:args.size] do children := children.push (← tree args[i]! bs s!"{path}.{i}" policy expansionDepth (depth + 1) reflectStructures)
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


/-- Candidates are logical heads only. Their single unfolding must be small and
    remain a proposition; the frontend determines whether its reading improves.
    Arbitrary computational definitions are not executed or normalized. -/
partial def previewCandidates (expression : Expr) (names : Array Name := #[])
    (depth : Nat := 0) : MetaM (Array Name) := do
  if names.size >= 3 || depth > 40 then return names
  let expression := expression.consumeMData
  match expression with
  | .forallE name ty body bi | .lam name ty body bi =>
    let names ← if ← isProp ty then previewCandidates ty names (depth + 1) else pure names
    return ← withLocalDecl name bi ty fun value =>
      previewCandidates (body.instantiate1 value) names (depth + 1)
  | _ =>
    let head := expression.getAppFn.constName?.getD .anonymous
    let args := expression.getAppArgs
    if #[`And, `Or, `Iff, `Not].contains head then
      let mut names := names
      for arg in args do names ← previewCandidates arg names (depth + 1)
      return names
    if head == `Exists && args.size == 2 then return ← previewCandidates args[1]! names (depth + 1)
    if head.isAnonymous || names.contains head then return names
    let some info := (← getEnv).find? head | return names
    unless info.isDefinition && !info.isUnsafe && !info.isPartial do return names
    unless ← isProp expression do return names
    let some expanded ← unfoldDefinition? expression (ignoreTransparency := true) | return names
    if expanded == expression || expanded.hasMVar || expanded.hasSorry ||
        expanded.approxDepth > 24 || expanded.sizeWithoutSharing > 80 then return names
    unless ← isProp expanded do return names
    checkWithKernel expanded
    unless ← isDefEq expression expanded do return names
    return names.push head

/-- Optional previews reuse the already elaborated expression and its local
    context. They never replay project commands, and cannot invalidate the
    mandatory semantic response when their own budget is exhausted. -/
def definitionPreviews (request : Json) (policy : ExportPolicy) (expressions : Array Expr)
    (originalPretty : String) (build : ExportPolicy → MetaM Json) : MetaM (Array Json) := do
  unless (request.getObjValAs? Bool "previewDefinitions").toOption.getD false do return #[]
  unless policy.constants.isEmpty do return #[]
  let ctx ← readThe Core.Context
  let now ← IO.getNumHeartbeats
  let remaining := if ctx.maxHeartbeats == 0 then 20000000 else ctx.maxHeartbeats - (now - ctx.initHeartbeats)
  let budget := min 20000000 (remaining - 1000000)
  if budget < 1000 then return #[]
  let saved ← Meta.saveState
  try
    withTheReader Core.Context (fun state =>
      { state with initHeartbeats := now, maxHeartbeats := budget, maxRecDepth := min state.maxRecDepth 128 }) do
      let mut names := #[]
      for expression in expressions do names ← previewCandidates expression names
      let mut previews := #[]
      let mut bytes := 0
      for name in names do
        try
          let previewPolicy : ExportPolicy := { constants := #[name], maxDepth := 1 }
          let result ← build previewPolicy
          let preview := obj [("constant", str name.toString), ("pretty", str originalPretty),
            ("originalPretty", str originalPretty), ("tree", result), ("expression", expressionOf result),
            ("expansionPolicy", obj [("constants", toJson #[name.toString]), ("maxDepth", toJson (1 : Nat))])]
          let size := preview.compress.utf8ByteSize
          if bytes + size <= 262144 then
            previews := previews.push preview
            bytes := bytes + size
        catch _ => pure ()
      return previews
  catch _ => return #[]
  finally saved.restore

end StatementLens
