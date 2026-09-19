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
  `«term-_», `«term|___|»
]

partial def validateSyntax (stx : Syntax) (depth : Nat := 0) : Except String Unit := do
  if depth > 128 then throw "Statement nesting exceeds the supported depth (128)."
  match stx with
  | .node _ kind args =>
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

/-- Domain classification uses definitional equality, never the user's spelling. -/
def domain (t : Expr) : MetaM (String × Nat) := do
  if ← isDefEq t realType then return ("real", 1)
  if ← isDefEq t (mkApp2 (mkConst `Prod [levelZero, levelZero]) realType realType) then
    return ("sup2", 2)
  if ← isDefEq t (← mkArrow realType realType) then return ("realFunction", 1)
  for n in [:13] do
    let fin := mkApp (mkConst `Fin) (mkNatLit n)
    let euclidean ← mkAppM `EuclideanSpace #[realType, fin]
    if ← isDefEq t euclidean then
      return (if n == 2 then "euclidean2" else "euclideanN", n)
    if ← isDefEq t (← mkArrow fin realType) then
      return (if n == 2 then "sup2" else "supN", n)
  return ("unknown", 0)

def binderJson (b : Bound) (t : Expr) (bs : Bounds) : MetaM Json := do
  let (d, n) ← domain t
  return obj [
    ("id", str b.id), ("name", str b.name), ("type", str b.type),
    ("role", str b.role), ("domain", str d), ("dimension", toJson n),
    ("dependsOn", toJson ((bs.filter (·.role != "assumption")).map (·.id))) ]

/-- Compare all explicit class arguments to the canonical imported instance in an
    empty local context. Thus custom/local metric or arithmetic instances do not
    inherit a standard numerical interpretation. -/
def standardInstances (e : Expr) : MetaM Bool := do
  try
    for a in e.getAppArgs do
      let ty ← inferType a
      if (← isClass? ty).isSome then
        if ty.hasFVar || ty.hasMVar then return false
        let expected ← withLCtx {} {} <| synthInstance ty
        unless ← isDefEq a expected do return false
    return true
  catch _ => return false

partial def encode (e : Expr) (bs : Bounds) (path : String) (depth : Nat := 0) : MetaM Json := do
  if depth > 80 then return obj [("kind", str "opaque"), ("text", str "Expression depth limit")]
  let e := e.consumeMData
  match e with
  | .const name _ => return obj [("kind", str "const"), ("name", str name.toString)]
  | .fvar id =>
    if let some b := bs.find? (·.fvar == id) then
      return obj [("kind", str "var"), ("id", str b.id), ("name", str b.name), ("type", str b.type)]
    return obj [("kind", str "opaque"), ("text", str (← pp e))]
  | .lit (.natVal n) => return obj [("kind", str "literal"), ("value", toJson n)]
  | .lit (.strVal s) => return obj [("kind", str "literal"), ("value", str s)]
  | .sort l => return obj [("kind", str "sort"), ("name", str (toString l))]
  | .forallE name ty body bi | .lam name ty body bi =>
    let kind := if e.isLambda then "lambda" else "forall"
    let prop ← isProp ty
    withLocalDecl name bi ty fun x => do
      let b : Bound := ⟨x.fvarId!, path ++ ".binder", name.toString, ← pp ty, if e.isLambda then "lambda" else if prop then "assumption" else "universal"⟩
      return obj [("kind", str kind), ("binder", ← binderJson b ty bs),
        ("binderType", ← encode ty bs (path ++ ".type") (depth + 1)),
        ("body", ← encode (body.instantiate1 x) (bs.push b) (path ++ ".body") (depth + 1))]
  | .app .. =>
    let args := e.getAppArgs
    let name := e.getAppFn.constName?.getD .anonymous
    let mut encoded := #[]
    for i in [:args.size] do
      let a := args[i]!
      if (← isClass? (← inferType a)).isSome then
        encoded := encoded.push (obj [("kind", str "opaque"), ("text", str (← pp a))])
      else
        encoded := encoded.push (← encode a bs s!"{path}.{i}" (depth + 1))
    let std ← standardInstances e
    let ty ← inferType e
    let (d, n) ← domain ty
    let mut fields := [
      ("kind", str "app"), ("fn", ← encode e.getAppFn bs (path ++ ".fn") (depth + 1)),
      ("args", Json.arr encoded), ("standard", toJson std), ("type", str (← pp ty)),
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

partial def tree (e : Expr) (bs : Bounds := #[]) (path : String := "n") : MetaM Json := do
  let e := e.consumeMData
  let pretty ← pp e
  match e with
  | .forallE name ty body bi =>
    let prop ← isProp ty
    let kind := if prop then "implies" else "forall"
    withLocalDecl name bi ty fun x => do
      let b : Bound := ⟨x.fvarId!, path ++ ".binder", name.toString, ← pp ty, if prop then "assumption" else "universal"⟩
      let bj ← binderJson b ty bs
      let child ← tree (body.instantiate1 x) (bs.push b) (path ++ ".body")
      let children ← if prop then pure #[← tree ty bs (path ++ ".premise"), child] else pure #[child]
      let expression := obj [("kind", str "forall"), ("binder", bj), ("binderType", ← encode ty bs (path ++ ".type")), ("body", expressionOf child)]
      return node path kind (if prop then "If … then …" else s!"For every {name}") pretty children expression (some bj)
  | _ =>
    let args := e.getAppArgs
    let head := e.getAppFn.constName?.getD .anonymous
    if head == `Exists && args.size == 2 then
      let p ← whnf args[1]!
      if let .lam name ty body bi := p then
        return ← withLocalDecl name bi ty fun x => do
          let b : Bound := ⟨x.fvarId!, path ++ ".binder", name.toString, ← pp ty, "existential"⟩
          let bj ← binderJson b ty bs
          let child ← tree (body.instantiate1 x) (bs.push b) (path ++ ".body")
          let expr := obj [("kind", str "app"), ("fn", obj [("kind", str "const"), ("name", str "Exists")]),
            ("args", Json.arr #[← encode ty bs (path ++ ".type"), obj [("kind", str "lambda"), ("binder", bj), ("binderType", ← encode ty bs (path ++ ".type")), ("body", expressionOf child)]])]
          return node path "exists" s!"There exists {name}" pretty #[child] expr (some bj)
    let logical := if head == `And then some ("and", "Both conditions") else if head == `Or then some ("or", "At least one condition") else if head == `Iff then some ("iff", "Equivalent conditions") else if head == `Not then some ("not", "Not") else none
    if let some (kind, label) := logical then
      let mut children := #[]
      for i in [:args.size] do children := children.push (← tree args[i]! bs s!"{path}.{i}")
      let expr := obj [("kind", str "app"), ("fn", obj [("kind", str "const"), ("name", str head.toString)]),
        ("args", Json.arr (children.map expressionOf))]
      return node path kind label pretty children expr
    return node path "predicate" pretty pretty #[] (← encode e bs path)

def analyze (source : String) : TermElabM Json := withoutErrToSorry do
  let env ← getEnv
  let stx ← match Parser.runParserCategory env `term source "<statement>" with
    | .ok s => pure s
    | .error err => throwError "{err}"
  match validateSyntax stx with
  | .error err => throwError "{err}"
  | .ok _ => pure ()
  let expression ← elabTermEnsuringType stx (some (mkSort levelZero))
  synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  if expression.hasMVar then throwError "Unresolved metavariables remain; provide explicit types."
  if expression.hasSorry then throwError "A placeholder or sorry remains; the statement was rejected."
  unless ← isProp expression do throwError "Input must be a mathematical proposition (a term of type Prop)."
  checkWithKernel expression
  let result ← tree expression
  return obj [
    ("ok", toJson true), ("leanVersion", str Lean.versionString), ("source", str source),
    ("pretty", str (← pp expression)), ("type", str "Prop"),
    ("validation", str "kernel-type-checked-statement"),
    ("tree", result), ("expression", expressionOf result), ("metrics", Json.arr #[]), ("diagnostics", Json.arr #[])]

def errorResult (message : String) : Json := obj [("ok", toJson false), ("error", str message),
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
      let action := MetaM.run' (TermElabM.run' (analyze source))
      Core.CoreM.toIO' action { fileName := "<statement>", fileMap := FileMap.ofString source, options := opts } { env }
    catch err => pure (errorResult err.toString)
    let result := if requestId == Json.null then result else result.setObjVal! "requestId" requestId
    stdout.putStrLn result.compress
    stdout.flush

end StatementLens

unsafe def main : IO Unit := StatementLens.main
