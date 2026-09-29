import ExactJson

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Definograph
open Lean Meta

/-- Limits cover expanded constructor JSON, including repeated strings and names.
Callers may lower these limits, but cannot raise the implementation ceilings. -/
structure RawJsonLimits where
  maxNodes : Nat := 100000
  maxDepth : Nat := 128
  maxTextBytes : Nat := 2 * 1024 * 1024
  maxNaturalDigits : Nat := 10000
  maxOutputBytes : Nat := 16 * 1024 * 1024

private structure RawState where
  limits : RawJsonLimits
  naturalExclusiveBound : Nat
  nodes : Nat := 0
  textBytes : Nat := 0
  outputBytes : Nat := 0

private abbrev RawM := StateT RawState (Except String)

private def depthCheck (depth : Nat) : RawM Unit := do
  if depth > (← get).limits.maxDepth then throw "raw JSON depth limit exceeded"

private def charge (depth output : Nat) : RawM Unit := do
  depthCheck depth
  let state ← get
  if state.nodes + 1 > state.limits.maxNodes then throw "raw JSON node limit exceeded"
  if state.outputBytes + output > state.limits.maxOutputBytes then throw "raw JSON output byte limit exceeded"
  set { state with nodes := state.nodes + 1, outputBytes := state.outputBytes + output }

private def textJson (depth : Nat) (value : String) : RawM Json := do
  depthCheck depth
  let state ← get
  if state.textBytes + value.utf8ByteSize > state.limits.maxTextBytes then
    throw "raw JSON cumulative UTF-8 text limit exceeded"
  set { state with textBytes := state.textBytes + value.utf8ByteSize }
  let encoded := toJson value
  -- A single string is text-bounded before its escaped spelling is allocated.
  charge depth encoded.compress.utf8ByteSize
  return encoded

private def boolJson (depth : Nat) (value : Bool) : RawM Json := do
  charge depth (if value then 4 else 5)
  return toJson value

private def arrayJson (depth : Nat) (values : Array Json) : RawM Json := do
  charge depth (2 + (values.size - 1))
  return .arr values

private def tagJson (depth : Nat) (tag : String) (values : List Json := []) : RawM Json := do
  let head ← textJson (depth + 1) tag
  arrayJson depth (#[head] ++ values.toArray)

private def objectJson (depth : Nat) (fields : List (String × Json)) : RawM Json := do
  for (key, _) in fields do
    let _ ← textJson (depth + 1) key
  charge depth (2 + (fields.length - 1) + fields.length)
  return Json.mkObj fields

private def natJson (depth : Nat) (value : Nat) : RawM Json := do
  depthCheck depth
  -- Refuse an oversized integer before allocating its decimal spelling.
  if value >= (← get).naturalExclusiveBound then throw "raw JSON natural digit limit exceeded"
  tagJson depth "nat" [← textJson (depth + 1) (toString value)]

private def intJson (depth : Nat) (value : Int) : RawM Json := do
  depthCheck depth
  match value with
  | .ofNat n => tagJson depth "ofNat" [← natJson (depth + 1) n]
  | .negSucc n => tagJson depth "negSucc" [← natJson (depth + 1) n]

private def rawName (depth : Nat) (value : Name) : RawM Json := do
  depthCheck depth
  match value with
  | .anonymous => tagJson depth "anonymous"
  | .str parent part => tagJson depth "str" [← rawName (depth + 1) parent, ← textJson (depth + 1) part]
  | .num parent part => tagJson depth "num" [← rawName (depth + 1) parent, ← natJson (depth + 1) part]

private def rawLevel (depth : Nat) (value : Level) : RawM Json := do
  depthCheck depth
  match value with
  | .zero => tagJson depth "zero"
  | .succ u => tagJson depth "succ" [← rawLevel (depth + 1) u]
  | .max u v => tagJson depth "max" [← rawLevel (depth + 1) u, ← rawLevel (depth + 1) v]
  | .imax u v => tagJson depth "imax" [← rawLevel (depth + 1) u, ← rawLevel (depth + 1) v]
  | .param n => tagJson depth "param" [← rawName (depth + 1) n]
  | .mvar n => tagJson depth "mvar" [← rawName (depth + 1) n.name]

private def rawSubstring (depth : Nat) (value : Substring.Raw) : RawM Json := do
  depthCheck depth
  tagJson depth "substring" [← textJson (depth + 1) value.str,
    ← natJson (depth + 1) value.startPos.byteIdx, ← natJson (depth + 1) value.stopPos.byteIdx]

private def rawSourceInfo (depth : Nat) (value : SourceInfo) : RawM Json := do
  depthCheck depth
  match value with
  | .none => tagJson depth "none"
  | .original leading pos trailing endPos =>
    tagJson depth "original" [← rawSubstring (depth + 1) leading, ← natJson (depth + 1) pos.byteIdx,
      ← rawSubstring (depth + 1) trailing, ← natJson (depth + 1) endPos.byteIdx]
  | .synthetic pos endPos canonical =>
    tagJson depth "synthetic"
      [← natJson (depth + 1) pos.byteIdx, ← natJson (depth + 1) endPos.byteIdx, ← boolJson (depth + 1) canonical]

private def rawPreresolved (depth : Nat) (value : Syntax.Preresolved) : RawM Json := do
  depthCheck depth
  match value with
  | .namespace name => tagJson depth "namespace" [← rawName (depth + 1) name]
  | .decl name fields =>
    let mut items := #[]
    for field in fields do items := items.push (← textJson (depth + 2) field)
    tagJson depth "decl" [← rawName (depth + 1) name, ← arrayJson (depth + 1) items]

private partial def rawSyntax (depth : Nat) (value : Syntax) : RawM Json := do
  depthCheck depth
  match value with
  | .missing => tagJson depth "missing"
  | .node info kind args =>
    let info ← rawSourceInfo (depth + 1) info
    let kind ← rawName (depth + 1) kind
    let mut children := #[]
    for arg in args do children := children.push (← rawSyntax (depth + 2) arg)
    tagJson depth "node" [info, kind, ← arrayJson (depth + 1) children]
  | .atom info value => tagJson depth "atom" [← rawSourceInfo (depth + 1) info, ← textJson (depth + 1) value]
  | .ident info rawVal value preresolved =>
    let info ← rawSourceInfo (depth + 1) info
    let rawVal ← rawSubstring (depth + 1) rawVal
    let value ← rawName (depth + 1) value
    let mut choices := #[]
    for choice in preresolved do choices := choices.push (← rawPreresolved (depth + 2) choice)
    tagJson depth "ident" [info, rawVal, value, ← arrayJson (depth + 1) choices]

private def rawDataValue (depth : Nat) (value : DataValue) : RawM Json := do
  depthCheck depth
  match value with
  | .ofString value => tagJson depth "ofString" [← textJson (depth + 1) value]
  | .ofBool value => tagJson depth "ofBool" [← boolJson (depth + 1) value]
  | .ofName value => tagJson depth "ofName" [← rawName (depth + 1) value]
  | .ofNat value => tagJson depth "ofNat" [← natJson (depth + 1) value]
  | .ofInt value => tagJson depth "ofInt" [← intJson (depth + 1) value]
  | .ofSyntax value => tagJson depth "ofSyntax" [← rawSyntax (depth + 1) value]

private def rawMetadata (depth : Nat) (value : MData) : RawM Json := do
  depthCheck depth
  let mut entries := #[]
  for (key, value) in value.entries do
    entries := entries.push (← arrayJson (depth + 2)
      #[← rawName (depth + 3) key, ← rawDataValue (depth + 3) value])
  tagJson depth "mdataEntries" [← arrayJson (depth + 1) entries]

private def rawBinderInfo (depth : Nat) (info : BinderInfo) : RawM Json :=
  textJson depth (match info with
    | .default => "default" | .implicit => "implicit"
    | .strictImplicit => "strictImplicit" | .instImplicit => "instImplicit")

private partial def rawExpr (depth : Nat) (value : Expr) : RawM Json := do
  depthCheck depth
  match value with
  | .bvar index => tagJson depth "bvar" [← natJson (depth + 1) index]
  | .fvar id => tagJson depth "fvar" [← rawName (depth + 1) id.name]
  | .mvar id => tagJson depth "mvar" [← rawName (depth + 1) id.name]
  | .sort u => tagJson depth "sort" [← rawLevel (depth + 1) u]
  | .const name levels =>
    let name ← rawName (depth + 1) name
    let mut instances := #[]
    for u in levels do instances := instances.push (← rawLevel (depth + 2) u)
    tagJson depth "const" [name, ← arrayJson (depth + 1) instances]
  | .app fn arg => tagJson depth "app" [← rawExpr (depth + 1) fn, ← rawExpr (depth + 1) arg]
  | .lam name type body info => tagJson depth "lam" [← rawName (depth + 1) name,
      ← rawExpr (depth + 1) type, ← rawExpr (depth + 1) body, ← rawBinderInfo (depth + 1) info]
  | .forallE name type body info => tagJson depth "forallE" [← rawName (depth + 1) name,
      ← rawExpr (depth + 1) type, ← rawExpr (depth + 1) body, ← rawBinderInfo (depth + 1) info]
  | .letE name type value body nondep => tagJson depth "letE" [← rawName (depth + 1) name,
      ← rawExpr (depth + 1) type, ← rawExpr (depth + 1) value, ← rawExpr (depth + 1) body,
      ← boolJson (depth + 1) nondep]
  | .lit literal =>
    let encoded ← match literal with
      | .natVal n => tagJson (depth + 1) "natVal" [← natJson (depth + 2) n]
      | .strVal s => tagJson (depth + 1) "strVal" [← textJson (depth + 2) s]
    tagJson depth "lit" [encoded]
  | .mdata data body => tagJson depth "mdata" [← rawMetadata (depth + 1) data, ← rawExpr (depth + 1) body]
  | .proj name index value => tagJson depth "proj" [← rawName (depth + 1) name,
      ← natJson (depth + 1) index, ← rawExpr (depth + 1) value]

private def rawLocalDeclaration (depth : Nat) (value : LocalDecl) : RawM Json := do
  depthCheck depth
  let common := [("index", ← natJson (depth + 1) value.index),
    ("fvarId", ← rawName (depth + 1) value.fvarId.name),
    ("userName", ← rawName (depth + 1) value.userName), ("type", ← rawExpr (depth + 1) value.type),
    ("kind", ← textJson (depth + 1) (match value.kind with
      | .default => "default" | .implDetail => "implDetail" | .auxDecl => "auxDecl"))]
  match value with
  | .cdecl _ _ _ _ info _ =>
    objectJson depth
      (common ++ [("constructor", ← textJson (depth + 1) "cdecl"), ("binderInfo", ← rawBinderInfo (depth + 1) info)])
  | .ldecl _ _ _ _ value nondep _ => objectJson depth (common ++ [
      ("constructor", ← textJson (depth + 1) "ldecl"), ("value", ← rawExpr (depth + 1) value),
      ("nondep", ← boolJson (depth + 1) nondep)])

private def runRaw {α : Type} (limits : RawJsonLimits) (action : RawM α) : Except String α := do
  let ceiling : RawJsonLimits := {}
  unless limits.maxNodes > 0 && limits.maxNodes <= ceiling.maxNodes &&
      limits.maxDepth > 0 && limits.maxDepth <= ceiling.maxDepth &&
      limits.maxTextBytes > 0 && limits.maxTextBytes <= ceiling.maxTextBytes &&
      limits.maxNaturalDigits > 0 && limits.maxNaturalDigits <= ceiling.maxNaturalDigits &&
      limits.maxOutputBytes > 0 && limits.maxOutputBytes <= ceiling.maxOutputBytes do
    throw "raw JSON limits must be positive and within the implementation ceilings"
  let (value, _) ← action.run { limits, naturalExclusiveBound := 10 ^ limits.maxNaturalDigits }
  return value

/-- Retain public Expr constructor data without resolving references or checking
typing. This is raw data, not semantic admission or a certificate. -/
def rawExprJson (expression : Expr) (limits : RawJsonLimits := {}) : Except String Json :=
  runRaw limits (rawExpr 0 expression)

/-- Multiple raw roots share one budget, including every repeated subtree. -/
def rawExprsJson (expressions : Array Expr) (limits : RawJsonLimits := {}) : Except String (Array Json) :=
  runRaw limits do
    let mut values := #[]
    for expression in expressions do values := values.push (← rawExpr 1 expression)
    let _ ← arrayJson 0 values
    return values

/-- Exact raw source records in supplied order. Repeated declaration indices and
identities are data here; this function asserts no context validity. -/
def rawFrameJson (originalDeclarations : List LocalDecl) (sourceTerm sourceType : Expr)
    (limits : RawJsonLimits := {}) : Except String Json :=
  runRaw limits do
    let mut declarations := #[]
    for declaration in originalDeclarations do
      declarations := declarations.push (← rawLocalDeclaration 2 declaration)
    let schema ← textJson 1 "definograph.raw-frame.v1"
    charge 1 1
    objectJson 0 [("schema", schema), ("naturalProfile", toJson (2 : Nat)),
      ("originalDeclarations", ← arrayJson 1 declarations),
      ("sourceTerm", ← rawExpr 1 sourceTerm), ("sourceType", ← rawExpr 1 sourceType)]

/-- Snapshot actual local declarations in chronological iteration order. No
ingestion, elaboration, resolution or kernel check is performed. -/
def captureRawFrame (sourceTerm sourceType : Expr) (limits : RawJsonLimits := {}) :
    MetaM (Except String Json) := do
  let original := (← getLCtx).foldl (fun declarations declaration => declaration :: declarations) []
  return rawFrameJson original.reverse sourceTerm sourceType limits

end Definograph
