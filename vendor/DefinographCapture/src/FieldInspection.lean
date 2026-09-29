import HeadExposure

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Definograph
open Lean Meta DerivedViewSyntax V6Structured V6Compose DefinographAdmission

/-- Only the signature is needed to apply a projector. Proof-valued projectors
are theorems; their proof bodies are neither unfolded nor copied into the trace. -/
structure FieldProjectorDeclaration where
  kind : String
  name : Name
  levelParams : List Name
  type : Expr
  deriving Inhabited

structure DirectFieldEntry where
  index : Nat
  name : Name
  projector : Name
  binderInfo : BinderInfo
  parent : Option Name
  projectionInfo : ProjectionFunctionInfo
  declaration : FieldProjectorDeclaration
  deriving Inhabited

structure DirectFieldCatalogue (n : Nat) where
  structureVal : InductiveVal
  constructorVal : ConstructorVal
  actualLevels : List ULevel
  parameters : Array (Core n)
  fields : Array DirectFieldEntry

structure DirectFieldCandidate (n : Nat) where
  field : DirectFieldEntry
  named : Core n
  primitive : Core n
  type : Core n
  carrierSort : ULevel

private def refuse (phase reason : String) : HeadExposureFailure :=
  ⟨"unsupported", phase, reason⟩

private def boundedCount (count maximum : Nat) (what : String) : Except HeadExposureFailure Unit := do
  if count > maximum then throw ⟨"limit", "field-metadata", what ++ " exceeds the metadata limit"⟩

private def checkName (limits : HeadExposureLimits) (name : Name) : Except HeadExposureFailure Unit :=
  checkHeadExposureExpressions limits [] [(0, .const name [])]

private def signature (limits : HeadExposureLimits) (value : ConstantVal) : Except HeadExposureFailure Unit := do
  checkName limits value.name
  boundedCount value.levelParams.length 128 "formal universe count"
  let mut seen : NameSet := {}
  for name in value.levelParams do
    checkName limits name
    if name == .anonymous || seen.contains name then
      throw (refuse "field-universes" "Formal universe names must be distinct and nonempty.")
    seen := seen.insert name
  checkHeadExposureExpressions limits value.levelParams [(0, value.type)]

private def exactCore (value : Expr) (arity : Nat) : Except HeadExposureFailure (Core arity) :=
  match CoreExprBridge.reify value arity with
  | some value => .ok value
  | none => .error (refuse "field-profile" "The field expression is outside the exact finished profile.")

/-- Read only direct metadata for a literal fully applied owner type. In
particular this does not weak-head normalize the type or search parent fields. -/
private def buildDirectFieldCatalogue {n : Nat} (initial : Environment) (allowed : List Name)
    (type : Core n) (limits : HeadExposureLimits) : Except HeadExposureFailure (DirectFieldCatalogue n) := do
  checkHeadExposureExpressions limits allowed [(n, dec type)]
  let expression := dec type
  let .const name levels := expression.getAppFn
    | throw (refuse "field-owner" "The owner type is not a literal fully applied structure constant.")
  let some metadata := getStructureInfo? initial name
    | throw (refuse "field-owner" "The owner type has no registered direct structure fields.")
  let some (.inductInfo structureVal) := initial.find? name
    | throw (refuse "field-metadata" "The registered structure has no initial inductive declaration.")
  unless metadata.structName == name && !structureVal.isUnsafe && !structureVal.isRec &&
      !structureVal.isReflexive && structureVal.numIndices == 0 && structureVal.numNested == 0 &&
      structureVal.all == [name] do
    throw (refuse "field-owner" "Only safe nonrecursive, nonindexed single structures are supported.")
  let [constructorName] := structureVal.ctors
    | throw (refuse "field-owner" "The structure must have exactly one constructor.")
  let some (.ctorInfo constructorVal) := initial.find? constructorName
    | throw (refuse "field-metadata" "The structure constructor is absent from the initial environment.")
  boundedCount structureVal.numParams 128 "structure parameter count"
  boundedCount constructorVal.numFields 65536 "direct field count"
  boundedCount metadata.fieldNames.size 65536 "field name count"
  boundedCount metadata.fieldInfo.size 65536 "field descriptor count"
  unless !constructorVal.isUnsafe && constructorVal.induct == name && constructorVal.cidx == 0 &&
      constructorVal.numParams == structureVal.numParams &&
      constructorVal.levelParams == structureVal.levelParams &&
      constructorVal.numFields == metadata.fieldNames.size &&
      metadata.fieldInfo.size == metadata.fieldNames.size do
    throw (refuse "field-metadata" "Structure, constructor and direct field metadata disagree.")
  unless levels.length == structureVal.levelParams.length && expression.getAppArgs.size == structureVal.numParams do
    throw (refuse "field-owner" "The structure's actual universe or parameter count does not match its declaration.")
  signature limits structureVal.toConstantVal
  signature limits constructorVal.toConstantVal
  -- Validate the two metadata orderings separately before binary name lookup.
  let mut names : NameSet := {}
  for fieldName in metadata.fieldNames do
    checkName limits fieldName
    let .str .anonymous text := fieldName
      | throw (refuse "field-metadata" "A direct field name is not a single-component name.")
    if text.isEmpty || names.contains fieldName then
      throw (refuse "field-metadata" "Direct field names must be nonempty and unique.")
    names := names.insert fieldName
  let mut previous : Option Name := none
  for info in metadata.fieldInfo do
    checkName limits info.fieldName
    unless names.contains info.fieldName && (previous.all fun p => Name.quickLt p info.fieldName) do
      throw (refuse "field-metadata" "The sorted direct-field metadata does not match its constructor-order names.")
    previous := some info.fieldName
  let mut parameters := #[]
  for parameter in expression.getAppArgs do
    parameters := parameters.push (← exactCore parameter n)
  let mut actualLevels := []
  for level in levels do
    let .sort value ← exactCore (.sort level) 0
      | throw (refuse "field-universes" "Invalid structure universe argument.")
    actualLevels := value :: actualLevels
  let mut fields := #[]
  for index in [:min constructorVal.numFields 16] do
    let fieldName := metadata.fieldNames[index]!
    let some info := getFieldInfo? initial name fieldName
      | throw (refuse "field-metadata" "A direct field descriptor is absent.")
    checkName limits fieldName
    checkName limits info.projFn
    let some projectionInfo := initial.getProjectionFnInfo? info.projFn
      | throw (refuse "field-metadata" "A direct projector registration is absent.")
    unless projectionInfo.ctorName == constructorName && projectionInfo.numParams == structureVal.numParams &&
        projectionInfo.i == index do
      throw (refuse "field-metadata" "A named projector does not match its direct constructor field.")
    let declaration ← match initial.find? info.projFn with
      | some (.defnInfo value) =>
        if value.safety != .safe then throw (refuse "field-projector" "Unsafe or partial field projectors are unsupported.")
        pure (FieldProjectorDeclaration.mk "defnDecl" value.name value.levelParams value.type)
      | some (.thmInfo value) => pure (FieldProjectorDeclaration.mk "thmDecl" value.name value.levelParams value.type)
      | _ => throw (refuse "field-projector" "The direct projector is not an initial safe definition or theorem.")
    unless declaration.levelParams == structureVal.levelParams do
      throw (refuse "field-universes" "Projector and structure formal universe order differ.")
    signature limits ⟨declaration.name, declaration.levelParams, declaration.type⟩
    if let some parent := info.subobject? then
      checkName limits parent
      unless (getStructureInfo? initial parent).isSome do
        throw (refuse "field-metadata" "An embedded parent is not an initial registered structure.")
      let some (.inductInfo _) := initial.find? parent
        | throw (refuse "field-metadata" "An embedded parent declaration is absent.")
    fields := fields.push ⟨index, fieldName, info.projFn, info.binderInfo, info.subobject?, projectionInfo, declaration⟩
  return ⟨structureVal, constructorVal, actualLevels.reverse, parameters, fields⟩

def prepareDirectFieldCatalogue {n : Nat} (initial : Environment) (allowed : List Name)
    (C : CTel n) (term type : Core n) (limits : HeadExposureLimits := {}) :
    MetaM (Except HeadExposureFailure (DirectFieldCatalogue n)) := do
  if n > 128 then return .error ⟨"limit", "field-context", "The owner context exceeds128 entries."⟩
  ensureSourceBasis initial [contextExpr C, dec term, dec type]
  match checkHeadExposureExpressions limits allowed [(0, contextExpr C), (n, dec term)] with
  | .error reason => return .error reason
  | .ok _ => pure ()
  let catalogue ← match buildDirectFieldCatalogue initial allowed type limits with
    | .error reason => return .error reason
    | .ok catalogue => pure catalogue
  ensureSourceBasis initial [catalogue.structureVal.type, catalogue.constructorVal.type]
  for field in catalogue.fields do ensureSourceBasis initial [field.declaration.type]
  return .ok catalogue

def prepareDirectField {n : Nat} (initial : Environment) (allowed : List Name)
    (C : CTel n) (term type : Core n) (index : Nat) (limits : HeadExposureLimits := {}) :
    MetaM (Except HeadExposureFailure (DirectFieldCandidate n)) := do
  let catalogue ← match ← prepareDirectFieldCatalogue initial allowed C term type limits with
    | .error reason => return .error reason
    | .ok value => pure value
  let some field := catalogue.fields[index]?
    | return .error (refuse "field-index" "The field index is not in the retained direct-field prefix.")
  let mut named : Core n := .const field.projector catalogue.actualLevels
  for parameter in catalogue.parameters do named := .app named parameter
  named := .app named term
  let primitive : Core n := .proj catalogue.structureVal.name index term
  match checkHeadExposureExpressions limits allowed [(n, dec named), (n, dec primitive)] with
  | .error reason => return .error reason
  | .ok _ => pure ()
  let inferred ← inferredTypeAt C named
  let .sort carrierSort ← inferredTypeAt C inferred
    | return .error (refuse "field-carrier" "The projected type's inferred type is not a literal Sort.")
  ensureSourceBasis initial [dec named, dec primitive, dec inferred, .sort (CoreExprBridge.decodeLevel carrierSort)]
  return (checkHeadExposureExpressions limits allowed [(n, dec inferred), (0, .sort (CoreExprBridge.decodeLevel carrierSort))]).map
    fun _ => ⟨field, named, primitive, inferred, carrierSort⟩

def directFieldConversion {n : Nat} (declarationPrefix : Name) (params : List Name)
    (C : CTel n) (candidate : DirectFieldCandidate n) : Declaration :=
  let level := CoreExprBridge.decodeLevel candidate.carrierSort
  thmD (declarationPrefix ++ `project.conversion)
    (closeForall (CTel.items C) (mkApp3 (mkConst ``Eq [level])
      (dec candidate.type) (dec candidate.named) (dec candidate.primitive)))
    (closeLam (CTel.items C) (mkApp2 (mkConst ``Eq.refl [level])
      (dec candidate.type) (dec candidate.named))) params

def directFieldEntryJson (field : DirectFieldEntry) : Except String Json := do
  return Json.mkObj [("index", toJson field.index), ("name", nameJson field.name),
    ("projector", nameJson field.projector), ("binderInfo", binderJson field.binderInfo),
    ("parent", field.parent.map nameJson |>.getD .null),
    ("projectionInfo", Json.mkObj [("ctorName", nameJson field.projectionInfo.ctorName),
      ("numParams", toJson field.projectionInfo.numParams), ("index", toJson field.projectionInfo.i),
      ("fromClass", toJson field.projectionInfo.fromClass)]),
    ("declaration", Json.mkObj [("kind", toJson field.declaration.kind), ("name", nameJson field.declaration.name),
      ("levelParams", arr (field.declaration.levelParams.map nameJson)),
      ("type", ← exprJson field.declaration.type), ("safety", toJson "safe")])]

def directFieldCatalogueJson {n : Nat} (catalogue : DirectFieldCatalogue n) : Except String Json := do
  let s := catalogue.structureVal
  let c := catalogue.constructorVal
  return Json.mkObj [
    ("structure", Json.mkObj [("name", nameJson s.name), ("levelParams", arr (s.levelParams.map nameJson)),
      ("type", ← exprJson s.type), ("numParams", toJson s.numParams), ("numIndices", toJson s.numIndices),
      ("isRec", toJson s.isRec), ("isUnsafe", toJson s.isUnsafe), ("constructor", nameJson c.name)]),
    ("constructor", Json.mkObj [("name", nameJson c.name), ("levelParams", arr (c.levelParams.map nameJson)),
      ("type", ← exprJson c.type), ("induct", nameJson c.induct), ("cidx", toJson c.cidx),
      ("numParams", toJson c.numParams), ("numFields", toJson c.numFields), ("isUnsafe", toJson c.isUnsafe)]),
    ("actualLevels", arr (catalogue.actualLevels.map ulevelJson)),
    ("parameters", Json.arr (← catalogue.parameters.mapM fun p => exprJson (dec p))),
    ("fields", Json.arr (← catalogue.fields.mapM directFieldEntryJson)),
    ("omittedFields", toJson (c.numFields - catalogue.fields.size))]

end Definograph
