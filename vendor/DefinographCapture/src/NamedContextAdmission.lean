import ComponentAdmission
import FVarCoreBridge

namespace DefinographAdmission
open Lean Meta DerivedViewSyntax V6Structured V6Compose

/-- Exact original LocalDecl values are retained separately from their closure.
    In particular, a nondep ldecl is abstracted as an assumption, as prescribed by
    Lean 4.28 LocalContext.lean. Its original opaque value is not used as a definition. -/
structure NamedContext where
  ids : List FVarId
  telescope : CTel ids.length
  original : List LocalDecl

def pushLocal (C : NamedContext) (d : LocalDecl) : Option NamedContext := do
  if C.ids.any (fun id => id.name == d.fvarId.name) then none else do
  let A ← FVarCoreBridge.reify C.ids d.type 0
  let next : CTel (d.fvarId :: C.ids).length ← match d with
    | .cdecl _ _ nm _ bi _ => pure (.port C.telescope ⟨nm, bi⟩ A)
    | .ldecl _ _ nm _ _ true _ => pure (.port C.telescope ⟨nm, .default⟩ A)
    | .ldecl _ _ nm _ value false _ => do
      let v ← FVarCoreBridge.reify C.ids value 0
      pure (.letE C.telescope nm false A v)
  return ⟨d.fvarId :: C.ids, next, C.original ++ [d]⟩

def ingestNamedContext (decls : List LocalDecl) : Option NamedContext :=
  decls.foldlM pushLocal ⟨[], .nil, []⟩

def captureLocalContext : MetaM (Option NamedContext) := do
  return ingestNamedContext ((← getLCtx).foldl (fun ds d => ds ++ [d]) [])

structure NamedComponent where
  context : NamedContext
  term : Core context.ids.length
  type : Core context.ids.length
  sourceTerm : Expr
  sourceType : Expr
  termReadback : FVarCoreBridge.decode context.ids 0 term = sourceTerm
  typeReadback : FVarCoreBridge.decode context.ids 0 type = sourceType

/-- Round-trip witnesses are proved by the existing constructor-total FVar bridge;
    declaration validity remains the subsequent kernel admission obligation. -/
def ingestNamedComponent (C : NamedContext) (term type : Expr) : Option NamedComponent :=
  match ht : FVarCoreBridge.reify C.ids term 0, hA : FVarCoreBridge.reify C.ids type 0 with
  | some t, some A => some ⟨C, t, A, term, type,
      (FVarCoreBridge.reify_readback C.ids term 0 t ht).2,
      (FVarCoreBridge.reify_readback C.ids type 0 A hA).2⟩
  | _, _ => none

def contextBound (C : NamedContext) : Bool :=
  match ingestNamedContext C.original with
  | none => false
  | some reconstructed =>
      C.ids == reconstructed.ids && coreEq
        (C.telescope.close (.const ``True []))
        (reconstructed.telescope.close (.const ``True []))

def checkNamedWith (run : Check) (nm : Name) (ls : List Name)
    (C : NamedComponent) : MetaM Checks := do
  unless contextBound C.context do
    throwError "named context does not match its original declaration identities, types and defining values"
  checkComponentWith run nm ls C.context.telescope C.term C.type

theorem named_readback (C : NamedComponent) :
    FVarCoreBridge.decode C.context.ids 0 C.term = C.sourceTerm ∧
    FVarCoreBridge.decode C.context.ids 0 C.type = C.sourceType :=
  ⟨C.termReadback, C.typeReadback⟩

#print axioms ingestNamedComponent
#print axioms named_readback
end DefinographAdmission
