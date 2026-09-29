import InferComponent
import SourceHome

namespace DefinographAdmission
open Lean Meta DerivedViewSyntax V6Structured V6Compose OccurrenceDecomposition

/-- Both the complete input and the extracted home/component receive fresh
    source checks. The extraction itself carries a general exact rebuild proof.
    Newly generated FVar IDs are internal context reconstruction identities;
    source origin remains C, term, and the explicit occurrence path. -/
def checkExtractionWith (run : Check) (nm : Name) (ls : List Name)
    (C : CTel n) (term : Core n) (path : List OccurrenceDecomposition.Step) :
    MetaM (Option ((selected : SourceHome C term) × Core selected.extraction.home × Checks)) := do
  ensureSourceBasis (← getEnv) [contextExpr C, dec term]
  let some selected := extractSource C term path | return none
  let (_, rootChecks) ← checkOriginalWithInferredType run (nm ++ `root) ls C term
  let (type, componentChecks) ← checkOriginalWithInferredType run (nm ++ `selected) ls
    selected.telescope selected.extraction.component
  return some ⟨selected, type, rootChecks ++ componentChecks⟩

end DefinographAdmission
