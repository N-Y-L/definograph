import Lean

open Lean

namespace StatementLens.Response

def unavailable (reason : String) : Json := Json.mkObj [
  ("provider", toJson "leantex"), ("status", toJson "unavailable"), ("reason", toJson reason)]

/-- Optional decomposition is repeated in the tree and its expression. Remove it
    recursively when the aggregate transport budget would otherwise reject the
    checked statement. Keep a small status on affected binder records. -/
partial def withoutStructureViews : Json → Json
  | .arr values => .arr (values.map withoutStructureViews)
  | .obj fields =>
    let entries := fields.toList
    let hasStructure := entries.any fun (key, _) => key == "structure"
    let kept := entries.filterMap fun (key, value) =>
      if key == "structure" || key == "typeExpansion" then none else some (key, withoutStructureViews value)
    Json.mkObj (kept ++ if hasStructure then [("structureOmission", toJson "Structure details omitted to preserve the semantic response size limit.")] else [])
  | other => other

/-- Add-on notation must not turn an otherwise accepted semantic response into an
oversized response. Call after attaching the request ID; the limit includes its newline.
Mandatory fields are never removed, even if they exceed the existing transport limit. -/
def serializeResponse (response : Json) (maxBytes : Nat := 2 * 1024 * 1024) : String := Id.run do
  let full := response.compress
  if full.utf8ByteSize + 1 ≤ maxBytes then return full
  let .ok fields := response.getObj? | return full
  let isNotation := fun key => key == "readableMath" || key == "definitionReadableMath" || key == "definitionPreviews"
  let entries := fields.toList
  let limited := Json.mkObj (entries.map fun (key, value) =>
    (key, if key == "definitionPreviews" then Json.arr #[] else if isNotation key then unavailable "Notation omitted to preserve the semantic response size limit." else value))
  let compact := limited.compress
  if compact.utf8ByteSize + 1 ≤ maxBytes then return compact
  let withoutStructures := withoutStructureViews limited
  let minimal := withoutStructures.compress
  if minimal.utf8ByteSize + 1 ≤ maxBytes then return minimal
  -- If even the small status records do not fit, omit the optional fields entirely.
  return (withoutStructureViews (Json.mkObj (entries.filter fun (key, _) => !isNotation key))).compress

end StatementLens.Response
