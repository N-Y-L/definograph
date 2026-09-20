import Lean

open Lean

namespace StatementLens.Response

def unavailable (reason : String) : Json := Json.mkObj [
  ("provider", toJson "leantex"), ("status", toJson "unavailable"), ("reason", toJson reason)]

/-- Add-on notation must not turn an otherwise accepted semantic response into an
oversized response. Call after attaching the request ID; the limit includes its newline.
Mandatory fields are never removed, even if they exceed the existing transport limit. -/
def serializeResponse (response : Json) (maxBytes : Nat := 2 * 1024 * 1024) : String := Id.run do
  let full := response.compress
  if full.utf8ByteSize + 1 ≤ maxBytes then return full
  let .ok fields := response.getObj? | return full
  let isNotation := fun key => key == "readableMath" || key == "definitionReadableMath"
  let entries := fields.toList
  let limited := Json.mkObj (entries.map fun (key, value) =>
    (key, if isNotation key then unavailable "Notation omitted to preserve the semantic response size limit." else value))
  let compact := limited.compress
  if compact.utf8ByteSize + 1 ≤ maxBytes then return compact
  -- If even the small status records do not fit, omit the optional fields entirely.
  return (Json.mkObj (entries.filter fun (key, _) => !isNotation key)).compress

end StatementLens.Response
