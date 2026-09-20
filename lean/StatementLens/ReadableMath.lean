import LeanTeX.Builtins

/-! Optional, expression-based mathematical notation. These fixed display rules use exact
constant identities and do not inspect or rewrite source strings. Importing this module
does not import additional Mathlib modules or register any client-executable command. -/

open Lean LeanTeX

namespace StatementLens.ReadableMath

def unavailable (reason : String) : Json := Json.mkObj [
  ("provider", toJson "leantex"), ("status", toJson "unavailable"), ("reason", toJson reason)]

@[latex_pp const.Real] def realNotation : LatexPrinter := fun _ =>
  pure (LatexData.atomString "\\mathbb{R}")

@[latex_pp const.Rat] def rationalNotation : LatexPrinter := fun _ =>
  pure (LatexData.atomString "\\mathbb{Q}")

/-- Rendering errors, excessive input, or exhausted printing budgets never become
semantic analysis errors. Save/restore isolates printer metavariables and environment state. -/
def render (expression : Expr) : MetaM Json := do
  if expression.approxDepth > 64 || expression.sizeWithoutSharing > 2000 then
    return unavailable "This expression exceeds the optional notation printer size limit."
  let ctx ← readThe Core.Context
  let now ← IO.getNumHeartbeats
  let used := now - ctx.initHeartbeats
  let remaining := if ctx.maxHeartbeats == 0 then 20000000 else ctx.maxHeartbeats - used
  -- Leave a margin in the enclosing request's budget; this is optional presentation work.
  let budget := min 20000000 (remaining - 1000000)
  if budget < 1000 then return unavailable "No notation printing budget remains."
  let saved ← Meta.saveState
  try
    let latex ← withTheReader Core.Context (fun state =>
      { state with initHeartbeats := now, maxHeartbeats := budget, maxRecDepth := min state.maxRecDepth 128 }) do
      LeanTeX.run_latexPP expression {
        mathjaxTooltips := false, familySubscripts := false,
        omitBinders := false, implicationAssoc := false, displayStyle := true }
    if latex.length > 32768 || latex.utf8ByteSize > 65536 then
      return unavailable "The generated notation exceeds the display size limit."
    return Json.mkObj [
      ("provider", toJson "leantex"), ("status", toJson "rendered"), ("latex", toJson latex)]
  catch _ =>
    return unavailable "Readable notation is unavailable for this expression; the checked Lean statement remains available."
  finally
    saved.restore

end StatementLens.ReadableMath
