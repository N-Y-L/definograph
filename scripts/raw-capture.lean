import SourceCapture

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace RawCaptureCorpus
open Lean Meta Definograph

private def require (result : Except String Json) : MetaM Json :=
  match result with
  | .ok value => pure value
  | .error reason => throwError "raw corpus serialization failed: {reason}"

private def labelled (label : String) (frame : Json) : Json :=
  Json.mkObj [("label", toJson label), ("frame", frame)]

private def slice (text : String) (start stop : Nat) : Substring.Raw :=
  ⟨text, ⟨start⟩, ⟨stop⟩⟩

private def syntaxValue (backing : String) : Syntax :=
  .node (.original (slice "α leading\n" 9007199254740993 1) ⟨9007199254740994⟩
      (slice "trailing α" 7 4) ⟨0⟩) (.num `kind 18446744073709551616)
    #[.missing, .atom .none "\n\t\"\\α",
      .atom (.synthetic ⟨8⟩ ⟨3⟩ true) "synthetic",
      .atom (.synthetic ⟨0⟩ ⟨1⟩ false) "noncanonical",
      .ident .none (slice backing 1 3) (.num `same 9007199254740993)
        [.namespace `same, .decl `same ["field", "field", "α"], .namespace `same]]

private def metadata (backing : String := "abcA") : MData := ⟨[
  (`duplicate, .ofString "first"), (`duplicate, .ofString "second"),
  (`boolean, .ofBool true), (`boolean, .ofBool false),
  (`name, .ofName (.num (.str .anonymous "1") 9007199254740993)),
  (`natural, .ofNat 18446744073709551616),
  (`integer, .ofInt (.ofNat 0)), (`integer, .ofInt (.ofNat 1)),
  (`integer, .ofInt (.ofNat 18446744073709551616)),
  (`integer, .ofInt (.negSucc 0)), (`integer, .ofInt (.negSucc 18446744073709551616)),
  (`syntax, .ofSyntax (syntaxValue backing))]⟩

private def add (frames : Array Json) (label : String) (term : Expr)
    (type : Expr := mkConst ``Nat) (declarations : List LocalDecl := []) : MetaM (Array Json) := do
  return frames.push (labelled label (← require (rawFrameJson declarations term type)))

def run : MetaM Unit := do
  let mut frames := #[]
  let huge := 9007199254740993
  let name := Name.num (.str .anonymous "same") huge
  let levels : List Level := [.zero, .succ .zero, .max (.param `u) (.succ .zero),
    .imax (.param `u) (.param (.num `u huge)), .mvar ⟨`unresolvedUniverse⟩]
  frames ← add frames "raw open bound reference" (.bvar 0)
  frames ← add frames "raw unregistered free reference" (.fvar ⟨name⟩)
  frames ← add frames "raw term metavariable" (.mvar ⟨name⟩)
  frames ← add frames "raw sort with universe metavariable" (.sort (.mvar ⟨name⟩)) (.sort (.succ .zero))
  frames ← add frames "all universe constructors and exact numeric names" (.const name levels)
  frames ← add frames "ordered higher-order application" (.app (.app (.fvar ⟨`function⟩) (.fvar ⟨`first⟩)) (.fvar ⟨`second⟩))
  for info in ([.default, .implicit, .strictImplicit, .instImplicit] : List BinderInfo) do
    let label := (binderJson info).getStr?.toOption.getD "unknown"
    frames ← add frames ("lambda binder " ++ label) (.lam name (mkConst ``Nat) (.bvar 0) info)
    frames ← add frames ("forall binder " ++ label) (.forallE name (mkConst ``Nat) (mkConst ``Nat) info) (.sort (.succ .zero))
  frames ← add frames "nested repeated-name binder scope" (.lam `same (mkConst ``Nat)
    (.lam `same (mkConst ``Nat) (.app (.bvar 1) (.bvar 0)) .default) .implicit)
  frames ← add frames "raw dangling bvar under binder" (.lam `same (mkConst ``Nat) (.bvar 1) .default)
  frames ← add frames "genuine owned let" (.letE name (mkConst ``Nat) (mkRawNatLit 1) (.bvar 0) false)
  frames ← add frames "owned have preserves value and flag" (.letE name (mkConst ``Nat)
    (.mdata (metadata "abcA") (mkRawNatLit 1)) (.bvar 0) true)
  frames ← add frames "exact natural literal" (mkRawNatLit 18446744073709551616)
  frames ← add frames "escaped UTF-8 literal" (.lit (.strVal "\n\t\"\\α")) (mkConst ``String)
  frames ← add frames "raw huge projection index" (.proj name huge (.mvar ⟨`unresolvedValue⟩))
  frames ← add frames "all metadata syntax and source-position constructors" (.mdata (metadata "abcA")
    (.mdata {} (.mvar ⟨`unresolvedTerm⟩)))
  frames ← add frames "same selected slice different backing string" (.mdata (metadata "xbcB")
    (.mdata {} (.mvar ⟨`unresolvedTerm⟩)))
  frames ← add frames "duplicate metadata entries reversed" (.mdata ⟨(metadata "abcA").entries.reverse⟩ (mkRawNatLit 0))
  let id : FVarId := ⟨name⟩
  let declarations : List LocalDecl := [
    .cdecl huge id `same (.sort (.mvar ⟨`u⟩)) .strictImplicit .auxDecl,
    .ldecl huge id `same (.fvar id) (.mdata (metadata "abcA") (.bvar 17)) true .implDetail,
    .ldecl 0 id `same (.mvar ⟨`type⟩) (.bvar 2) false .default]
  frames ← add frames "raw repeated LocalDecl indices names and FVar identities" (.mdata {} (.fvar id))
    (.mvar ⟨`type⟩) declarations
  let actual ← withLocalDecl `same .implicit (mkConst ``Nat) fun x =>
    withLetDecl `same (mkConst ``Nat) x fun seed =>
      withLetDecl `same (mkConst ``Nat) (.mdata (metadata "abcA") (.fvar ⟨`unregistered⟩))
          (nondep := true) fun opaqueValue => do
        let term := .app (.lam `same (mkConst ``Nat) (.bvar 0) .default) opaqueValue
        let _ := seed
        return labelled "actual local context with genuine let and opaque stored metadata"
          (← require (← captureRawFrame term (mkConst ``Nat)))
  frames := frames.push actual
  frames ← add frames "10000-digit natural boundary" (mkRawNatLit (10 ^ 9999))
  IO.println (Json.arr frames).compress

end RawCaptureCorpus

#eval RawCaptureCorpus.run
