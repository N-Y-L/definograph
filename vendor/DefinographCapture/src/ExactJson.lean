import CompositionBase

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Definograph
open Lean DerivedViewSyntax V6BinderShared V6Structured V6Compose
open ContextualViewDAG (Table Occ Args Row Ref)

def arr (xs : List Json) : Json := .arr xs.toArray
def tag (s : String) (xs : List Json := []) : Json := arr (toJson s :: xs)

/-- Version 2 preserves every semantic natural as canonical decimal text,
including small values. Finite operational positions remain JSON numbers. -/
def exactNatJson (n : Nat) : Json := tag "nat" [toJson (toString n)]

def exactNaturalMaxDigits : Nat := 10000

/-- Pure encoders retain every digit. Capture/output boundaries separately refuse
values beyond the supported transport budget, before emitting any packet text. -/
partial def checkExactNaturalBudget (value : Json) : Except String Unit := do
  match value with
  | .arr values =>
    if values.size == 2 && values[0]! == toJson "nat" then
      if let .ok digits := values[1]!.getStr? then
        if digits.length > exactNaturalMaxDigits then
          throw "exact natural exceeds the 10000-digit transport limit"
    for child in values do checkExactNaturalBudget child
  | .obj fields =>
    for (_, child) in fields.toList do checkExactNaturalBudget child
  | _ => pure ()

def nameJson : Name → Json
  | .anonymous => tag "anonymous"
  | .str p s => tag "str" [nameJson p, toJson s]
  | .num p n => tag "num" [nameJson p, exactNatJson n]

def levelJson : Level → Json
  | .zero => tag "zero"
  | .succ u => tag "succ" [levelJson u]
  | .max u v => tag "max" [levelJson u, levelJson v]
  | .imax u v => tag "imax" [levelJson u, levelJson v]
  | .param n => tag "param" [nameJson n]
  | .mvar n => tag "mvar" [nameJson n.name]

def ulevelJson (u : ULevel) : Json := levelJson (CoreExprBridge.decodeLevel u)
def binderJson : BinderInfo → Json
  | .default => toJson "default"
  | .implicit => toJson "implicit"
  | .strictImplicit => toJson "strictImplicit"
  | .instImplicit => toJson "instImplicit"

def attrsJson (a : BinderAttrs) : Json :=
  Json.mkObj [("name", nameJson a.name), ("info", binderJson a.info)]

def uniqueJson (a : UniqueAttrs) : Json := Json.mkObj
  [("u", ulevelJson a.u), ("v", ulevelJson a.v), ("x", attrsJson a.x),
   ("yName", nameJson a.yName), ("yNondep", toJson a.yNondep),
   ("a", attrsJson a.a), ("b", attrsJson a.b), ("z", attrsJson a.z), ("h", attrsJson a.h)]

def literalJson : Literal → Json
  | .natVal n => tag "natVal" [exactNatJson n]
  | .strVal s => tag "strVal" [toJson s]

/-- Exact constructor encoding for this worker's normalized declaration profile.
Unsupported metadata aborts capture before the declaration reaches the kernel. -/
def exprJson : Expr → Except String Json
  | .bvar n => pure (tag "bvar" [exactNatJson n])
  | .fvar n => pure (tag "fvar" [nameJson n.name])
  | .mvar n => pure (tag "mvar" [nameJson n.name])
  | .sort l => pure (tag "sort" [levelJson l])
  | .const n ls => pure (tag "const" [nameJson n, arr (ls.map levelJson)])
  | .app f a => return tag "app" [← exprJson f, ← exprJson a]
  | .lam n t b bi => return tag "lam" [nameJson n, ← exprJson t, ← exprJson b, binderJson bi]
  | .forallE n t b bi => return tag "forallE" [nameJson n, ← exprJson t, ← exprJson b, binderJson bi]
  | .letE n t v b nd => return tag "letE" [nameJson n, ← exprJson t, ← exprJson v, ← exprJson b, toJson nd]
  | .lit l => pure (tag "lit" [literalJson l])
  | .proj n i v => return tag "proj" [nameJson n, exactNatJson i, ← exprJson v]
  | .mdata .. => .error "Expr.mdata is outside the normalized packet profile"

def hintsJson : ReducibilityHints → Json
  | .abbrev => tag "abbrev"
  | .opaque => tag "opaque"
  | .regular n => tag "regular" [toJson n.toNat]

def safetyJson : DefinitionSafety → Json
  | .safe => toJson "safe"
  | .unsafe => toJson "unsafe"
  | .partial => toJson "partial"

private def declarationJsonCore : Declaration → Except String Json
  | .thmDecl d => do
    return Json.mkObj [("kind", toJson "thmDecl"), ("name", nameJson d.name),
      ("levelParams", arr (d.levelParams.map nameJson)), ("type", ← exprJson d.type),
      ("value", ← exprJson d.value), ("all", arr (d.all.map nameJson))]
  | .defnDecl d => do
    return Json.mkObj [("kind", toJson "defnDecl"), ("name", nameJson d.name),
      ("levelParams", arr (d.levelParams.map nameJson)), ("type", ← exprJson d.type),
      ("value", ← exprJson d.value), ("all", arr (d.all.map nameJson)),
      ("hints", hintsJson d.hints), ("safety", safetyJson d.safety)]
  | _ => .error "declaration kind is outside the theorem/definition packet profile"

def declarationJson (declaration : Declaration) : Except String Json := do
  let encoded ← declarationJsonCore declaration
  checkExactNaturalBudget encoded
  return encoded

mutual
  def occJson {Γ : List Nat} {n : Nat} : Occ Γ n → Json
    | .var i => tag "var" [toJson i.val]
    | @Occ.use _ _ r ref actuals => tag "use" [toJson ref.offset, toJson r, argsJson actuals]
  def argsJson {Γ : List Nat} {n r : Nat} : Args Γ n r → Json
    | .nil => tag "nil"
    | .cons first rest => tag "cons" [occJson first, argsJson rest]
end

def rowJson {Γ : List Nat} {n : Nat} : Row Γ n → Json
  | .var i => tag "var" [toJson i.val]
  | .sort u => tag "sort" [ulevelJson u]
  | .const nm ls => tag "const" [nameJson nm, arr (ls.map ulevelJson)]
  | .lit l => tag "lit" [literalJson l]
  | .app f a => tag "app" [occJson f, occJson a]
  | .lam x d b => tag "lam" [attrsJson x, occJson d, occJson b]
  | .pi x d b => tag "pi" [attrsJson x, occJson d, occJson b]
  | .letE nm nd t v b => tag "letE" [nameJson nm, toJson nd, occJson t, occJson v, occJson b]
  | .proj nm i v => tag "proj" [nameJson nm, exactNatJson i, occJson v]
  | .unique x a b s d r => tag "unique" [uniqueJson x, occJson a, occJson b, occJson s, occJson d, occJson r]
  | @Row.inst _ _ r b a => tag "inst" [toJson r, occJson b, argsJson a]

def tableRows {Γ : List Nat} : Table Γ → List Json
  | .empty => []
  | @Table.snoc _ n prior row => tableRows prior ++ [Json.mkObj [("home", toJson n), ("row", rowJson row)]]

def tableJson {Γ : List Nat} (t : Table Γ) : Json := Json.mkObj
  [("homes", toJson Γ), ("rows", arr (tableRows t))]

def ownerJson {Γ : List Nat} {n : Nat} : OTel Γ n → Json
  | .nil => tag "nil"
  | .port c a d => tag "port" [ownerJson c, attrsJson a, occJson d]
  | .letE c nm nd t v => tag "letE" [ownerJson c, nameJson nm, toJson nd, occJson t, occJson v]

def certJson {Γ : List Nat} {n : Nat} : CertR Γ n → Json
  | .exact => tag "exact"
  | .classB nm k a => tag "classB" [nameJson nm, toJson k, argsJson a]

def useJson {Γ : List Nat} {n e : Nat} (u : UseR Γ n e) : Json := Json.mkObj
  [("oid", exactNatJson u.oid), ("src", occJson u.src), ("view", occJson u.view),
   ("acts", argsJson u.acts), ("srcCert", certJson u.srcCert), ("viewCert", certJson u.viewCert)]

def templateJson {Γ : List Nat} {n e : Nat} : Tmpl Γ n e → Json
  | .leaf o => tag "leaf" [occJson o]
  | .hole u => tag "hole" [useJson u]
  | .app f a => tag "app" [templateJson f, templateJson a]
  | .pi a d b => tag "pi" [attrsJson a, occJson d, templateJson b]
  | .letE nm nd t v b => tag "letE" [nameJson nm, toJson nd, occJson t, occJson v, templateJson b]

def pathJson (p : List Step) : Json := arr (p.map fun s => toJson (match s with
  | .fn => "fn" | .arg => "arg" | .piBody => "piBody" | .letBody => "letBody"))

def scopeJson {Γ : List Nat} {n : Nat} : LB Γ n → Json
  | .pi e a d => tag "pi" [toJson e, attrsJson a, occJson d]
  | .letE e nm nd t v => tag "letE" [toJson e, nameJson nm, toJson nd, occJson t, occJson v]

def entryJson {Γ : List Nat} {n : Nat} (u : UseEntry Γ n) : Json := Json.mkObj
  [("e", toJson u.e), ("path", pathJson u.path), ("scope", arr (u.scope.map scopeJson)), ("use", useJson u.use)]

def levelsJson {Γ : List Nat} {n : Nat} (c : CertR Γ n) (ls : Option (List ULevel)) : Json :=
  match c with
  | .exact => Json.mkObj [("tag", toJson "notApplicable")]
  | .classB .. => match ls with
    | none => Json.mkObj [("tag", toJson "unavailable"), ("reason", toJson "no associated universe instance")]
    | some us => Json.mkObj [("tag", toJson "available"), ("values", arr (us.map ulevelJson))]

def memberJson {Γ : List Nat} {n : Nat} (u : UseEntry Γ n) (ls : Option (List ULevel)) : Json := Json.mkObj
  [("entry", entryJson u), ("sourceLevels", levelsJson u.use.srcCert ls), ("viewLevels", levelsJson u.use.viewCert ls)]

def recordJson (r : SRec) (ls : Nat → Option (List ULevel)) : Json := Json.mkObj
  [("homes", toJson r.homes), ("table", tableJson r.table), ("n", toJson r.n),
   ("owner", ownerJson r.owner), ("nodeName", nameJson r.nodeName), ("nodeTy", occJson r.nodeTy),
   ("sup", occJson r.sup), ("body", templateJson r.body),
   ("uses", arr (r.body.uses.map fun u => memberJson u (ls u.use.oid)))]

def lv3Json (l : Lv3) : Json := arr [ulevelJson l.u, ulevelJson l.x, ulevelJson l.y]
def lv4Json (l : Lv4) : Json := arr [ulevelJson l.u, ulevelJson l.a, ulevelJson l.b, ulevelJson l.c]

def certUJson {Γ : List Nat} {n : Nat} (c : CertU Γ n) : Json := Json.mkObj
  [("base", certJson c.base), ("levels", arr (c.lvls.map ulevelJson))]

def inputJson {Γ : List Nat} {n : Nat} (p : MapIn Γ n) : Json := Json.mkObj
  [("lv", lv3Json p.lv), ("ports", argsJson p.ports), ("srcPorts", argsJson p.srcPorts),
   ("certs", arr ((List.finRange 6).map fun j => certUJson (p.certs j))),
   ("ev", match p.ev with
      | none => .null
      | some (r, o) => Json.mkObj [
          ("role", toJson (match r with | .assumption => "assumption" | .proof => "proof")),
          ("occurrence", occJson o)])]

end Definograph
