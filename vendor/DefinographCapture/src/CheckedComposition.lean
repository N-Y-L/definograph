import CheckSupport

set_option autoImplicit false
set_option maxRecDepth 8192

namespace V6Compose
open Lean Meta DerivedViewSyntax V6BinderShared V6Structured
open ContextualViewDAG (Table Occ Args Row Ref RefMap)

/-- Lambda closure of a Core telescope. -/
def ctelLam : {k : Nat} → CTel k → Core k → Core 0
  | _, .nil, b => b
  | _, .port C x d, b => ctelLam C (.lam x d b)
  | _, .letE C nm nd ty v, b => ctelLam C (.letE nm nd ty v b)

/-- A closed Core term seen at arity `m`. -/
def wk0 {m : Nat} (t : Core 0) : Core m := rename (fun i => Fin.elim0 i) t

/-- The declared type of port `j` of a map interface, at the arity of all six ports. -/
def portDom (l : Lv3) : Fin 6 → Core 6
  | ⟨0, _⟩ => mapTy 5 4 3
  | ⟨1, _⟩ => opTy 5 3
  | ⟨2, _⟩ => opTy 5 4
  | ⟨3, _⟩ => famTy 5 l.y
  | ⟨4, _⟩ => famTy 5 l.x
  | _ => .sort (.succ l.u)

/-- The universe of `portDom l j`. -/
def portSort (l : Lv3) : Fin 6 → ULevel
  | ⟨0, _⟩ => .imax (.succ l.u) (.imax (.succ l.x) (.succ l.y))
  | ⟨1, _⟩ => .imax (.succ l.u) (.imax (.succ l.y) (.imax (.succ l.y) (.succ l.y)))
  | ⟨2, _⟩ => .imax (.succ l.u) (.imax (.succ l.x) (.imax (.succ l.x) (.succ l.x)))
  | ⟨3, _⟩ => .imax (.succ l.u) (.succ (.succ l.y))
  | ⟨4, _⟩ => .imax (.succ l.u) (.succ (.succ l.x))
  | _ => .succ (.succ l.u)

def kDecide (tl : TRef) (hb : Nat) (decl : Declaration) : MetaM KOut := do
  tl.modify fun t => { t with kernelCalls := t.kernelCalls + 1 }
  match ← kernelCall hb decl with
  | .ok env' =>
    setEnv env'
    tl.modify fun t => { t with accepted := t.accepted + 1 }
    return .accepted
  | .error (.declTypeMismatch ..) =>
    tl.modify fun t => { t with notConvertible := t.notConvertible + 1 }
    return .notConvertible
  | .error .deterministicTimeout =>
    tl.modify fun t => { t with unknown := t.unknown + 1 }
    return .unknown s!"timeout: the kernel reached the heartbeat bound {hb}"
  | .error e =>
    let kind? : Option String := match e with
      | .funExpected .. => some "funExpected"
      | .typeExpected .. => some "typeExpected"
      | .letTypeMismatch .. => some "letTypeMismatch"
      | .exprTypeMismatch .. => some "exprTypeMismatch"
      | .appTypeMismatch .. => some "appTypeMismatch"
      | .invalidProj .. => some "invalidProj"
      | _ => none
    match kind? with
    | some k =>
      tl.modify fun t => { t with typeErrors := t.typeErrors + 1 }
      return .typeError k
    | none =>
      tl.modify fun t => { t with unknown := t.unknown + 1 }
      return .unknown (← (e.toMessageData {}).toString)

def kAccepted : KOut → Bool
  | .accepted => true
  | _ => false

def kUnknown : KOut → Bool
  | .unknown _ => true
  | _ => false

def expectUnknown (tl : TRef) (k : KOut) (what : String) : MetaM Unit :=
  ensure tl (kUnknown k) s!"{what}: expected unknown, got {k.str}"

/-! ### The verdict -/

inductive Formation where
  | unsupported (what : String)
  | refused (reasons : List String)
  | rejected (check : String) (k : KOut)
  | unknown (check : String) (msg : String)
  | formed

inductive EvStatus where
  | notFormed
  | missing
  | rejected (check : String) (k : KOut)
  | unknown (check : String) (msg : String)
  | certified

def Formation.str : Formation → String
  | .unsupported w => s!"unsupported ({w})"
  | .refused rs => s!"refused ({"; ".intercalate rs})"
  | .rejected c k => s!"rejected at {c}: {k.str}"
  | .unknown c msg => s!"unknown at {c} ({msg})"
  | .formed => "formed"

def EvStatus.str : EvStatus → String
  | .notFormed => "not formed"
  | .missing => "missing (no evidence for both inputs; the statement is formed, not certified)"
  | .rejected c k => s!"rejected at {c}: {k.str}"
  | .unknown c msg => s!"unknown at {c} ({msg})"
  | .certified => "certified by the generic proof at the recorded universe instance"

structure Report where
  formation : Formation
  evidence : EvStatus
  checks : Array (String × KOut) := #[]

def Report.formed (r : Report) : Bool := match r.formation with | .formed => true | _ => false
def Report.certified (r : Report) : Bool := match r.evidence with | .certified => true | _ => false
def Report.missing (r : Report) : Bool := match r.evidence with | .missing => true | _ => false
def Report.evRejected (r : Report) : Bool := match r.evidence with | .rejected .. => true | _ => false
def Report.refused (r : Report) : Bool := match r.formation with | .refused _ => true | _ => false
def Report.unsupported (r : Report) : Bool := match r.formation with | .unsupported _ => true | _ => false
def Report.unknown (r : Report) : Bool := match r.formation with | .unknown .. => true | _ => false
def Report.rejected (r : Report) : Bool := match r.formation with | .rejected .. => true | _ => false
def Report.check (r : Report) (c : String) : Option KOut := (r.checks.find? (·.1 == c)).map (·.2)

/-- The admission conjuncts, named, for the log (the operation itself uses `midB`). -/
def midReasons (B : Bank) {m : Nat} (ctx : OTel B.homes m) (F G : MapIn B.homes m) : List (String × Bool) :=
  [("the instance context's lets are genuine", ctx.admitB),
   ("the rule's universe instance is the pair's", B.l == ⟨F.lv.u, F.lv.x, F.lv.y, G.lv.y⟩),
   ("index universe levels agree", G.lv.u == F.lv.u),
   ("middle carrier universe levels agree", G.lv.x == F.lv.y),
   ("same index type", coreEq (ev B.table (G.ports.get 5)) (ev B.table (F.ports.get 5))),
   ("same middle carrier", coreEq (ev B.table (G.ports.get 4)) (ev B.table (F.ports.get 3))),
   ("same middle operation (G's source operation is F's target operation)",
      coreEq (ev B.table (G.ports.get 2)) (ev B.table (F.ports.get 1))),
   ("F's routes are exact or class B at the shared operation", F.routesB B.table 1),
   ("G's routes are exact or class B at the shared operation", G.routesB B.table 2)]

def portNames : Array String := #["φ", "μY", "μX", "Y", "X", "I"]
def compNames : Array String := #["g", "f", "μC", "μB", "μA", "C", "B", "A", "I"]

/-- The kernel checks of a formed composite. `nm` is the hierarchical prefix of the declarations. -/
def checkFormedWith (run : String → Declaration → MetaM KOut) (nm : Name) (ls : List Name)
    (B : Bank) (K : Comp B) : MetaM Report := do
  let tb := B.table
  let items := K.ctx.items tb
  let ctxAll (b : Expr) := closeForall items b
  let lamAll (b : Expr) := closeLam items b
  let mut checks : Array (String × KOut) := #[]
  let mut formation : Formation := .formed
  -- 1. the instance context
  let k1 ← run "context" (thmD (nm ++ `context) (ctxAll (mkConst ``True)) (lamAll (mkConst ``True.intro)) ls)
  checks := checks.push ("context", k1)
  -- 2. each map's ports against the interface, and the composite vector against its interface
  let iface (lv : Lv3) (ports : Args B.homes K.m 6) : Core K.m :=
    appArgs (wk0 (ctelLam (mapTel lv) (lawSrc lv))) 6 (fun j => evA tb ports ⟨5 - j.val, by omega⟩)
  let kF ← run "F.interface" (defD (nm ++ `F ++ `interface) (ctxAll (mkSort .zero)) (lamAll (dec (iface K.F.lv K.F.ports))) ls)
  let kG ← run "G.interface" (defD (nm ++ `G ++ `interface) (ctxAll (mkSort .zero)) (lamAll (dec (iface K.G.lv K.G.ports))) ls)
  let σ := evA tb K.σ
  let compI : Core K.m := appArgs (wk0 (ctelLam (compTel B.l) (phT B.l))) 9 (fun j => σ ⟨8 - j.val, by omega⟩)
  let kC ← run "composite.interface" (defD (nm ++ `composite ++ `interface) (ctxAll (mkSort .zero)) (lamAll (dec compI)) ls)
  checks := checks ++ #[("F.interface", kF), ("G.interface", kG), ("composite.interface", kC)]
  -- 3. class B routes, each with its recorded universe instance
  for (who, P, pnm) in [("F", K.F, `F), ("G", K.G, `G)] do
    for j in List.finRange 6 do
      match (P.certs j).base with
      | .exact => pure ()
      | .classB cn k acts =>
        let T := subst (evA tb P.ports) (portDom P.lv j)
        let lvl := CoreExprBridge.decodeLevel (portSort P.lv j)
        let stmt := ctxAll (mkApp3 (mkConst ``Eq [lvl]) (dec T) (dec (evA tb P.srcPorts j)) (dec (evA tb P.ports j)))
        let pf := lamAll (dec (appArgs (.const cn (P.certs j).lvls) k (evA tb acts)))
        let kr ← run s!"{who}.route[{portNames[j.val]!}]"
          (thmD (nm ++ pnm ++ Name.mkSimple s!"route{j.val}") stmt pf ls)
        checks := checks.push (s!"{who}.route", kr)
  -- 4. the kept input laws and the derived law are propositions; reading, source and view convert
  let tyChk (label : String) (n : Name) (t : Core 0) : MetaM KOut := run label (defD n (mkSort .zero) (dec t) ls)
  let eqChk (label : String) (n : Name) (a b : Core 0) : MetaM KOut := run label (thmD n (eqProp (dec a) (dec b)) (reflProp (dec a)) ls)
  let L := K.lawsIn
  let D := K.law
  let a1 ← tyChk "laws.source is a proposition" (nm ++ `laws ++ `source) L.source
  let a2 ← tyChk "laws.view is a proposition" (nm ++ `laws ++ `view) L.view
  let a3 ← tyChk "laws.reading is a proposition" (nm ++ `laws ++ `reading) L.reading
  let a4 ← eqChk "laws.reading = laws.source" (nm ++ `laws ++ `reading_eq_source) L.reading L.source
  let a5 ← eqChk "laws.view = laws.source" (nm ++ `laws ++ `view_eq_source) L.view L.source
  let b1 ← tyChk "law.source is a proposition" (nm ++ `law ++ `source) D.source
  let b2 ← tyChk "law.reading is a proposition" (nm ++ `law ++ `reading) D.reading
  let b3 ← eqChk "law.reading = law.source" (nm ++ `law ++ `reading_eq_source) D.reading D.source
  checks := checks ++ #[("laws.source", a1), ("laws.view", a2), ("laws.reading", a3), ("laws.reading=source", a4),
    ("laws.view=source", a5), ("law.source", b1), ("law.reading", b2), ("law.reading=source", b3)]
  for (c, k) in checks do
    match formation with
    | .formed =>
      match k with
      | .accepted => pure ()
      | .unknown msg => formation := .unknown c msg
      | _ => formation := .rejected c k
    | _ => pure ()
  -- 5. evidence: each input's own evidence against its exact source law, then the composite
  let mut evidence : EvStatus := if formation matches .formed then .missing else .notFormed
  let mut inputsOk := true
  for (who, P, pnm) in [("F", K.F, `F), ("G", K.G, `G)] do
    if let some (_, o) := P.ev then
      let ke ← run s!"{who}.evidence (its exact source law)"
        (thmD (nm ++ pnm ++ `evidence) (ctxAll (dec (P.srcLaw tb))) (lamAll (dec (ev tb o))) ls)
      checks := checks.push (s!"{who}.evidence", ke)
      unless kAccepted ke do
        inputsOk := false
        if evidence matches .missing then
          evidence := match ke with
            | .unknown msg => .unknown s!"{who}.evidence" msg
            | _ => .rejected s!"{who}.evidence" ke
  if let some c := K.ev then
    if formation matches .formed then
      if inputsOk then
        match c.term tb with
        | some t =>
          let kc ← run "certificate (generic proof applied)" (thmD (nm ++ `certificate) (dec D.source) (lamAll (dec t)) ls)
          checks := checks.push ("certificate", kc)
          evidence := match kc with
            | .accepted => .certified
            | .unknown msg => .unknown "certificate" msg
            | _ => .rejected "certificate" kc
        | none => evidence := .rejected "certificate" (.typeError "no proof term")
  return { formation, evidence, checks }


/-- Uninstrumented reference entry point, using the same ordered checker. -/
def checkFormed (tl : TRef) (nm : Name) (ls : List Name) (hb : Nat)
    (B : Bank) (K : Comp B) : MetaM Report :=
  checkFormedWith (fun _ d => kDecide tl hb d) nm ls B K

end V6Compose
