import Lean

/- Structural serialization of actual Lean 4.28 Expr/Level syntax.
   No graph node stores Expr, Level, or List Level as a payload. -/
namespace ExprReferenceGraph
open Lean

inductive Kind where
  | expr | level | levels
  deriving DecidableEq

def Meaning : Kind → Type
  | .expr => Expr
  | .level => Level
  | .levels => List Level

-- A reference is an ordinal slot in an earlier finite instruction prefix.
-- Its index records only the syntactic result kind, not a Lean term type.
inductive Ref : List Kind → Kind → Type where
  | here : Ref (k :: Γ) k
  | there : Ref Γ k → Ref (j :: Γ) k

def Ref.offset : Ref Γ k → Nat
  | .here => 0
  | .there previous => previous.offset + 1

theorem Ref.offset_bounded (r : Ref Γ k) : r.offset < Γ.length := by
  induction r with
  | here => simp [Ref.offset]
  | there previous ih => simpa [Ref.offset] using Nat.succ_lt_succ ih

structure Values (Γ : List Kind) where
  get : {k : Kind} → Ref Γ k → Meaning k

instance : CoeFun (Values Γ) (fun _ => {k : Kind} → Ref Γ k → Meaning k) :=
  ⟨Values.get⟩

def pushValues (values : Values Γ) (value : Meaning k) : Values (k :: Γ) where
  get := fun {j} r =>
    match r with
    | .here => value
    | .there old => values old

inductive Node (Γ : List Kind) : Kind → Type where
  | levelZero : Node Γ .level
  | levelSucc : Ref Γ .level → Node Γ .level
  | levelMax : Ref Γ .level → Ref Γ .level → Node Γ .level
  | levelIMax : Ref Γ .level → Ref Γ .level → Node Γ .level
  | levelParam : Name → Node Γ .level
  | levelMVar : LMVarId → Node Γ .level
  | levelsNil : Node Γ .levels
  | levelsCons : Ref Γ .level → Ref Γ .levels → Node Γ .levels
  | bvar : Nat → Node Γ .expr
  | fvar : FVarId → Node Γ .expr
  | mvar : MVarId → Node Γ .expr
  | sort : Ref Γ .level → Node Γ .expr
  | const : Name → Ref Γ .levels → Node Γ .expr
  | app : Ref Γ .expr → Ref Γ .expr → Node Γ .expr
  | lam : Name → Ref Γ .expr → Ref Γ .expr → BinderInfo → Node Γ .expr
  | forallE : Name → Ref Γ .expr → Ref Γ .expr → BinderInfo → Node Γ .expr
  | letE : Name → Ref Γ .expr → Ref Γ .expr → Ref Γ .expr → Bool → Node Γ .expr
  | lit : Literal → Node Γ .expr
  | proj : Name → Nat → Ref Γ .expr → Node Γ .expr

def evalNode (values : Values Γ) : Node Γ k → Meaning k
  | .levelZero => .zero
  | .levelSucc u => .succ (values u)
  | .levelMax u v => .max (values u) (values v)
  | .levelIMax u v => .imax (values u) (values v)
  | .levelParam name => .param name
  | .levelMVar id => .mvar id
  | .levelsNil => []
  | .levelsCons u us => values u :: values us
  | .bvar i => .bvar i
  | .fvar id => .fvar id
  | .mvar id => .mvar id
  | .sort u => .sort (values u)
  | .const name us => .const name (values us)
  | .app f a => .app (values f) (values a)
  | .lam name type body info => .lam name (values type) (values body) info
  | .forallE name type body info => .forallE name (values type) (values body) info
  | .letE name type value body nondep => .letE name (values type) (values value) (values body) nondep
  | .lit literal => .lit literal
  | .proj name index struct => .proj name index (values struct)

-- An extension is a finite linear instruction store, not a syntax tree.
-- Each newly appended node can reference any slot of its preceding store.
inductive Extension (Γ : List Kind) : List Kind → Type where
  | done : Extension Γ Γ
  | snoc : Extension Γ Δ → Node Δ k → Extension Γ (k :: Δ)

def Extension.nodeCount : Extension Γ Δ → Nat
  | .done => 0
  | .snoc previous _ => previous.nodeCount + 1

theorem Extension.slot_count (code : Extension Γ Δ) :
    Δ.length = Γ.length + code.nodeCount := by
  induction code with
  | done => simp [Extension.nodeCount]
  | snoc previous node ih => simp [Extension.nodeCount, ih, Nat.add_assoc]

def Extension.append (first : Extension Γ Δ) : Extension Δ Θ → Extension Γ Θ
  | .done => first
  | .snoc rest node => .snoc (first.append rest) node

def Extension.lift : Extension Γ Δ → Ref Γ k → Ref Δ k
  | .done, r => r
  | .snoc previous _, r => .there (previous.lift r)

def run (initial : Values Γ) : Extension Γ Δ → Values Δ
  | .done => initial
  | .snoc previous node =>
    let before := run initial previous
    pushValues before (evalNode before node)

theorem run_append (initial : Values Γ) (first : Extension Γ Δ) (rest : Extension Δ Θ) :
    run initial (first.append rest) = run (run initial first) rest := by
  induction rest with
  | done => rfl
  | snoc rest node ih => simp only [Extension.append, run, ih]

theorem run_lift (initial : Values Γ) (code : Extension Γ Δ) (r : Ref Γ k) :
    run initial code (code.lift r) = initial r := by
  induction code with
  | done => rfl
  | snoc previous node ih => exact ih

structure Built (Γ : List Kind) (k : Kind) where
  slots : List Kind
  code : Extension Γ slots
  root : Ref slots k

abbrev Builder (k : Kind) := (Γ : List Kind) → Built Γ k

def builtValue (initial : Values Γ) (built : Built Γ k) : Meaning k :=
  run initial built.code built.root

def Correct (builder : Builder k) (expected : Meaning k) : Prop :=
  ∀ (Γ : List Kind) (initial : Values Γ), builtValue initial (builder Γ) = expected

def atom (node : (Γ : List Kind) → Node Γ k) : Builder k :=
  fun Γ => ⟨k :: Γ, .snoc .done (node Γ), .here⟩

def unary (first : Builder a) (node : {Γ : List Kind} → Ref Γ a → Node Γ k) : Builder k :=
  fun Γ =>
    let one := first Γ
    ⟨k :: one.slots, .snoc one.code (node one.root), .here⟩

def binary (first : Builder a) (second : Builder b)
    (node : {Γ : List Kind} → Ref Γ a → Ref Γ b → Node Γ k) : Builder k :=
  fun Γ =>
    let one := first Γ
    let two := second one.slots
    ⟨k :: two.slots,
      .snoc (one.code.append two.code) (node (two.code.lift one.root) two.root), .here⟩

def ternary (first : Builder a) (second : Builder b) (third : Builder c)
    (node : {Γ : List Kind} → Ref Γ a → Ref Γ b → Ref Γ c → Node Γ k) : Builder k :=
  fun Γ =>
    let one := first Γ
    let two := second one.slots
    let three := third two.slots
    ⟨k :: three.slots,
      .snoc ((one.code.append two.code).append three.code)
        (node (three.code.lift (two.code.lift one.root)) (three.code.lift two.root) three.root),
      .here⟩

theorem correct_atom (node : (Γ : List Kind) → Node Γ k) (expected : Meaning k)
    (h : ∀ Γ (values : Values Γ), evalNode values (node Γ) = expected) :
    Correct (atom node) expected := by
  intro Γ values
  exact h Γ values

theorem correct_unary (first : Builder a)
    (node : {Γ : List Kind} → Ref Γ a → Node Γ k)
    (operation : Meaning a → Meaning k)
    (hnode : ∀ Γ (values : Values Γ) r, evalNode values (node r) = operation (values r))
    (value : Meaning a) (hfirst : Correct first value) :
    Correct (unary first node) (operation value) := by
  intro Γ initial
  simp only [unary, builtValue, run, pushValues]
  rw [hnode]
  exact congrArg operation (hfirst Γ initial)

theorem correct_binary (first : Builder a) (second : Builder b)
    (node : {Γ : List Kind} → Ref Γ a → Ref Γ b → Node Γ k)
    (operation : Meaning a → Meaning b → Meaning k)
    (hnode : ∀ Γ (values : Values Γ) r s,
      evalNode values (node r s) = operation (values r) (values s))
    (x : Meaning a) (y : Meaning b) (hfirst : Correct first x) (hsecond : Correct second y) :
    Correct (binary first second node) (operation x y) := by
  intro Γ initial
  simp only [binary, builtValue, run, pushValues]
  rw [hnode, run_append, run_lift]
  rw [show run initial (first Γ).code (first Γ).root = x from hfirst Γ initial]
  rw [show run (run initial (first Γ).code) (second (first Γ).slots).code
      (second (first Γ).slots).root = y from hsecond _ _]

theorem correct_ternary (first : Builder a) (second : Builder b) (third : Builder c)
    (node : {Γ : List Kind} → Ref Γ a → Ref Γ b → Ref Γ c → Node Γ k)
    (operation : Meaning a → Meaning b → Meaning c → Meaning k)
    (hnode : ∀ Γ (values : Values Γ) r s t,
      evalNode values (node r s t) = operation (values r) (values s) (values t))
    (x : Meaning a) (y : Meaning b) (z : Meaning c)
    (hfirst : Correct first x) (hsecond : Correct second y) (hthird : Correct third z) :
    Correct (ternary first second third node) (operation x y z) := by
  intro Γ initial
  simp only [ternary, builtValue, run, pushValues]
  rw [hnode, run_append, run_append, run_lift, run_lift, run_lift]
  rw [show run initial (first Γ).code (first Γ).root = x from hfirst Γ initial]
  rw [show run (run initial (first Γ).code) (second (first Γ).slots).code
      (second (first Γ).slots).root = y from hsecond _ _]
  rw [show run (run (run initial (first Γ).code) (second (first Γ).slots).code)
      (third (second (first Γ).slots).slots).code
      (third (second (first Γ).slots).slots).root = z from hthird _ _]

def encodeLevel : Level → Builder .level
  | .zero => atom (fun _ => .levelZero)
  | .succ u => unary (encodeLevel u) Node.levelSucc
  | .max u v => binary (encodeLevel u) (encodeLevel v) Node.levelMax
  | .imax u v => binary (encodeLevel u) (encodeLevel v) Node.levelIMax
  | .param name => atom (fun _ => .levelParam name)
  | .mvar id => atom (fun _ => .levelMVar id)

def encodeLevels : List Level → Builder .levels
  | [] => atom (fun _ => .levelsNil)
  | u :: us => binary (encodeLevel u) (encodeLevels us) Node.levelsCons

def eraseMetadata : Expr → Expr
  | .bvar i => .bvar i
  | .fvar id => .fvar id
  | .mvar id => .mvar id
  | .sort u => .sort u
  | .const name us => .const name us
  | .app f a => .app (eraseMetadata f) (eraseMetadata a)
  | .lam name type body info => .lam name (eraseMetadata type) (eraseMetadata body) info
  | .forallE name type body info => .forallE name (eraseMetadata type) (eraseMetadata body) info
  | .letE name type value body nondep =>
    .letE name (eraseMetadata type) (eraseMetadata value) (eraseMetadata body) nondep
  | .lit literal => .lit literal
  | .mdata _ body => eraseMetadata body
  | .proj name index struct => .proj name index (eraseMetadata struct)

def encodeExpr : Expr → Builder .expr
  | .bvar i => atom (fun _ => .bvar i)
  | .fvar id => atom (fun _ => .fvar id)
  | .mvar id => atom (fun _ => .mvar id)
  | .sort u => unary (encodeLevel u) Node.sort
  | .const name us => unary (encodeLevels us) (Node.const name)
  | .app f a => binary (encodeExpr f) (encodeExpr a) Node.app
  | .lam name type body info =>
    binary (encodeExpr type) (encodeExpr body) (fun type body => Node.lam name type body info)
  | .forallE name type body info =>
    binary (encodeExpr type) (encodeExpr body) (fun type body => Node.forallE name type body info)
  | .letE name type value body nondep =>
    ternary (encodeExpr type) (encodeExpr value) (encodeExpr body)
      (fun type value body => Node.letE name type value body nondep)
  | .lit literal => atom (fun _ => .lit literal)
  | .mdata _ body => encodeExpr body
  | .proj name index struct => unary (encodeExpr struct) (Node.proj name index)

theorem encodeLevel_correct (level : Level) : Correct (encodeLevel level) level := by
  induction level with
  | zero => exact correct_atom _ _ (fun _ _ => rfl)
  | succ u ihu => exact correct_unary (encodeLevel u) Node.levelSucc Level.succ (fun _ _ _ => rfl) u ihu
  | max u v ihu ihv =>
    exact correct_binary (encodeLevel u) (encodeLevel v) Node.levelMax Level.max (fun _ _ _ _ => rfl) u v ihu ihv
  | imax u v ihu ihv =>
    exact correct_binary (encodeLevel u) (encodeLevel v) Node.levelIMax Level.imax (fun _ _ _ _ => rfl) u v ihu ihv
  | param name => exact correct_atom _ _ (fun _ _ => rfl)
  | mvar id => exact correct_atom _ _ (fun _ _ => rfl)

theorem encodeLevels_correct (levels : List Level) : Correct (encodeLevels levels) levels := by
  induction levels with
  | nil => exact correct_atom _ _ (fun _ _ => rfl)
  | cons u us ih =>
    exact correct_binary (encodeLevel u) (encodeLevels us) Node.levelsCons List.cons
      (fun _ _ _ _ => rfl) u us (encodeLevel_correct u) ih

theorem encodeExpr_correct (e : Expr) : Correct (encodeExpr e) (eraseMetadata e) := by
  induction e with
  | bvar i => exact correct_atom _ _ (fun _ _ => rfl)
  | fvar id => exact correct_atom _ _ (fun _ _ => rfl)
  | mvar id => exact correct_atom _ _ (fun _ _ => rfl)
  | sort u => exact correct_unary (encodeLevel u) Node.sort Expr.sort (fun _ _ _ => rfl) u (encodeLevel_correct u)
  | const name us =>
    exact correct_unary (encodeLevels us) (Node.const name) (Expr.const name)
      (fun _ _ _ => rfl) us (encodeLevels_correct us)
  | app f a ihf iha =>
    exact correct_binary (encodeExpr f) (encodeExpr a) Node.app Expr.app (fun _ _ _ _ => rfl) _ _ ihf iha
  | lam name type body info iht ihb =>
    exact correct_binary (encodeExpr type) (encodeExpr body) (fun t b => Node.lam name t b info)
      (fun t b => Expr.lam name t b info)
      (fun _ _ _ _ => rfl) _ _ iht ihb
  | forallE name type body info iht ihb =>
    exact correct_binary (encodeExpr type) (encodeExpr body) (fun t b => Node.forallE name t b info)
      (fun t b => Expr.forallE name t b info)
      (fun _ _ _ _ => rfl) _ _ iht ihb
  | letE name type value body nondep iht ihv ihb =>
    exact correct_ternary (encodeExpr type) (encodeExpr value) (encodeExpr body)
      (fun t v b => Node.letE name t v b nondep) (fun t v b => Expr.letE name t v b nondep)
      (fun _ _ _ _ _ => rfl) _ _ _ iht ihv ihb
  | lit literal => exact correct_atom _ _ (fun _ _ => rfl)
  | mdata metadata body ih => exact ih
  | proj name index struct ih =>
    exact correct_unary (encodeExpr struct) (Node.proj name index) (Expr.proj name index)
      (fun _ _ _ => rfl) _ ih

def emptyValues : Values [] where
  get := fun r => nomatch r

-- Closed graphs have only the finite instruction store and a designated root.
abbrev ClosedGraph (k : Kind) := Built [] k

def decodeGraph (graph : ClosedGraph k) : Meaning k := builtValue emptyValues graph

def encode (e : Expr) : ClosedGraph .expr := encodeExpr e []

theorem roundTrip_eq (e : Expr) : decodeGraph (encode e) = eraseMetadata e :=
  encodeExpr_correct e [] emptyValues

-- A constructor-by-constructor relation, separate from Expr's alpha-oriented BEq.
inductive ExactLevel : Level → Level → Prop where
  | zero : ExactLevel .zero .zero
  | succ : ExactLevel u v → ExactLevel (.succ u) (.succ v)
  | max : ExactLevel u u' → ExactLevel v v' → ExactLevel (.max u v) (.max u' v')
  | imax : ExactLevel u u' → ExactLevel v v' → ExactLevel (.imax u v) (.imax u' v')
  | param (name : Name) : ExactLevel (.param name) (.param name)
  | mvar (id : LMVarId) : ExactLevel (.mvar id) (.mvar id)

theorem ExactLevel.refl (u : Level) : ExactLevel u u := by
  induction u with
  | zero => exact .zero
  | succ u ih => exact .succ ih
  | max u v ihu ihv => exact .max ihu ihv
  | imax u v ihu ihv => exact .imax ihu ihv
  | param name => exact .param name
  | mvar id => exact .mvar id

inductive ExactLevels : List Level → List Level → Prop where
  | nil : ExactLevels [] []
  | cons : ExactLevel u v → ExactLevels us vs → ExactLevels (u :: us) (v :: vs)

theorem exactLevels_refl (us : List Level) : ExactLevels us us := by
  induction us with
  | nil => exact .nil
  | cons u us ih => exact .cons (ExactLevel.refl u) ih

inductive ExactExpr : Expr → Expr → Prop where
  | bvar (i : Nat) : ExactExpr (.bvar i) (.bvar i)
  | fvar (id : FVarId) : ExactExpr (.fvar id) (.fvar id)
  | mvar (id : MVarId) : ExactExpr (.mvar id) (.mvar id)
  | sort : ExactLevel u v → ExactExpr (.sort u) (.sort v)
  | const (name : Name) : ExactLevels us vs → ExactExpr (.const name us) (.const name vs)
  | app : ExactExpr f f' → ExactExpr a a' → ExactExpr (.app f a) (.app f' a')
  | lam (name : Name) (info : BinderInfo) : ExactExpr t t' → ExactExpr b b' →
      ExactExpr (.lam name t b info) (.lam name t' b' info)
  | forallE (name : Name) (info : BinderInfo) : ExactExpr t t' → ExactExpr b b' →
      ExactExpr (.forallE name t b info) (.forallE name t' b' info)
  | letE (name : Name) (nondep : Bool) : ExactExpr t t' → ExactExpr v v' → ExactExpr b b' →
      ExactExpr (.letE name t v b nondep) (.letE name t' v' b' nondep)
  | lit (literal : Literal) : ExactExpr (.lit literal) (.lit literal)
  | mdata (metadata : MData) : ExactExpr e e' → ExactExpr (.mdata metadata e) (.mdata metadata e')
  | proj (name : Name) (index : Nat) : ExactExpr e e' → ExactExpr (.proj name index e) (.proj name index e')

theorem ExactExpr.refl (e : Expr) : ExactExpr e e := by
  induction e with
  | bvar i => exact .bvar i
  | fvar id => exact .fvar id
  | mvar id => exact .mvar id
  | sort u => exact .sort (ExactLevel.refl u)
  | const name us => exact .const name (exactLevels_refl us)
  | app f a ihf iha => exact .app ihf iha
  | lam name type body info iht ihb => exact .lam name info iht ihb
  | forallE name type body info iht ihb => exact .forallE name info iht ihb
  | letE name type value body nondep iht ihv ihb => exact .letE name nondep iht ihv ihb
  | lit literal => exact .lit literal
  | mdata metadata body ih => exact .mdata metadata ih
  | proj name index struct ih => exact .proj name index ih

theorem roundTrip_exact (e : Expr) : ExactExpr (decodeGraph (encode e)) (eraseMetadata e) := by
  rw [roundTrip_eq]
  exact ExactExpr.refl _

theorem exact_binder_fields
    (h : ExactExpr (.lam name type body info) (.lam name' type' body' info')) :
    name = name' ∧ info = info' := by
  cases h
  exact ⟨rfl, rfl⟩

theorem exact_let_flag
    (h : ExactExpr (.letE name type value body flag) (.letE name' type' value' body' flag')) :
    flag = flag' := by
  cases h
  rfl

theorem eraseMetadata_idempotent (e : Expr) :
    eraseMetadata (eraseMetadata e) = eraseMetadata e := by
  induction e <;> simp_all [eraseMetadata]

-- A graph supplied directly, not by encode: it represents Nat.add 7 7 using
-- five instructions; the literal slot is reused.
def sharedLiteral : ClosedGraph .expr where
  slots := [.expr, .expr, .expr, .expr, .levels]
  code := .snoc
    (.snoc
      (.snoc
        (.snoc
          (.snoc .done .levelsNil)
          (.const ``Nat.add .here))
        (.lit (.natVal 7)))
      (.app (.there .here) .here))
    (.app .here (.there .here))
  root := .here

theorem sharedLiteral_reading :
    decodeGraph sharedLiteral =
      .app (.app (.const ``Nat.add []) (.lit (.natVal 7))) (.lit (.natVal 7)) := rfl

theorem sharedLiteral_five_nodes : sharedLiteral.code.nodeCount = 5 := rfl

-- This diagnostic contains metadata below a binder and under an application,
-- a nondefault binder annotation, and a retained dependent-let flag.
def metadataExample : Expr :=
  .lam `outer (.mdata {} (.sort (.imax (.param `u) (.succ .zero))))
    (.letE `local (.mdata {} (.const ``Nat [])) (.lit (.natVal 7))
      (.app (.mdata {} (.bvar 1)) (.mdata {} (.bvar 0))) false) .strictImplicit

theorem nested_metadata_and_attributes :
    decodeGraph (encode metadataExample) =
      .lam `outer (.sort (.imax (.param `u) (.succ .zero)))
        (.letE `local (.const ``Nat []) (.lit (.natVal 7))
          (.app (.bvar 1) (.bvar 0)) false) .strictImplicit := by
  rw [roundTrip_eq]
  rfl


end ExprReferenceGraph
