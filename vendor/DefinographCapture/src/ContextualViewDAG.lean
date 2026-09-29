import DerivedViewSyntax

/- Finite earlier-ranked constructor rows and explicit contextual occurrences.
   Raw scopes are arities, not named homes or dependent telescopes. Graph data
   store no View/Expr payload and no function-valued occurrence maps. -/
namespace ContextualViewDAG
open Lean DerivedViewSyntax

-- Γ lists row home arities, newest first. A Ref retains its callee's arity.
inductive Ref : List Nat → Nat → Type where
  | here : Ref (r :: Γ) r
  | there : Ref Γ r → Ref (s :: Γ) r

mutual
  inductive Occ (Γ : List Nat) (n : Nat) where
    | var : Fin n → Occ Γ n
    | use {r : Nat} : Ref Γ r → Args Γ n r → Occ Γ n
  inductive Args (Γ : List Nat) (n : Nat) : Nat → Type where
    | nil : Args Γ n 0
    | cons {r : Nat} : Occ Γ n → Args Γ n r → Args Γ n (r+1)
end

def Args.get : Args Γ n r → Fin r → Occ Γ n
  | .nil => Fin.elim0
  | .cons first rest => Fin.cases first rest.get

def Args.ofFn : {r : Nat} → (Fin r → Occ Γ n) → Args Γ n r
  | 0, _ => .nil
  | _+1, f => .cons (f 0) (Args.ofFn (fun i => f i.succ))

-- Exactly one source/view constructor layer per stored row.
inductive Row (Γ : List Nat) : Nat → Type where
  | var {n} : Fin n → Row Γ n
  | sort {n} : ULevel → Row Γ n
  | const {n} : Name → List ULevel → Row Γ n
  | lit {n} : Literal → Row Γ n
  | app {n} : Occ Γ n → Occ Γ n → Row Γ n
  | lam {n} : BinderAttrs → Occ Γ n → Occ Γ (n+1) → Row Γ n
  | pi {n} : BinderAttrs → Occ Γ n → Occ Γ (n+1) → Row Γ n
  | letE {n} : Name → Bool → Occ Γ n → Occ Γ n → Occ Γ (n+1) → Row Γ n
  | proj {n} : Name → Nat → Occ Γ n → Row Γ n
  | unique {n} : UniqueAttrs → Occ Γ n → Occ Γ n → Occ Γ n → Occ Γ n → Occ Γ n → Row Γ n
  | inst {n r} : Occ Γ r → Args Γ n r → Row Γ n

inductive Table : List Nat → Type where
  | empty : Table []
  | snoc : Table Γ → Row Γ n → Table (n :: Γ)

def Table.rowCount : Table Γ → Nat
  | .empty => 0
  | .snoc prior _ => prior.rowCount + 1

theorem Table.rowCount_eq (table : Table Γ) : table.rowCount = Γ.length := by
  induction table with
  | empty => rfl
  | snoc prior row ih => simp [Table.rowCount, ih]

def Ref.offset : Ref Γ r → Nat
  | .here => 0
  | .there previous => previous.offset + 1

theorem Ref.offset_bounded (ref : Ref Γ r) : ref.offset < Γ.length := by
  induction ref with
  | here => simp [Ref.offset]
  | there previous ih => simpa [Ref.offset] using Nat.succ_lt_succ ih

-- Independent syntactic actions; neither calls unrolling or View.subst.
mutual
  def rename (ρ : Fin n → Fin m) : Occ Γ n → Occ Γ m
    | .var i => .var (ρ i)
    | .use ref actuals => .use ref (renameArgs ρ actuals)
  def renameArgs (ρ : Fin n → Fin m) : Args Γ n r → Args Γ m r
    | .nil => .nil
    | .cons first rest => .cons (rename ρ first) (renameArgs ρ rest)
end

mutual
  def subst (σ : Fin n → Occ Γ m) : Occ Γ n → Occ Γ m
    | .var i => σ i
    | .use ref actuals => .use ref (substArgs σ actuals)
  def substArgs (σ : Fin n → Occ Γ m) : Args Γ n r → Args Γ m r
    | .nil => .nil
    | .cons first rest => .cons (subst σ first) (substArgs σ rest)
end

def liftSub (σ : Fin n → Occ Γ m) : Fin (n+1) → Occ Γ (m+1) :=
  Fin.cases (.var 0) (fun i => rename Fin.succ (σ i))

-- Reference embedding leaves ambient slots and callee home arities unchanged.
abbrev RefMap (Γ Δ : List Nat) := {r : Nat} → Ref Γ r → Ref Δ r

mutual
  def mapRefs (ρ : RefMap Γ Δ) : Occ Γ n → Occ Δ n
    | .var i => .var i
    | .use ref actuals => .use (ρ ref) (mapArgs ρ actuals)
  def mapArgs (ρ : RefMap Γ Δ) : Args Γ n r → Args Δ n r
    | .nil => .nil
    | .cons first rest => .cons (mapRefs ρ first) (mapArgs ρ rest)
end

-- Values are temporary decoder state, never a payload of graph data.
abbrev Values (Γ : List Nat) := {r : Nat} → Ref Γ r → View r

mutual
  def evalOcc (values : Values Γ) : Occ Γ n → View n
    | .var i => .var i
    | .use ref actuals => DerivedViewSyntax.subst (evalArgs values actuals) (values ref)
  def evalArgs (values : Values Γ) : Args Γ n r → Fin r → View n
    | .nil => Fin.elim0
    | .cons first rest => Fin.cases (evalOcc values first) (evalArgs values rest)
end

def evalRow (values : Values Γ) : Row Γ n → View n
  | .var i => .var i
  | .sort u => .sort u
  | .const name levels => .const name levels
  | .lit value => .lit value
  | .app fn arg => .app (evalOcc values fn) (evalOcc values arg)
  | .lam attrs domain body => .lam attrs (evalOcc values domain) (evalOcc values body)
  | .pi attrs domain body => .pi attrs (evalOcc values domain) (evalOcc values body)
  | .letE name nondep type value body =>
    .letE name nondep (evalOcc values type) (evalOcc values value) (evalOcc values body)
  | .proj name index value => .proj name index (evalOcc values value)
  | .unique attrs A B step advance relation =>
    .unique rfl attrs (evalOcc values A) (evalOcc values B) (evalOcc values step)
      (evalOcc values advance) (evalOcc values relation)
  | .inst body actuals => .inst rfl (evalOcc values body) (evalArgs values actuals)

-- The denotation of every row is constructed from its actual earlier prefix.
def tableValues : Table Γ → Values Γ
  | .empty => fun ref => nomatch ref
  | .snoc prior row => fun ref =>
    match ref with
    | .here => evalRow (tableValues prior) row
    | .there previous => tableValues prior previous

def unroll (table : Table Γ) (occurrence : Occ Γ n) : View n :=
  evalOcc (tableValues table) occurrence

def unrollArgs (table : Table Γ) (actuals : Args Γ n r) : Fin r → View n :=
  evalArgs (tableValues table) actuals

structure Graph (n : Nat) where
  homes : List Nat
  table : Table homes
  root : Occ homes n

def Graph.unroll (graph : Graph n) : View n := ContextualViewDAG.unroll graph.table graph.root

mutual
  theorem subst_id (o : Occ Γ n) : subst Occ.var o = o := by
    cases o with
    | var i => rfl
    | use ref actuals => simp only [subst, substArgs_id actuals]
  termination_by sizeOf o
  theorem substArgs_id (actuals : Args Γ n r) : substArgs Occ.var actuals = actuals := by
    cases actuals with
    | nil => rfl
    | cons first rest => simp only [substArgs, subst_id first, substArgs_id rest]
  termination_by sizeOf actuals
end

mutual
  theorem subst_comp (o : Occ Γ n) (σ : Fin n → Occ Γ m) (τ : Fin m → Occ Γ l) :
      subst τ (subst σ o) = subst (fun i => subst τ (σ i)) o := by
    cases o with
    | var i => rfl
    | use ref actuals => simp only [subst, substArgs_comp actuals σ τ]
  termination_by sizeOf o
  theorem substArgs_comp (actuals : Args Γ n r) (σ : Fin n → Occ Γ m) (τ : Fin m → Occ Γ l) :
      substArgs τ (substArgs σ actuals) = substArgs (fun i => subst τ (σ i)) actuals := by
    cases actuals with
    | nil => rfl
    | cons first rest => simp only [substArgs, subst_comp first σ τ, substArgs_comp rest σ τ]
  termination_by sizeOf actuals
end

mutual
  theorem rename_id (o : Occ Γ n) : rename id o = o := by
    cases o with
    | var i => rfl
    | use ref actuals => simp only [rename, renameArgs_id actuals]
  termination_by sizeOf o
  theorem renameArgs_id (actuals : Args Γ n r) : renameArgs id actuals = actuals := by
    cases actuals with
    | nil => rfl
    | cons first rest => simp only [renameArgs, rename_id first, renameArgs_id rest]
  termination_by sizeOf actuals
end

mutual
  theorem rename_comp (o : Occ Γ n) (ρ : Fin n → Fin m) (θ : Fin m → Fin l) :
      rename θ (rename ρ o) = rename (fun i => θ (ρ i)) o := by
    cases o with
    | var i => rfl
    | use ref actuals => simp only [rename, renameArgs_comp actuals ρ θ]
  termination_by sizeOf o
  theorem renameArgs_comp (actuals : Args Γ n r) (ρ : Fin n → Fin m) (θ : Fin m → Fin l) :
      renameArgs θ (renameArgs ρ actuals) = renameArgs (fun i => θ (ρ i)) actuals := by
    cases actuals with
    | nil => rfl
    | cons first rest => simp only [renameArgs, rename_comp first ρ θ, renameArgs_comp rest ρ θ]
  termination_by sizeOf actuals
end

def compose (σ : Fin n → Occ Γ m) (τ : Fin m → Occ Γ l) : Fin n → Occ Γ l :=
  fun i => subst τ (σ i)

theorem compose_id_left (σ : Fin n → Occ Γ m) : compose Occ.var σ = σ := rfl

theorem compose_id_right (σ : Fin n → Occ Γ m) : compose σ Occ.var = σ := by
  funext i
  exact subst_id (σ i)

theorem compose_assoc (σ : Fin n → Occ Γ m) (τ : Fin m → Occ Γ l) (υ : Fin l → Occ Γ k) :
    compose (compose σ τ) υ = compose σ (compose τ υ) := by
  funext i
  exact subst_comp (σ i) τ υ

-- These helpers prove laws for the evaluator. Actual-table theorems below use
-- tableValues, which was constructed from stored rows, never assumed as data.
mutual
  theorem eval_subst (values : Values Γ) (o : Occ Γ n) (σ : Fin n → Occ Γ m) :
      evalOcc values (subst σ o) =
        DerivedViewSyntax.subst (fun i => evalOcc values (σ i)) (evalOcc values o) := by
    cases o with
    | var i => rfl
    | use ref actuals =>
      simp only [subst, evalOcc, evalArgs_subst values actuals σ, DerivedViewSyntax.subst_comp]
  termination_by sizeOf o
  theorem evalArgs_subst (values : Values Γ) (actuals : Args Γ n r) (σ : Fin n → Occ Γ m) :
      evalArgs values (substArgs σ actuals) =
        fun j => DerivedViewSyntax.subst (fun i => evalOcc values (σ i)) (evalArgs values actuals j) := by
    cases actuals with
    | nil => funext i; exact Fin.elim0 i
    | cons first rest =>
      funext i
      exact Fin.cases (eval_subst values first σ)
        (fun j => congrFun (evalArgs_subst values rest σ) j) i
  termination_by sizeOf actuals
end

mutual
  theorem eval_rename (values : Values Γ) (o : Occ Γ n) (ρ : Fin n → Fin m) :
      evalOcc values (rename ρ o) = DerivedViewSyntax.rename ρ (evalOcc values o) := by
    cases o with
    | var i => rfl
    | use ref actuals =>
      simp only [rename, evalOcc, evalArgs_rename values actuals ρ, DerivedViewSyntax.rename_subst]
  termination_by sizeOf o
  theorem evalArgs_rename (values : Values Γ) (actuals : Args Γ n r) (ρ : Fin n → Fin m) :
      evalArgs values (renameArgs ρ actuals) = fun j => DerivedViewSyntax.rename ρ (evalArgs values actuals j) := by
    cases actuals with
    | nil => funext i; exact Fin.elim0 i
    | cons first rest =>
      funext i
      exact Fin.cases (eval_rename values first ρ)
        (fun j => congrFun (evalArgs_rename values rest ρ) j) i
  termination_by sizeOf actuals
end

theorem unroll_subst (table : Table Γ) (o : Occ Γ n) (σ : Fin n → Occ Γ m) :
    unroll table (subst σ o) = DerivedViewSyntax.subst (fun i => unroll table (σ i)) (unroll table o) :=
  eval_subst (tableValues table) o σ

theorem unroll_rename (table : Table Γ) (o : Occ Γ n) (ρ : Fin n → Fin m) :
    unroll table (rename ρ o) = DerivedViewSyntax.rename ρ (unroll table o) :=
  eval_rename (tableValues table) o ρ

theorem unroll_liftSub (table : Table Γ) (σ : Fin n → Occ Γ m) :
    (fun i => unroll table (liftSub σ i)) = DerivedViewSyntax.liftSub (fun i => unroll table (σ i)) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact unroll_rename table (σ j) Fin.succ

theorem evalArgs_ofFn (values : Values Γ) (f : Fin r → Occ Γ n) :
    evalArgs values (Args.ofFn f) = fun i => evalOcc values (f i) := by
  induction r with
  | zero => funext i; exact Fin.elim0 i
  | succ r ih =>
    funext i
    exact Fin.cases rfl (fun j => congrFun (ih (fun i => f i.succ)) j) i

theorem Args.get_ofFn (f : Fin r → Occ Γ n) : (Args.ofFn f).get = f := by
  induction r with
  | zero => funext i; exact Fin.elim0 i
  | succ r ih =>
    funext i
    exact Fin.cases rfl (fun j => congrFun (ih (fun i => f i.succ)) j) i

theorem evalArgs_get (values : Values Γ) (actuals : Args Γ n r) (i : Fin r) :
    evalArgs values actuals i = evalOcc values (actuals.get i) := by
  cases actuals with
  | nil => exact Fin.elim0 i
  | cons first rest => exact Fin.cases rfl (evalArgs_get values rest) i
termination_by r

mutual
  theorem eval_mapRefs (ρ : RefMap Γ Δ) (old : Values Γ) (new : Values Δ)
      (h : ∀ {r} (ref : Ref Γ r), new (ρ ref) = old ref) (o : Occ Γ n) :
      evalOcc new (mapRefs ρ o) = evalOcc old o := by
    cases o with
    | var i => rfl
    | use ref actuals => simp only [mapRefs, evalOcc, eval_mapArgs ρ old new h actuals, h]
  termination_by sizeOf o
  theorem eval_mapArgs (ρ : RefMap Γ Δ) (old : Values Γ) (new : Values Δ)
      (h : ∀ {r} (ref : Ref Γ r), new (ρ ref) = old ref) (actuals : Args Γ n r) :
      evalArgs new (mapArgs ρ actuals) = evalArgs old actuals := by
    cases actuals with
    | nil => rfl
    | cons first rest =>
      simp only [mapArgs, evalArgs, eval_mapRefs ρ old new h first, eval_mapArgs ρ old new h rest]
  termination_by sizeOf actuals
end

-- A finite, actual append-only extension, including all appended row data.
inductive Extension (Γ : List Nat) : List Nat → Type where
  | done : Extension Γ Γ
  | snoc : Extension Γ Δ → Row Δ n → Extension Γ (n :: Δ)

def Extension.extend (base : Table Γ) : Extension Γ Δ → Table Δ
  | .done => base
  | .snoc prior row => .snoc (prior.extend base) row

def Extension.lift : Extension Γ Δ → RefMap Γ Δ
  | .done => fun ref => ref
  | .snoc prior _ => fun ref => .there (prior.lift ref)

theorem tableValues_lift (base : Table Γ) (extension : Extension Γ Δ) (ref : Ref Γ r) :
    tableValues (extension.extend base) (extension.lift ref) = tableValues base ref := by
  induction extension with
  | done => rfl
  | snoc prior row ih => exact ih

theorem prefix_stability (base : Table Γ) (extension : Extension Γ Δ) (o : Occ Γ n) :
    unroll (extension.extend base) (mapRefs extension.lift o) = unroll base o :=
  eval_mapRefs extension.lift (tableValues base) (tableValues (extension.extend base))
    (tableValues_lift base extension) o

theorem args_prefix_stability (base : Table Γ) (extension : Extension Γ Δ) (actuals : Args Γ n r) :
    unrollArgs (extension.extend base) (mapArgs extension.lift actuals) = unrollArgs base actuals :=
  eval_mapArgs extension.lift (tableValues base) (tableValues (extension.extend base))
    (tableValues_lift base extension) actuals

theorem unroll_snoc (table : Table Γ) (row : Row Γ r) (o : Occ Γ n) :
    unroll (.snoc table row) (mapRefs Ref.there o) = unroll table o :=
  eval_mapRefs Ref.there (tableValues table) (tableValues (.snoc table row)) (fun _ => rfl) o

-- Add a genuine explicit-inst row; the administrative use of that row carries
-- the identity occurrence map. The operation invokes no decoder or expansion.
def plugTable (table : Table Γ) (producer : Occ Γ r) (actuals : Args Γ n r) : Table (n :: Γ) :=
  .snoc table (.inst producer actuals)

def freshUse : Occ (n :: Γ) n := .use .here (Args.ofFn Occ.var)

def plugOccurrence (consumer : Occ Γ (n+1)) : Occ (n :: Γ) n :=
  subst (Fin.cases freshUse Occ.var) (mapRefs Ref.there consumer)

theorem unroll_freshUse (table : Table Γ) (producer : Occ Γ r) (actuals : Args Γ n r) :
    unroll (plugTable table producer actuals) freshUse =
      .inst rfl (unroll table producer) (unrollArgs table actuals) := by
  simp only [unroll, freshUse, evalOcc, evalArgs_ofFn, plugTable, tableValues, evalRow]
  exact DerivedViewSyntax.subst_id _

theorem unroll_plug (table : Table Γ) (consumer : Occ Γ (n+1))
    (producer : Occ Γ r) (actuals : Args Γ n r) :
    unroll (plugTable table producer actuals) (plugOccurrence consumer) =
      DerivedViewSyntax.plug (unroll table consumer) (unroll table producer) (unrollArgs table actuals) := by
  unfold plugOccurrence
  rw [unroll_subst]
  rw [show unroll (plugTable table producer actuals) (mapRefs Ref.there consumer) =
    unroll table consumer from unroll_snoc table (.inst producer actuals) consumer]
  unfold DerivedViewSyntax.plug
  congr 1
  funext i
  exact Fin.cases (unroll_freshUse table producer actuals) (fun _ => rfl) i

theorem expand_unroll_subst (table : Table Γ) (o : Occ Γ n) (σ : Fin n → Occ Γ m) :
    DerivedViewSyntax.expand (unroll table (subst σ o)) =
      DerivedViewSyntax.subst (fun i => DerivedViewSyntax.expand (unroll table (σ i)))
        (DerivedViewSyntax.expand (unroll table o)) := by
  rw [unroll_subst, DerivedViewSyntax.expand_subst]

theorem expand_unroll_plug (table : Table Γ) (consumer : Occ Γ (n+1))
    (producer : Occ Γ r) (actuals : Args Γ n r) :
    DerivedViewSyntax.expand (unroll (plugTable table producer actuals) (plugOccurrence consumer)) =
      DerivedViewSyntax.corePlug (DerivedViewSyntax.expand (unroll table consumer))
        (DerivedViewSyntax.expand (unroll table producer))
        (fun i => DerivedViewSyntax.expand (unrollArgs table actuals i)) := by
  rw [unroll_plug, DerivedViewSyntax.expand_plug]

-- Four actual rows. The selector is the very same row in the inner lambda's
-- domain and body, with distinct ambient arities/lexical interpretations.
def selectorTable : Table [1] := .snoc .empty (.var 0)

def selectorAndSort : Table [0, 1] := .snoc selectorTable (.sort (.succ .zero))

def innerSharedRow : Row [0, 1] 1 :=
  .lam ⟨`x, .default⟩
    (.use (.there .here) (.cons (.var 0) .nil))
    (.use (.there .here) (.cons (.var 0) .nil))

def withInnerShared : Table [1, 0, 1] := .snoc selectorAndSort innerSharedRow

def sharingTable : Table [0, 1, 0, 1] :=
  .snoc withInnerShared
    (.lam ⟨`A, .default⟩ (.use (.there .here) .nil)
      (.use .here (.cons (.var 0) .nil)))

def sharingRoot : Occ [0, 1, 0, 1] 0 := .use .here .nil

theorem sharing_four_rows : sharingTable.rowCount = 4 := rfl

theorem sharing_exact :
    unroll sharingTable sharingRoot =
      Term.lam ⟨`A, .default⟩ (.sort (.succ .zero))
        (.lam ⟨`x, .default⟩ (.var 0) (.var 0)) := rfl

-- A map image can refer to a row newer than the callee, while both precede
-- their storage site. Termination must account for the map tree, not just ref.
def laterArgument : Occ [0, 1] 0 :=
  .use (.there .here) (.cons (.use .here .nil) .nil)

theorem later_argument_exact :
    unroll selectorAndSort laterArgument = Term.sort (.succ .zero) := rfl


end ContextualViewDAG
