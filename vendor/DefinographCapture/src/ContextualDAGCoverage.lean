import ContextualViewDAG

/- Constructive finite-table coverage. This file uses the actual ranked table
   representation, not an arbitrary assignment of semantic row values. -/
namespace ContextualDAGCoverage
open Lean DerivedViewSyntax ContextualViewDAG

structure Extension (initial : Table Γ) where
  homes : List Nat
  table : Table homes
  refs : RefMap Γ homes
  preserved : ∀ {r} (ref : Ref Γ r), tableValues table (refs ref) = tableValues initial ref

def Extension.refl (table : Table Γ) : Extension table :=
  ⟨Γ, table, (fun ref => ref), (fun _ => rfl)⟩

def Extension.trans {base : Table Γ} (a : Extension base) (b : Extension a.table) : Extension base :=
  ⟨b.homes, b.table, (fun ref => b.refs (a.refs ref)), by
    intro r ref
    rw [b.preserved, a.preserved]⟩

def Extension.add (table : Table Γ) (row : Row Γ n) : Extension table :=
  ⟨n :: Γ, .snoc table row, (fun ref => .there ref), (fun _ => rfl)⟩

def Extension.map {base : Table Γ} (e : Extension base) (o : Occ Γ n) : Occ e.homes n :=
  mapRefs e.refs o

theorem Extension.unroll_map {base : Table Γ} (e : Extension base) (o : Occ Γ n) :
    unroll e.table (e.map o) = unroll base o :=
  eval_mapRefs e.refs (tableValues base) (tableValues e.table) e.preserved o

def rootOfRow : Occ (n :: Γ) n :=
  .use .here (Args.ofFn Occ.var)

theorem unroll_rootOfRow (table : Table Γ) (row : Row Γ n) :
    unroll (.snoc table row) (rootOfRow) = evalRow (tableValues table) row := by
  simp only [unroll, rootOfRow, evalOcc, evalArgs_ofFn, tableValues]
  exact DerivedViewSyntax.subst_id _

def Representable (t : View n) : Prop :=
  ∀ {Γ} (table : Table Γ), ∃ e : Extension table,
    ∃ o : Occ e.homes n, unroll e.table o = t

theorem represent_row (table : Table Γ) (row : Row Γ n) :
    ∃ e : Extension table, ∃ o : Occ e.homes n,
      unroll e.table o = evalRow (tableValues table) row :=
  ⟨Extension.add table row, rootOfRow, unroll_rootOfRow table row⟩

theorem represent_unary (t : View a) (ht : Representable t)
    (ctor : View a → View n)
    (row : {Γ : List Nat} → Occ Γ a → Row Γ n)
    (law : ∀ {Γ} (v : Values Γ) (o : Occ Γ a),
      evalRow v (row o) = ctor (evalOcc v o)) : Representable (ctor t) := by
  intro Γ table
  obtain ⟨e, o, ho⟩ := ht table
  obtain ⟨e', out, hout⟩ := represent_row e.table (row o)
  refine ⟨e.trans e', out, ?_⟩
  change unroll e'.table out = ctor t
  rw [hout, law]
  exact congrArg ctor ho

theorem represent_binary (t : View a) (u : View b)
    (ht : Representable t) (hu : Representable u)
    (ctor : View a → View b → View n)
    (row : {Γ : List Nat} → Occ Γ a → Occ Γ b → Row Γ n)
    (law : ∀ {Γ} (v : Values Γ) (o : Occ Γ a) (p : Occ Γ b),
      evalRow v (row o p) = ctor (evalOcc v o) (evalOcc v p)) :
    Representable (ctor t u) := by
  intro Γ table
  obtain ⟨e, o, ho⟩ := ht table
  obtain ⟨e', p, hp⟩ := hu e.table
  obtain ⟨e'', out, hout⟩ := represent_row e'.table (row (e'.map o) p)
  refine ⟨(e.trans e').trans e'', out, ?_⟩
  change unroll e''.table out = ctor t u
  rw [hout, law]
  change ctor (unroll e'.table (e'.map o)) (unroll e'.table p) = _
  rw [e'.unroll_map, ho, hp]

theorem represent_ternary (t : View a) (u : View b) (v : View c)
    (ht : Representable t) (hu : Representable u) (hv : Representable v)
    (ctor : View a → View b → View c → View n)
    (row : {Γ : List Nat} → Occ Γ a → Occ Γ b → Occ Γ c → Row Γ n)
    (law : ∀ {Γ} (values : Values Γ) (o : Occ Γ a) (p : Occ Γ b) (q : Occ Γ c),
      evalRow values (row o p q) =
        ctor (evalOcc values o) (evalOcc values p) (evalOcc values q)) :
    Representable (ctor t u v) := by
  intro Γ table
  obtain ⟨e, o, ho⟩ := ht table
  obtain ⟨e', p, hp⟩ := hu e.table
  obtain ⟨e'', q, hq⟩ := hv e'.table
  obtain ⟨last, out, hout⟩ := represent_row e''.table
    (row (e''.map (e'.map o)) (e''.map p) q)
  refine ⟨((e.trans e').trans e'').trans last, out, ?_⟩
  change unroll last.table out = ctor t u v
  rw [hout, law]
  change ctor (unroll e''.table (e''.map (e'.map o)))
    (unroll e''.table (e''.map p)) (unroll e''.table q) = _
  rw [e''.unroll_map, e''.unroll_map, e'.unroll_map, ho, hp, hq]

theorem represent_args (terms : Fin r → View n)
    (h : ∀ i, Representable (terms i)) (table : Table Γ) :
    ∃ e : Extension table, ∃ args : Args e.homes n r,
      unrollArgs e.table args = terms := by
  induction r generalizing Γ with
  | zero =>
    refine ⟨Extension.refl table, .nil, ?_⟩
    funext i
    exact Fin.elim0 i
  | succ r ih =>
    obtain ⟨e, first, hf⟩ := h 0 table
    obtain ⟨e', rest, hr⟩ := ih (fun i => terms i.succ) (fun i => h i.succ) e.table
    refine ⟨e.trans e', .cons (e'.map first) rest, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change unroll e'.table (e'.map first) = terms 0
      rw [e'.unroll_map, hf]
    · exact congrFun hr j

theorem represent_unique (η : UniqueAttrs) (A B s k R : View n)
    (hA : Representable A) (hB : Representable B) (hs : Representable s)
    (hk : Representable k) (hR : Representable R) :
    Representable (.unique rfl η A B s k R) := by
  intro Γ table
  have h : ∀ i, Representable (five A B s k R i) := by
    intro i
    refine Fin.cases hA (fun i => ?_) i
    refine Fin.cases hB (fun i => ?_) i
    refine Fin.cases hs (fun i => ?_) i
    refine Fin.cases hk (fun i => ?_) i
    exact Fin.cases hR (fun j => nomatch j) i
  obtain ⟨e, args, hargs⟩ := represent_args (five A B s k R) h table
  obtain ⟨e', out, hout⟩ := represent_row e.table
    (.unique η (args.get 0) (args.get 1) (args.get 2) (args.get 3) (args.get 4))
  refine ⟨e.trans e', out, ?_⟩
  change unroll e'.table out = Term.unique rfl η A B s k R
  rw [hout]
  simp only [evalRow, ← evalArgs_get]
  change Term.unique rfl η (unrollArgs e.table args 0) (unrollArgs e.table args 1)
    (unrollArgs e.table args 2) (unrollArgs e.table args 3) (unrollArgs e.table args 4) = _
  rw [hargs]
  rfl

theorem represent_inst (body : View r) (actuals : Fin r → View n)
    (hb : Representable body) (ha : ∀ i, Representable (actuals i)) :
    Representable (.inst rfl body actuals) := by
  intro Γ table
  obtain ⟨e, b, hbody⟩ := hb table
  obtain ⟨e', args, hargs⟩ := represent_args actuals ha e.table
  obtain ⟨e'', out, hout⟩ := represent_row e'.table (.inst (e'.map b) args)
  refine ⟨(e.trans e').trans e'', out, ?_⟩
  change unroll e''.table out = Term.inst rfl body actuals
  rw [hout]
  change Term.inst rfl (unroll e'.table (e'.map b)) (unrollArgs e'.table args) = _
  rw [e'.unroll_map, hbody, hargs]

theorem every_view_representable (t : View n) : Representable t := by
  induction t with
  | var i =>
    intro Γ table
    exact ⟨Extension.refl table, .var i, rfl⟩
  | sort u =>
    intro Γ table
    exact represent_row table (.sort u)
  | const name levels =>
    intro Γ table
    exact represent_row table (.const name levels)
  | lit value =>
    intro Γ table
    exact represent_row table (.lit value)
  | app f a ihf iha =>
    exact represent_binary f a ihf iha Term.app Row.app (fun _ _ _ => rfl)
  | lam attrs domain body ihd ihb =>
    exact represent_binary domain body ihd ihb (Term.lam attrs) (Row.lam attrs)
      (fun _ _ _ => rfl)
  | pi attrs domain body ihd ihb =>
    exact represent_binary domain body ihd ihb (Term.pi attrs) (Row.pi attrs)
      (fun _ _ _ => rfl)
  | letE name nondep type value body iht ihv ihb =>
    exact represent_ternary type value body iht ihv ihb
      (Term.letE name nondep) (Row.letE name nondep) (fun _ _ _ _ => rfl)
  | proj name index value ih =>
    exact represent_unary value ih (Term.proj name index) (Row.proj name index)
      (fun _ _ => rfl)
  | unique enabled attrs A B step advance relation ihA ihB ihs ihk ihR =>
    exact represent_unique attrs A B step advance relation ihA ihB ihs ihk ihR
  | inst enabled body actuals ihbody ihactuals =>
    exact represent_inst body actuals ihbody ihactuals

theorem every_view_has_graph (t : View n) : ∃ g : Graph n, g.unroll = t := by
  obtain ⟨e, o, ho⟩ := every_view_representable t Table.empty
  exact ⟨⟨e.homes, e.table, o⟩, ho⟩


end ContextualDAGCoverage
