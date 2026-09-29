import FoundationIntegration

/- Arbitrary-occurrence decomposition over the existing scoped syntax.
   Addresses select occurrences, not all uses of an expression or supplier.
   Arity-indexed frames preserve binder ownership; dependent typing remains
   the separate admitted-source contract. -/
namespace OccurrenceDecomposition
open DerivedViewSyntax

def replace (xs : Fin r → α) (i : Fin r) (x : α) : Fin r → α :=
  fun j => if j = i then x else xs j

theorem replace_self (xs : Fin r → α) (i : Fin r) : replace xs i (xs i) = xs := by
  funext j
  simp only [replace]
  split
  next h => subst j; rfl
  next => rfl

theorem map_replace (f : α → β) (xs : Fin r → α) (i : Fin r) (x : α) :
    (fun j => f (replace xs i x j)) = replace (fun j => f (xs j)) i (f x) := by
  funext j
  simp only [replace]
  split <;> rfl

theorem expand_replace (xs : Fin r → Term d n) (i j : Fin r) (x : Term d n) :
    expand (replace xs i x j) = replace (fun k => expand (xs k)) i (expand x) j :=
  congrFun (map_replace expand xs i x) j

/- Frame d outer home retains the fields needed to rebuild the surrounding
   constructor. Vector frames retain the original vector (including the old
   selected entry); fill overwrites exactly that entry. No minimal-storage
   or selected-value-erasure property is claimed. -/
inductive Frame (d : Bool) : Nat → Nat → Type where
  | appFun (a : Term d n) : Frame d n n
  | appArg (f : Term d n) : Frame d n n
  | lamDomain (attrs : BinderAttrs) (body : Term d (n+1)) : Frame d n n
  | lamBody (attrs : BinderAttrs) (domain : Term d n) : Frame d n (n+1)
  | piDomain (attrs : BinderAttrs) (body : Term d (n+1)) : Frame d n n
  | piBody (attrs : BinderAttrs) (domain : Term d n) : Frame d n (n+1)
  | letType (name : Lean.Name) (nondep : Bool) (value : Term d n)
      (body : Term d (n+1)) : Frame d n n
  | letValue (name : Lean.Name) (nondep : Bool) (type : Term d n)
      (body : Term d (n+1)) : Frame d n n
  | letBody (name : Lean.Name) (nondep : Bool) (type value : Term d n) :
      Frame d n (n+1)
  | projValue (name : Lean.Name) (index : Nat) : Frame d n n
  | uniqueArg (enabled : d = true) (attrs : UniqueAttrs)
      (args : Fin 5 → Term d n) (index : Fin 5) : Frame d n n
  | instBody (enabled : d = true) (actuals : Fin r → Term d n) : Frame d n r
  | instActual (enabled : d = true) (body : Term d r)
      (actuals : Fin r → Term d n) (index : Fin r) : Frame d n n

def Frame.fill : Frame d n m → Term d m → Term d n
  | .appFun a, t => .app t a
  | .appArg f, t => .app f t
  | .lamDomain a b, t => .lam a t b
  | .lamBody a D, t => .lam a D t
  | .piDomain a b, t => .pi a t b
  | .piBody a D, t => .pi a D t
  | .letType a b v body, t => .letE a b t v body
  | .letValue a b T body, t => .letE a b T t body
  | .letBody a b T v, t => .letE a b T v t
  | .projValue a i, t => .proj a i t
  | .uniqueArg h a args i, t =>
      let ys := replace args i t
      .unique h a (ys 0) (ys 1) (ys 2) (ys 3) (ys 4)
  | .instBody h args, t => .inst h t args
  | .instActual h body args i, t => .inst h body (replace args i t)

/- Independent interpretation of a frame accepts an already-decoded hole. -/
def Frame.decode : Frame d n m → Core m → Core n
  | .appFun a, t => .app t (expand a)
  | .appArg f, t => .app (expand f) t
  | .lamDomain a b, t => .lam a t (expand b)
  | .lamBody a D, t => .lam a (expand D) t
  | .piDomain a b, t => .pi a t (expand b)
  | .piBody a D, t => .pi a (expand D) t
  | .letType a b v body, t => .letE a b t (expand v) (expand body)
  | .letValue a b T body, t => .letE a b (expand T) t (expand body)
  | .letBody a b T v, t => .letE a b (expand T) (expand v) t
  | .projValue a i, t => .proj a i t
  | .uniqueArg _ a args i, t =>
      let ys := replace (fun j => expand (args j)) i t
      subst (five (ys 4) (ys 3) (ys 2) (ys 1) (ys 0)) (uniqueTemplate a)
  | .instBody _ args, t => subst (fun i => expand (args i)) t
  | .instActual _ body args i, t =>
      subst (replace (fun j => expand (args j)) i t) (expand body)

theorem Frame.expand_fill (f : Frame d n m) (t : Term d m) :
    expand (f.fill t) = f.decode (expand t) := by
  cases f <;> simp only [Frame.fill, Frame.decode, expand, expand_replace]

inductive Context (d : Bool) : Nat → Nat → Type where
  | hole : Context d n n
  | step (outer : Context d n k) (frame : Frame d k m) : Context d n m

def Context.fill : Context d n m → Term d m → Term d n
  | .hole, t => t
  | .step outer frame, t => outer.fill (frame.fill t)

def Context.decode : Context d n m → Core m → Core n
  | .hole, t => t
  | .step outer frame, t => outer.decode (frame.decode t)

theorem Context.expand_fill (c : Context d n m) (t : Term d m) :
    expand (c.fill t) = c.decode (expand t) := by
  induction c with
  | hole => rfl
  | step outer frame ih =>
      simp only [Context.fill, Context.decode, ih, Frame.expand_fill]

def Context.prepend (f : Frame d n k) : Context d k m → Context d n m
  | .hole => .step .hole f
  | .step outer frame => .step (outer.prepend f) frame

theorem Context.fill_prepend (f : Frame d n k) (c : Context d k m) (t : Term d m) :
    (c.prepend f).fill t = f.fill (c.fill t) := by
  induction c with
  | hole => rfl
  | step outer frame ih => simp only [Context.prepend, Context.fill, ih]

/- These are grammar addresses, not printed variable names or node values. -/
inductive Step where
  | appFun | appArg | lamDomain | lamBody | piDomain | piBody
  | letType | letValue | letBody | projValue
  | uniqueArg (index : Nat) | instBody | instActual (index : Nat)
  deriving DecidableEq, Repr

structure Child (t : Term d n) where
  home : Nat
  frame : Frame d n home
  term : Term d home
  recover : frame.fill term = t

def descend : (t : Term d n) → Step → Option (Child t)
  | .app f a, .appFun => some ⟨_, .appFun a, f, rfl⟩
  | .app f a, .appArg => some ⟨_, .appArg f, a, rfl⟩
  | .lam a D b, .lamDomain => some ⟨_, .lamDomain a b, D, rfl⟩
  | .lam a D b, .lamBody => some ⟨_, .lamBody a D, b, rfl⟩
  | .pi a D b, .piDomain => some ⟨_, .piDomain a b, D, rfl⟩
  | .pi a D b, .piBody => some ⟨_, .piBody a D, b, rfl⟩
  | .letE a h T v b, .letType => some ⟨_, .letType a h v b, T, rfl⟩
  | .letE a h T v b, .letValue => some ⟨_, .letValue a h T b, v, rfl⟩
  | .letE a h T v b, .letBody => some ⟨_, .letBody a h T v, b, rfl⟩
  | .proj a i v, .projValue => some ⟨_, .projValue a i, v, rfl⟩
  | .unique h a A B s k R, .uniqueArg j =>
      if hj : j < 5 then
        let args := five A B s k R
        let i : Fin 5 := ⟨j, hj⟩
        some ⟨_, .uniqueArg h a args i, args i, by
          simp only [Frame.fill, replace_self]
          rfl⟩
      else none
  | .inst h body args, .instBody => some ⟨_, .instBody h args, body, rfl⟩
  | .inst (r := r) h body args, .instActual j =>
      if hj : j < r then
        let i : Fin r := ⟨j, hj⟩
        some ⟨_, .instActual h body args i, args i, by
          simp only [Frame.fill, replace_self]⟩
      else none
  | _, _ => none

structure Extraction (t : Term d n) where
  home : Nat
  context : Context d n home
  component : Term d home
  recover : context.fill component = t

/- The executable operation builds frames; it never saves a whole source
   expression in place of its missing child and never invokes expansion. -/
def extract (t : Term d n) : List Step → Option (Extraction t)
  | [] => some ⟨n, .hole, t, rfl⟩
  | s :: ss => do
      let c ← descend t s
      let e ← extract c.term ss
      return ⟨e.home, e.context.prepend c.frame, e.component, by
        rw [Context.fill_prepend, e.recover, c.recover]⟩

/- Independent constructor membership: no frame, decoder, or extractor
   appears in this definition of a legal child occurrence. -/
inductive IsChild (d : Bool) : {n : Nat} → (t : Term d n) → Step → (m : Nat) → Term d m → Prop where
  | appFun {f a : Term d n} : IsChild d (.app f a) .appFun n f
  | appArg {f a : Term d n} : IsChild d (.app f a) .appArg n a
  | lamDomain {D : Term d n} {b : Term d (n+1)} :
      IsChild d (.lam attrs D b) .lamDomain n D
  | lamBody {D : Term d n} {b : Term d (n+1)} :
      IsChild d (.lam attrs D b) .lamBody (n+1) b
  | piDomain {D : Term d n} {b : Term d (n+1)} :
      IsChild d (.pi attrs D b) .piDomain n D
  | piBody {D : Term d n} {b : Term d (n+1)} :
      IsChild d (.pi attrs D b) .piBody (n+1) b
  | letType {T v : Term d n} {b : Term d (n+1)} :
      IsChild d (.letE name nondep T v b) .letType n T
  | letValue {T v : Term d n} {b : Term d (n+1)} :
      IsChild d (.letE name nondep T v b) .letValue n v
  | letBody {T v : Term d n} {b : Term d (n+1)} :
      IsChild d (.letE name nondep T v b) .letBody (n+1) b
  | projValue {v : Term d n} : IsChild d (.proj name index v) .projValue n v
  | uniqueArg {A B s k R : Term d n} (i : Fin 5) :
      IsChild d (.unique h attrs A B s k R) (.uniqueArg i.val) n (five A B s k R i)
  | instBody {body : Term d r} {args : Fin r → Term d n} :
      IsChild d (.inst h body args) .instBody r body
  | instActual {body : Term d r} {args : Fin r → Term d n} (i : Fin r) :
      IsChild d (.inst h body args) (.instActual i.val) n (args i)

theorem descend_complete (h : IsChild d (n := n) t s m u) :
    ∃ c, descend t s = some c ∧
      (⟨c.home, c.term⟩ : (k : Nat) × Term d k) = ⟨m, u⟩ := by
  cases h <;> simp [descend]

inductive IsOccurrence (d : Bool) : {n : Nat} → (t : Term d n) → List Step → (m : Nat) → Term d m → Prop where
  | root {t : Term d n} : IsOccurrence d t [] n t
  | child {t : Term d n} {child : Term d k} {u : Term d m}
      (hc : IsChild d t step k child) (hp : IsOccurrence d child rest m u) :
      IsOccurrence d t (step :: rest) m u

theorem extract_complete (h : IsOccurrence d (n := n) t path m u) :
    ∃ e, extract t path = some e ∧
      (⟨e.home, e.component⟩ : (k : Nat) × Term d k) = ⟨m, u⟩ := by
  induction h with
  | root => simp [extract]
  | @child n t step k child rest m u hc hp ih =>
      obtain ⟨c, hdesc, heq⟩ := descend_complete hc
      cases c with
      | mk home frame term recover =>
        cases heq
        obtain ⟨e, hextract, hcomponent⟩ := ih
        simpa [extract, hdesc, hextract] using hcomponent

def Extraction.fold {n : Nat} {t : View n} (e : Extraction t) : View n :=
  e.context.fill (.inst rfl e.component Term.var)

theorem identity_call (t : View n) : expand (.inst rfl t Term.var) = expand t := by
  exact subst_id (expand t)

theorem Extraction.fold_exact {n : Nat} {t : View n} (e : Extraction t) :
    expand e.fold = expand t := by
  unfold Extraction.fold
  rw [Context.expand_fill, identity_call, ← Context.expand_fill, e.recover]

theorem Extraction.fold_subst_exact {n : Nat} {t : View n} (e : Extraction t)
    (σ : Fin n → View m) :
    expand (subst σ e.fold) = expand (subst σ t) := by
  rw [expand_subst, expand_subst, e.fold_exact]

/- Replacing the selected component by a contextual application has the
   independently specified decoded action below, regardless of typing. -/
def Extraction.apply {n : Nat} {t : View n} (e : Extraction t) (producer : View r)
    (actuals : Fin r → View e.home) : View n :=
  e.context.fill (.inst rfl producer actuals)

theorem Extraction.apply_decode {n : Nat} {t : View n} (e : Extraction t)
    (producer : View r) (actuals : Fin r → View e.home) :
    expand (e.apply producer actuals) =
      e.context.decode (subst (fun i => expand (actuals i)) (expand producer)) := by
  rw [Extraction.apply, Context.expand_fill]
  rfl

theorem Extraction.fold_source {n : Nat} {t : View n} (e : Extraction t) :
    FoundationIntegration.decodeView e.fold = FoundationIntegration.decodeView t := by
  unfold FoundationIntegration.decodeView
  rw [e.fold_exact]

theorem Extraction.fold_registered_source {registry : List Lean.FVarId} {depth : Nat}
    {t : View (registry.length + depth)} (e : Extraction t) :
    FoundationIntegration.Registered.decodeView registry depth e.fold =
      FoundationIntegration.Registered.decodeView registry depth t := by
  unfold FoundationIntegration.Registered.decodeView
  rw [e.fold_exact]

theorem extract_success_fold (t : View n) (path : List Step) (e : Extraction t)
    (_h : extract t path = some e) : expand e.fold = expand t := e.fold_exact

#print axioms replace_self
#print axioms map_replace
#print axioms expand_replace
#print axioms Frame.expand_fill
#print axioms Context.expand_fill
#print axioms Context.fill_prepend
#print axioms descend_complete
#print axioms extract_complete
#print axioms identity_call
#print axioms Extraction.fold_exact
#print axioms Extraction.fold_subst_exact
#print axioms Extraction.apply_decode
#print axioms Extraction.fold_source
#print axioms Extraction.fold_registered_source
#print axioms extract_success_fold
#print axioms descend
#print axioms extract
end OccurrenceDecomposition
