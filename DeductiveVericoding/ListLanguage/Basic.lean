/-!
# Verified Sorting via List Induction

This module synthesizes correct-by-construction sorting algorithms using the
list induction principle, following the Codable pattern.

## Structure

1. **Type Universe**: `Tpe` - types in our DSL (unit, nat, list, pair, arrow)
2. **PHOAS Syntax**: `Trm' rep : Tpe → Type` - Parametric Higher-Order Abstract Syntax
3. **Closed Terms**: `Trm t = {rep : Tpe → Type} → Trm' rep t`
4. **Context-free Semantics**: `Trm'.eval` - no variable lookup needed
5. **Refinement Types**: `Impl` with pre/postconditions as subtypes
6. **Combinators**: `ListRecTactic` & co. - the list induction principle

## PHOAS-Style Typed Terms

Following Chlipala's PHOAS approach, terms are parameterized by a variable
representation `rep : Tpe → Type`. This allows:
- **Evaluation**: instantiate `rep = Tpe.denote` so variables hold values directly
- **Pretty printing**: instantiate `rep = fun _ => String` for variable names
- **No context lookup**: Lean handles substitution automatically

```
inductive Trm' (rep : Tpe → Type) : Tpe → Type where
  | var : rep t → Trm' rep t
  | lam : (rep t → Trm' rep u) → Trm' rep (.arrow t u)  -- Lean function!
  | app : Trm' rep (.arrow t u) → Trm' rep t → Trm' rep u
  ...
```

## The List Induction Principle

Given `Inv : List Nat → List Nat → Prop` relating input to output:
- Base implementation: `BaseImpl Inv` proving `Inv [] (base.code.eval ())`
- Step implementation: `StepImpl Inv` proving the step preserves invariant

We construct: `ListImpl ListPre (ListPost Inv)`

For sorting, `Sorted inp out = Ordered out ∧ List.Perm inp out`.

## References
- Adam Chlipala, "Parametric Higher-Order Abstract Syntax for Mechanized Semantics" (ICFP 2008)
- Adam Chlipala, "Certified Programming with Dependent Types"
- Jin-Xing Lim, "Formalization of divide-and-conquer algorithm in Coq" (Appendix A)
-/

namespace ListLanguage

/-! ## Type Universe (CPDT-style) -/

/-- Types in our DSL -/
inductive Tpe where
  | unit : Tpe
  | bool : Tpe
  | nat : Tpe
  | list : Tpe
  | pair : Tpe → Tpe → Tpe
  | arrow : Tpe → Tpe → Tpe
  deriving Repr, BEq, DecidableEq

/-- Denotation of types to Lean types.

`@[reducible]` so that typeclass synthesis (which runs at `.instances` transparency and does
*not* unfold ordinary definitions) can see that a goal like `ListLike Tpe.list.denote
Tpe.nat.denote` is really `ListLike (List Nat) Nat`. Without it every `listRec` construction
site would have to pass its `ListLike` instance by hand. -/
@[reducible] def Tpe.denote : Tpe → Type
  | .unit => Unit
  | .bool => Bool
  | .nat => Nat
  | .list => List Nat
  | .pair t u => t.denote × u.denote
  | .arrow t u => t.denote → u.denote

/-- Default value for each type -/
instance instInhabitedDenote : (t : Tpe) → Inhabited t.denote
  | .unit => inferInstanceAs (Inhabited Unit)
  | .bool => inferInstanceAs (Inhabited Bool)
  | .nat => inferInstanceAs (Inhabited Nat)
  | .list => inferInstanceAs (Inhabited (List Nat))
  | .pair t u => ⟨(instInhabitedDenote t).default, (instInhabitedDenote u).default⟩
  | .arrow _t u => ⟨fun _ => (instInhabitedDenote u).default⟩

/-! ## `ListLike`: types that are lists

`listRec` below recurses over an arbitrary `ListLike` type rather than over `List Nat`.
The class says exactly what list recursion needs: a `nil`, a `cons`, and the statement
that *nothing else is in the type* — every element is reachable from `nil` by `cons`es.

That last statement has to be **constructive**: `Trm'.eval` produces data (`s.denote`) by
recursing on the container, and a `Prop`-valued `∀ a, ∃ l, foldr cons nil l = a` cannot be
eliminated into `Type`. So reachability is packaged as a dependent eliminator `elim`
together with its two computation rules. There is deliberately no `fold` field: a fold is
`elim` at a constant motive, and `Prop`-valued induction (`ListLike.ind`) is `elim` at a
`PLift` motive.
-/

/-- `α` is a list of `β`s: it has `nil` and `cons`, and every element of `α` is reachable
from `nil` by `cons`es — stated constructively as a dependent eliminator plus its two
computation rules.

The eliminator cannot be called `rec`/`recOn`/`casesOn`, which are taken by the
auto-generated eliminators of the class structure itself. -/
class ListLike (α : Type) (β : outParam Type) where
  nil : α
  cons : β → α → α
  /-- Every element of `α` is reachable from `nil` by `cons`es: recursion principle. -/
  elim {motive : α → Type} (base : motive nil)
    (step : (b : β) → (a : α) → motive a → motive (cons b a)) : (a : α) → motive a
  elim_nil {motive : α → Type} (base : motive nil)
    (step : (b : β) → (a : α) → motive a → motive (cons b a)) :
    elim base step nil = base
  elim_cons {motive : α → Type} (base : motive nil)
    (step : (b : β) → (a : α) → motive a → motive (cons b a)) (b : β) (a : α) :
    elim base step (cons b a) = step b a (elim base step a)

attribute [simp] ListLike.elim_nil ListLike.elim_cons

/-- `Prop`-valued induction, obtained from `elim` at a `PLift` motive. This is the reason
`elim` has to be *dependent*: a non-dependent fold cannot recover it. -/
theorem ListLike.ind {α β : Type} [ListLike α β] {motive : α → Prop}
    (base : motive ListLike.nil)
    (step : ∀ (b : β) (a : α), motive a → motive (ListLike.cons b a)) : ∀ a, motive a :=
  fun a => (ListLike.elim (motive := fun a => PLift (motive a))
    (PLift.up base) (fun b a ih => PLift.up (step b a ih.down)) a).down

/-- `List`'s own dependent recursor, written as structural recursion so that it has a code
generator (`List.rec` does not). -/
def listElim {β : Type} {motive : List β → Type} (base : motive [])
    (step : (b : β) → (l : List β) → motive l → motive (b :: l)) : (l : List β) → motive l
  | [] => base
  | b :: l => step b l (listElim base step l)

instance List_ListLike {β : Type} : ListLike (List β) β where
  nil := []
  cons := List.cons
  elim base step := listElim base step
  elim_nil _ _ := rfl
  elim_cons _ _ _ _ := rfl

/-- Bridge the class operations back to `List` notation. Without these the goals produced
by the generalized `ListRec*` combinators mention `ListLike.cons`, and every downstream
proof — written about `x :: xs` — stops matching. -/
@[simp] theorem ListLike.nil_list {β : Type} : (ListLike.nil : List β) = [] := rfl

@[simp] theorem ListLike.cons_list {β : Type} (b : β) (l : List β) :
    ListLike.cons b l = b :: l := rfl

/-- The recursion scheme that `listRec` evaluates to: fold the container, handing the step
the head, the tail, and the recursive result on the tail.

This is `ListLike.elim` at a constant motive, but it is given its own name on purpose. The
whole tactic layer reasons by `simp [Trm.eval, Trm'.eval]`, which unfolds `Trm'.eval`
completely; with the fold inlined, every goal would be a raw `elim` application and the
`listRec` equations below could never fire. Keeping it folded is the same trick
`Parametrized.listFold` uses. -/
def listFold {α β γ : Type} [ListLike α β] (base : γ) (step : β → α → γ → γ) : α → γ :=
  ListLike.elim (motive := fun _ => γ) base step

@[simp] theorem listFold_nil {α β γ : Type} [ListLike α β] (base : γ) (step : β → α → γ → γ) :
    listFold base step ListLike.nil = base :=
  ListLike.elim_nil (motive := fun _ => γ) base step

@[simp] theorem listFold_cons {α β γ : Type} [ListLike α β] (base : γ) (step : β → α → γ → γ)
    (b : β) (a : α) :
    listFold base step (ListLike.cons b a) = step b a (listFold base step a) :=
  ListLike.elim_cons (motive := fun _ => γ) base step b a

/-- `listFold`'s equations in `List` notation, for the same reason as `elim_*_list`. -/
@[simp] theorem listFold_nil_list {β γ : Type} (base : γ) (step : β → List β → γ → γ) :
    listFold (α := List β) base step [] = base := rfl

@[simp] theorem listFold_cons_list {β γ : Type} (base : γ) (step : β → List β → γ → γ)
    (b : β) (l : List β) :
    listFold (α := List β) base step (b :: l) = step b l (listFold base step l) := rfl

/-- Bridges the `Tpe` universe to `ListLike`: `c` is a `Tpe` whose denotation is a container
of `e.denote`s.

Why this exists rather than using `ListLike c.denote e.denote` directly at every call site:
instance search can solve `ListLike (List Nat) Nat` and, thanks to `Tpe.denote` being
reducible, also `ListLike Tpe.list.denote Tpe.nat.denote`. But when only the container `c` is
known — which is the situation at every `ListRec*` goal — it would have to *recover* `e : Tpe`
from `e.denote = Nat`, and `Tpe.denote` is not invertible by unification. Keying the class on
the `Tpe`s themselves makes `e` an honest output parameter. -/
class ListTpe (c : Tpe) (e : outParam Tpe) where
  toListLike : ListLike c.denote e.denote

attribute [instance] ListTpe.toListLike

instance ListTpe_list : ListTpe .list .nat := ⟨List_ListLike⟩

/-! ## Typed Trms (PHOAS-style) -/

/-- Typed terms using Parametric Higher-Order Abstract Syntax (PHOAS).
    Following Chlipala's approach, terms are parameterized by a variable
    representation `rep : Tpe → Type`. This allows:
    - Evaluation: instantiate `rep = Tpe.denote` so variables hold values directly
    - Pretty printing: instantiate `rep = fun _ => String` for variable names
    - No context lookup needed - Lean handles substitution automatically

    Note the result universe: `Trm'` stores a `ListTpe` instance in `listRec`, and that
    instance lives in `Type 1` (`ListLike.elim` quantifies over a motive `α → Type`), so the
    term type cannot stay in `Type 0`. Nothing else about the language changes: `Tpe.denote`
    is still `Type 0`-valued and `Trm'.eval` is an ordinary large elimination. -/
inductive Trm' (rep : Tpe → Type) : Tpe → Type 1 where
  | unit : Trm' rep .unit
  | nil : Trm' rep .list
  | num : Nat → Trm' rep .nat
  | cons : Trm' rep .nat → Trm' rep .list → Trm' rep .list
  | var : {t : Tpe} → rep t → Trm' rep t
  | mkPair : {t u : Tpe} → Trm' rep t → Trm' rep u → Trm' rep (.pair t u)
  | fst : {t u : Tpe} → Trm' rep (.pair t u) → Trm' rep t
  | snd : {t u : Tpe} → Trm' rep (.pair t u) → Trm' rep u
  | lam : {t u : Tpe} → (rep t → Trm' rep u) → Trm' rep (.arrow t u)
  | app : {t u : Tpe} → Trm' rep (.arrow t u) → Trm' rep t → Trm' rep u
  /-- List recursion over any `ListLike` type: `c` is the container being recursed over and
      `e` its element type. The step receives the parameter, the recursive result on the
      tail, the head, and the tail. -/
  | listRec {s t c e : Tpe} [ListTpe c e] : Trm' rep (.arrow t s) →
    Trm' rep (.arrow (.pair t (.pair s (.pair e c))) s) →
    Trm' rep (.arrow (.pair t c) s)
  -- Boolean operations
  | true : Trm' rep .bool
  | false : Trm' rep .bool
  | le : Trm' rep .nat → Trm' rep .nat → Trm' rep .bool
  | ite : {t : Tpe} → Trm' rep .bool → Trm' rep t → Trm' rep t → Trm' rep t
  -- List operations
  | head : Trm' rep .list → Trm' rep .nat   -- returns 0 for empty list
  | tail : Trm' rep .list → Trm' rep .list  -- returns [] for empty list

/-- Default value for each term -/
instance instInhabitedTrm' {rep : Tpe → Type} : (t : Tpe) → Inhabited (Trm' rep t)
  | .unit => ⟨.unit⟩
  | .bool => ⟨.false⟩
  | .nat => ⟨.num 0⟩
  | .list => ⟨.nil⟩
  | .pair t u => ⟨.mkPair (instInhabitedTrm' t).default (instInhabitedTrm' u).default⟩
  | .arrow _ u => ⟨.lam fun _ => (instInhabitedTrm' u).default⟩

/-- Closed terms are polymorphic over all variable representations -/
def Trm (t : Tpe) := {rep : Tpe → Type} → Trm' rep t

/-- Pretty-print a type -/
def Tpe.pretty : Tpe → String
  | .unit => "Unit"
  | .bool => "Bool"
  | .nat => "Nat"
  | .list => "List"
  | .pair t u => s!"({t.pretty} × {u.pretty})"
  | .arrow t u => s!"({t.pretty} → {u.pretty})"

/-- Pretty-print a term with string variables.
    Uses a counter to generate fresh variable names. -/
def Trm'.prettyAux : {t : Tpe} → Trm' (fun _ => String) t → Nat → String × Nat
  | _, .unit, n => ("()", n)
  | _, .nil, n => ("[]", n)
  | _, .num k, n => (toString k, n)
  | _, .cons hd tl, n =>
      let (hds, n1) := hd.prettyAux n
      let (tls, n2) := tl.prettyAux n1
      (s!"{hds} :: {tls}", n2)
  | _, .var x, n => (x, n)
  | _, .mkPair e1 e2, n =>
      let (s1, n1) := e1.prettyAux n
      let (s2, n2) := e2.prettyAux n1
      (s!"({s1}, {s2})", n2)
  | _, .fst e, n =>
      let (s, n1) := e.prettyAux n
      (s!"{s}.1", n1)
  | _, .snd e, n =>
      let (s, n1) := e.prettyAux n
      (s!"{s}.2", n1)
  | _, .lam (t := ty) f, n =>
      let name := s!"x{n}"
      let (body, n') := (f name).prettyAux (n + 1)
      (s!"(λ {name} : {ty.pretty} => {body})", n')
  | _, .app f arg, n =>
      let (fs, n1) := f.prettyAux n
      let (args, n2) := arg.prettyAux n1
      (s!"{fs}({args})", n2)
  | _, @Trm'.listRec _ _ _ _ _ _ base step, n =>
      let (bs, n1) := base.prettyAux n
      let (ss, n2) := step.prettyAux n1
      (s!"listRec({bs}, {ss})", n2)
  | _, .true, n => ("true", n)
  | _, .false, n => ("false", n)
  | _, .le e1 e2, n =>
      let (s1, n1) := e1.prettyAux n
      let (s2, n2) := e2.prettyAux n1
      (s!"{s1} ≤ {s2}", n2)
  | _, .ite c t e, n =>
      let (sc, n1) := c.prettyAux n
      let (st, n2) := t.prettyAux n1
      let (se, n3) := e.prettyAux n2
      (s!"if {sc} then {st} else {se}", n3)
  | _, .head e, n =>
      let (s, n1) := e.prettyAux n
      (s!"head({s})", n1)
  | _, .tail e, n =>
      let (s, n1) := e.prettyAux n
      (s!"tail({s})", n1)

/-- Pretty-print a closed term -/
def Trm.pretty {t : Tpe} (e : Trm t) : String :=
  (e.prettyAux 0).1

instance {t : Tpe} : ToString (Trm t) := ⟨Trm.pretty⟩

/-! ## Semantics -/

/-- Evaluate a term with `rep = Tpe.denote`.
    Variables hold their values directly - no context lookup needed!
    This is the key PHOAS insight: Lean handles substitution automatically.

    Termination: structural recursion on terms. `listRec` does not recurse on terms at
    all — the recursion over the container is `listFold`, i.e. the `elim` of the instance
    stored in the constructor. -/
def Trm'.eval : {t : Tpe} → Trm' Tpe.denote t → t.denote
  | _, .unit => ()
  | _, .nil => []
  | _, .num n => n
  | _, .cons hd tl => hd.eval :: tl.eval
  | _, .var x => x  -- x is already the value!
  | _, .mkPair e1 e2 => (e1.eval, e2.eval)
  | _, .fst e => e.eval.1
  | _, .snd e => e.eval.2
  | _, .lam f => fun v => (f v).eval  -- Lean handles binding
  | _, .app f arg => f.eval arg.eval
  -- the instance has to be named: in a pattern an instance-implicit argument is
  -- *synthesized*, not bound, and here `c`/`e` are still metavariables
  | _, @Trm'.listRec _ _ _ _ _ inst base step => fun (par, l) =>
      @listFold _ _ _ inst.toListLike (base.eval par)
        (fun a tl res => step.eval (par, (res, (a, tl)))) l
  | _, .true => Bool.true
  | _, .false => Bool.false
  | _, .le e1 e2 => Nat.ble e1.eval e2.eval
  | _, .ite c t e => bif c.eval then t.eval else e.eval
  | _, .head e => match e.eval with | [] => (0 : Nat) | h :: _ => h
  | _, .tail e => match e.eval with | [] => [] | _ :: tl => tl

/-! The two equations for `listRec` evaluation. These replace the equation lemmas that the
old `let rec go` used to export under the generated name `Trm'.eval.go`; being ordinary
theorems, they survive any future reshaping of the definition. -/

@[simp] theorem Trm'.eval_listRec_nil {s t c e : Tpe} [ListTpe c e]
    (base : Trm' Tpe.denote (.arrow t s))
    (step : Trm' Tpe.denote (.arrow (.pair t (.pair s (.pair e c))) s))
    (par : t.denote) :
    (Trm'.listRec base step).eval (par, ListLike.nil) = base.eval par := by
  simp [Trm'.eval]

@[simp] theorem Trm'.eval_listRec_cons {s t c e : Tpe} [ListTpe c e]
    (base : Trm' Tpe.denote (.arrow t s))
    (step : Trm' Tpe.denote (.arrow (.pair t (.pair s (.pair e c))) s))
    (par : t.denote) (a : e.denote) (tl : c.denote) :
    (Trm'.listRec base step).eval (par, ListLike.cons a tl)
      = step.eval (par, ((Trm'.listRec base step).eval (par, tl), (a, tl))) := by
  simp [Trm'.eval]

/-- Evaluate a closed term -/
def Trm.eval {t : Tpe} (e : Trm t) : t.denote :=
  (e (rep := Tpe.denote)).eval

/-! ## Impl -/

/-- General implementation structure with embedded correctness proof.

    Parameters:
    - `inTpe` : the DSL input type
    - `outTpe` : the DSL output type
    - `Pre` : precondition on parameter and input
    - `Post` : postcondition relating parameter, input, and output (also receives proof of Pre)

    The code type is `.arrow inTpe outTpe`, so `code.eval : inTpe.denote → outTpe.denote`. -/
structure Impl (inTpe outTpe : Tpe)
    (Pre : inTpe.denote → Prop)
    (Post : inTpe.denote → outTpe.denote → Prop) where
  /-- The term implementing the function -/
  code : Trm (.arrow inTpe outTpe)
  /-- Correctness: precondition implies postcondition after evaluation -/
  correct : ∀ inp, Pre inp → Post inp (code.eval inp)

end ListLanguage
