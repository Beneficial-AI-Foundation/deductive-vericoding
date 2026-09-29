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
6. **Combinator**: `listRecImpl` - the list induction principle

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

/-- Denotation of types to Lean types -/
abbrev Tpe.denote : Tpe → Type
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

notation s "→L" t => Tpe.arrow s t
notation s "×L" t => Tpe.pair s t

/-! ## Typed Trms (PHOAS-style) -/

/-- Typed terms using Parametric Higher-Order Abstract Syntax (PHOAS).
    Following Chlipala's approach, terms are parameterized by a variable
    representation `rep : Tpe → Type`. This allows:
    - Evaluation: instantiate `rep = Tpe.denote` so variables hold values directly
    - Pretty printing: instantiate `rep = fun _ => String` for variable names
    - No context lookup needed - Lean handles substitution automatically -/

/- A tuple consisting of `n` copies of the same type `t` -/
abbrev dup (t : Tpe) : Nat → Tpe
  | 0 => .unit
  | 1 => t
  | n + 2 => .pair t (dup t (n+1))

abbrev dup.toList {t : Tpe} : {d : Nat} → (dup t d).denote → List t.denote
  | 0, _ => []
  | 1, x => [x]
  | _ + 2, ⟨x, xs⟩ => x :: dup.toList xs

abbrev dup.map {s t : Tpe} (f : s.denote → t.denote) : {d : Nat} → (dup s d).denote → (dup t d).denote
  | 0, _ => ()
  | 1, x => f x
  | _ + 2, ⟨x, xs⟩ => (f x, dup.map f xs)

/- A dependent version of `dup.map`: the mapped function additionally receives a
   proof that its argument satisfies `P`, which holds of every entry of the tuple.
   This is what lets `Recursor.fold` below pass the termination checker -- with the
   plain `dup.map` the recursive call is generalized over an arbitrary element of
   `s.denote` and the descent proof is lost. -/
def dup.pmap {s t : Tpe} {P : s.denote → Prop} (f : (y : s.denote) → P y → t.denote) :
    {d : Nat} → (x : (dup s d).denote) → (∀ y ∈ dup.toList x, P y) → (dup t d).denote
  | 0, _, _ => ()
  | 1, x, h => f x (h x (by simp [dup.toList]))
  | _ + 2, ⟨x, xs⟩, h =>
      (f x (h x (by simp [dup.toList])),
       dup.pmap f xs (fun y hy => h y (by simp [dup.toList]; exact Or.inr hy)))

@[simp]
theorem dup.pmap_eq_map {s t : Tpe} {P : s.denote → Prop} {d : Nat} (g : s.denote → t.denote)
    (x : (dup s d).denote) (h : ∀ y ∈ dup.toList x, P y) :
    dup.pmap (fun y _ => g y) x h = dup.map g x := by
  induction d with
  | zero => rfl
  | succ n ih =>
    match n, x with
    | 0, x => rfl
    | n + 1, ⟨x, xs⟩ => simp [dup.pmap, dup.map, ih]

@[simp]
theorem dup.map_map {s t u: Tpe} {d : Nat} (f : s.denote → t.denote) (g : t.denote → u.denote) (x : (dup s d).denote) :
    dup.map g (dup.map f x) = dup.map (g ∘ f) x := by
  induction d; rfl
  expose_names
  induction n; rfl
  grind only [cases eager Prod]

@[simp]
theorem dup.map_id {s: Tpe} {d : Nat} (x : (dup s d).denote) :
    dup.map id x = x := by
  induction d; rfl
  expose_names
  induction n; rfl
  grind only [= id.eq_1, cases eager Prod]

@[simp]
theorem dup.map_toList {s t : Tpe} {d : Nat} (f : s.denote → t.denote) (x : (dup s d).denote) :
    (dup.toList x).map f = dup.toList (dup.map f x) := by
  induction d; rfl
  expose_names
  induction n; rfl
  simp only [toList, List.map_cons, List.cons.injEq, true_and]
  exact h x.2

@[simp]
theorem dup.toList_length {s : Tpe} {d : Nat} (x : (dup s d).denote) :
    (dup.toList x).length = d := by
  induction d; rfl
  expose_names
  induction n; rfl
  simpa [toList] using h x.2

/- A Recursor used for list recursion. Provides oracle access to a splitting function and provides a proof of finite descent. -/
structure Recursor (s u : Tpe) (d : Nat) where
  split : s.denote → u.denote × (dup s d).denote
  unsplit : u.denote × (dup s d).denote → s.denote
  depth : s.denote → Nat
  unsplit_split : ∀ x, depth x > 0 → unsplit (split x) = x
  -- descending : ∀ x, depth x > 0 → dup.foldl (t := .nat) max (dup.map depth (split x).snd) < depth x
  descending : ∀ x, depth x > 0 → ((dup.toList (split x).snd).map depth).foldl max 0 < depth x

/-- The running `max` fold over a list of naturals dominates its starting value. -/
private theorem init_le_foldl_max : ∀ (l : List Nat) (init : Nat), init ≤ l.foldl max init
  | [], _ => Nat.le_refl _
  | b :: l, init => Nat.le_trans (Nat.le_max_left init b) (init_le_foldl_max l (max init b))

/-- Every element of a list of naturals is bounded by its `max` fold. -/
private theorem le_foldl_max {a : Nat} {l : List Nat} :
    ∀ {init : Nat}, a ∈ l → a ≤ l.foldl max init := by
  induction l with
  | nil => intro _ h; cases h
  | cons b l ih =>
    intro init h
    rcases List.mem_cons.mp h with rfl | h'
    · exact Nat.le_trans (Nat.le_max_right init a) (init_le_foldl_max l (max init a))
    · exact ih h'

/- The list recursion function associated with a Recursor `R`.

   The recursive calls are made through `dup.pmap` rather than `dup.map` so that
   each call carries the proof that its argument is smaller than `x`; `R.descending`
   supplies that proof via `le_foldl_max`. See `Recursor.fold_eq` for the unfolding
   equation stated with the plain `dup.map`. -/
def Recursor.fold {s t u : Tpe} {d : Nat} (R : Recursor s u d) (base : s.denote → t.denote)
  (step : u.denote × ((dup s d).denote × (dup t d).denote) → t.denote) (x : s.denote) : t.denote :=
  if hx : R.depth x = 0 then base x else
    step ⟨(R.split x).1, (R.split x).2,
      dup.pmap (P := fun y => R.depth y < R.depth x) (fun y _ => R.fold base step y) (R.split x).2
        (fun y hy => Nat.lt_of_le_of_lt (le_foldl_max (List.mem_map_of_mem hy))
          (R.descending x (Nat.pos_of_ne_zero hx)))⟩
  termination_by (R.depth x)
  decreasing_by
  assumption

/- The defining equation of `Recursor.fold`, phrased with the plain `dup.map`
   (`dup.pmap` is only needed to get the definition past the termination checker). -/
theorem Recursor.fold_eq {s t u : Tpe} {d : Nat} (R : Recursor s u d) (base : s.denote → t.denote)
    (step : u.denote × ((dup s d).denote × (dup t d).denote) → t.denote) (x : s.denote) :
    R.fold base step x =
      if R.depth x = 0 then base x
      else step ⟨(R.split x).1, (R.split x).2, dup.map (R.fold base step) (R.split x).2⟩ := by
  rw [Recursor.fold]
  split <;> simp

inductive Trm' (rep : Tpe → Type) : Tpe → Type where
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
  | listRec {s u t : Tpe} {d : Nat} (rec : Recursor s u d) : Trm' rep (s →L t) →
    Trm' rep ((u ×L ((dup s d) ×L (dup t d))) →L t) → Trm' rep (s →L t)
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
  | _, .listRec _ base step, n =>
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

    Termination: structural recursion on terms, with a nested recursion on
    the input list for `listRec` (using precomputed base/step values). -/
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
  | _, .listRec R base step => R.fold base.eval step.eval
  | _, .true => Bool.true
  | _, .false => Bool.false
  | _, .le e1 e2 => Nat.ble e1.eval e2.eval
  | _, .ite c t e => bif c.eval then t.eval else e.eval
  | _, .head e => match e.eval with | [] => (0 : Nat) | h :: _ => h
  | _, .tail e => match e.eval with | [] => [] | _ :: tl => tl

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
