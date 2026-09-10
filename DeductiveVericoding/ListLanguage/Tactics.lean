import DeductiveVericoding.ListLanguage.Basic
import Lean

/- # TACTICS : Here we have a collection of vericoding tactics-/

open ListLanguage

--goal closing tactics

def NilTactic {t : Tpe} {Pre : t.denote → Prop} {Post : t.denote → List Nat → Prop}
  (h : ∀ inp : t.denote, Pre inp → Post inp []) :
    Impl t .list Pre Post :=
  {code := .lam fun _ => .nil, correct := h}

def UnitTactic {t : Tpe} {Pre : t.denote → Prop} {Post : t.denote → Unit → Prop}
  (h : ∀ inp : t.denote, Pre inp → Post inp ()) :
    Impl t .unit Pre Post :=
  {code := .lam fun _ => .unit, correct := h}

def TrueTactic {t : Tpe} {Pre : t.denote → Prop} {Post : t.denote → Bool → Prop}
  (h : ∀ inp : t.denote, Pre inp → Post inp true) :
    Impl t .bool Pre Post :=
  {code := .lam fun _ => .true, correct := h}

def FalseTactic {t : Tpe} {Pre : t.denote → Prop} {Post : t.denote → Bool → Prop}
  (h : ∀ inp : t.denote, Pre inp → Post inp false) :
    Impl t .bool Pre Post :=
  {code := .lam fun _ => .false, correct := h}

def NumTactic {t : Tpe} {Pre : t.denote → Prop} {Post : t.denote → Nat → Prop} (n : Nat)
  (h : ∀ inp : t.denote, Pre inp → Post inp n) :
    Impl t .nat Pre Post :=
  { code := .lam fun _ => .num n, correct := h}

def IdentityTactic {t : Tpe} {Pre : t.denote → Prop} {Post : t.denote → t.denote → Prop}
  (h : ∀ inp : t.denote, Pre inp → Post inp inp) :
    Impl t t Pre Post :=
  { code := .lam fun k => .var k, correct := h}

def ContradictionTactic {s t : Tpe} {Pre : t.denote → Prop} {Post : t.denote → s.denote → Prop}
  (h : ∀ inp, Pre inp → False) :
    Impl t s Pre Post :=
  { code := .lam fun _ => default
    correct inp pre := False.elim <| h inp pre
  }

/- Tactics manipulating lists and pairs-/

/- reduces a list problem to a pair problem -/
def ConsTactic {t : Tpe} {Pre : t.denote → Prop} {Post : t.denote → List Nat → Prop}
  (impl : Impl t (.pair .nat .list) Pre (fun inp ⟨x, xs⟩ => Post inp (x :: xs))) :
    Impl t .list Pre Post :=
  { code := .lam fun k => .cons (.fst (.app impl.code (.var k))) (.snd (.app impl.code (.var k)))
    correct := impl.correct
  }

/- reduces a pair problem to two independent impls-/
def PairTactic {s t u : Tpe} {Pre : s.denote → Prop}
  (Post1 :  s.denote → t.denote → Prop) (Post2 :  s.denote → u.denote → Prop)
  (impl1 : Impl s t Pre Post1)
  (impl2 : Impl s u Pre Post2) :
    Impl s (.pair t u) Pre (fun inp out => Post1 inp out.1 ∧ Post2 inp out.2) :=
  { code := .lam fun k => .mkPair (.app impl1.code (.var k)) (.app impl2.code (.var k))
    correct inp pre := ⟨impl1.correct inp pre, impl2.correct inp pre⟩
  }

def FstTactic {s t u : Tpe} {Pre : s.denote → Prop} {Post : s.denote → t.denote → Prop}
  (impl : Impl s (.pair t u) Pre (fun inp out => Post inp out.1)) :
    Impl s t Pre Post :=
  { code := .lam fun k => .fst (.app impl.code (.var k)), correct := impl.correct }

def SndTactic {s t u : Tpe} {Pre : s.denote → Prop} {Post : s.denote → u.denote → Prop}
  (impl : Impl s (.pair t u) Pre (fun inp out => Post inp out.2)) :
    Impl s u Pre Post :=
  { code := .lam fun k => .snd (.app impl.code (.var k)), correct := impl.correct }

--should be scrapped at some point
def SwapTactic {s t u : Tpe} {Pre : s.denote × t.denote → Prop} {Post : s.denote × t.denote → u.denote → Prop}
  (impl : Impl (.pair t s) u (fun ⟨x, y⟩ => Pre ⟨y, x⟩) (fun ⟨x, y⟩ out => Post ⟨y, x⟩ out)) :
    Impl (.pair s t) u Pre Post :=
  { code := .lam fun k => .app impl.code (.mkPair (.snd (.var k)) (.fst (.var k))),
    correct inp pre := impl.correct ⟨inp.2, inp.1⟩ pre }

/-Recursion Tactics-/

def ListRecTactic {s t : Tpe} {Pre : t.denote × List Nat → Prop} {Post : t.denote × List Nat → s.denote → Prop}
  (h : ∀ p, ∀ x, ∀ xs, Pre ⟨p, (x :: xs)⟩ → Pre ⟨p, xs⟩)
  (base : Impl t s (fun inp ↦ Pre ⟨inp, []⟩) (fun p out ↦ Post (p, []) out))
  (step : Impl (.pair t (.pair s (.pair .nat .list))) s (fun (p, (res, (_, xs))) ↦ Post (p, xs) res) (fun (p, (_, (x, xs))) out ↦ Post (p, (x :: xs)) out)) :
    Impl (.pair t .list) s Pre Post :=
  { code := .listRec base.code step.code
    correct inp pre := by
      obtain ⟨par, l⟩ := inp
      induction l with
      | nil => exact base.correct par (by trivial)
      | cons x xs ih => exact step.correct ⟨_ ,⟨_, ⟨x, xs⟩⟩⟩ (ih <| h par x xs pre)
  }

--version without the parameter t
def ListRecTactic' {s : Tpe} {Pre : List Nat → Prop} {Post : List Nat → s.denote → Prop}
  (h : ∀ x, ∀ xs, Pre (x :: xs) → Pre xs)
  (base : Impl .unit s (fun _ => Pre []) (fun _ out ↦ Post [] out))
  (step : Impl (.pair s (.pair .nat .list)) s (fun (res, (_, xs)) ↦ Post xs res) (fun (_, (x, xs)) out ↦ Post (x :: xs) out)) :
    Impl .list s Pre Post :=
  {
    code := .lam fun k => .app (.listRec base.code (.lam fun l => .app step.code (.snd (.var l)))) (.mkPair .unit (.var k))
    correct inp pre := by
      induction inp with
      | nil => exact base.correct _ (by trivial)
      | cons x xs ih => exact step.correct ⟨_, ⟨x, xs⟩⟩ (ih <| h x xs pre)
  }

--version without actual recursion
def ListRecTactic'' {s : Tpe} {Pre : List Nat → Prop} {Post : List Nat → s.denote → Prop}
  (base : Impl .unit s (fun _ => Pre []) (fun _ out ↦ Post [] out))
  (step : Impl (.pair .nat .list) s (fun (x, xs) => Pre (x :: xs)) (fun (x, xs) out ↦ Post (x :: xs) out)) :
    Impl .list s Pre Post :=
  {
    code := .lam fun k => .app (.listRec base.code (.lam fun l => .app step.code (.snd (.snd (.var l))))) (.mkPair .unit (.var k))
    correct inp pre := by
      induction inp with
      | nil => exact base.correct _ (by trivial)
      | cons x xs _ => exact step.correct ⟨x, xs⟩ pre
  }

/- Finally we need a tactic for relaxing Pre Conditions-/
def RelaxPreTactic {s t : Tpe} (Pre1 Pre2 : s.denote → Prop) {Post :  s.denote → t.denote → Prop}
  (h : ∀ inp, Pre2 inp → Pre1 inp)
  (impl : Impl s t Pre1 Post) :
    Impl s t Pre2 Post :=
  { code := impl.code
    correct inp pre := impl.correct inp <| h inp pre }

/- here the human written tactics end-/

--maybe this is not needed
def SplitTactic (s t u : Tpe) {Pre : s.denote → Prop} (target : s.denote → t.denote) (Post : t.denote → u.denote → Prop)
  (base : Impl s t Pre (fun inp out => out = target inp))
  (step : Impl t u (fun _ => True) Post) :
    Impl s u Pre (fun inp out => Post (target inp) out) :=
  { code := .lam fun k => .app step.code (.app base.code (.var k))
    correct inp pre := by
      have : base.code.eval inp = target inp := base.correct inp pre
      simp [Trm.eval, Trm'.eval, this]
      exact step.correct (target inp) (by trivial)
  }

/- # METATACTICS : Here we have a collection of meta tactics, in order to make applications easier-/

open Lean Elab Tactic Meta

/-- `Tpe.denote t`, as an `Expr`. -/
def denoteExpr (t : Expr) : Expr := mkApp (mkConst ``Tpe.denote) t

/-- One reduction step for a projection out of an explicit pair: `(a, b).1 ↦ a` and
    `(a, b).2 ↦ b`, in both the `Prod.fst`/`Prod.snd` and the raw `Expr.proj` spelling.
    `none` if `e` is not such a redex. -/
def pairProjStep? (e : Expr) : Option Expr :=
  match e with
  | .proj ``Prod i inner =>
      if inner.isAppOfArity ``Prod.mk 4 then inner.getAppArgs[2 + i]? else none
  | _ =>
      if e.isAppOfArity ``Prod.fst 3 && e.appArg!.isAppOfArity ``Prod.mk 4 then
        e.appArg!.getAppArgs[2]?
      else if e.isAppOfArity ``Prod.snd 3 && e.appArg!.isAppOfArity ``Prod.mk 4 then
        e.appArg!.getAppArgs[3]?
      else none

/-- Iterate `pairProjStep?` at the head of `e`. -/
partial def whnfPairProj (e : Expr) : Expr :=
  match pairProjStep? e with
  | some e' => whnfPairProj e'
  | none => e

/-- Reduce every `(a, b).1`/`(a, b).2` redex occurring anywhere in `e`. Needed because a
    postcondition on a pair is usually stated via projections (`fun inp out => out.1 = … ∧
    out.2 = …`), and we inspect it at an explicit pair `(o₁, o₂)` of fresh components. -/
def reducePairProjs (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => return .done (whnfPairProj e))

/-- Take the body of a pair postcondition, already instantiated at two fresh components
    `o₁ o₂` (i.e. `Post inp (o₁, o₂)`), and split it into the bodies of `Post1` and `Post2`.

    The body must reduce to a conjunction `A ∧ B` in which `A` only constrains `o₁` and `B`
    only constrains `o₂` — precisely the shape `PairTactic` concludes with, so the split is
    correct *by definitional unfolding* and needs no extra proof. -/
def splitPairPost (o1 o2 body : Expr) : MetaM (Expr × Expr) := do
  let body ← reducePairProjs (← whnf body)
  unless body.isAppOfArity ``And 2 do
    throwError "Vpair: cannot split the postcondition into one condition per component: it is \
      not a conjunction `A ∧ B`:{indentExpr body}"
  let A := body.appFn!.appArg!
  let B := body.appArg!
  if A.containsFVar o2.fvarId! then
    throwError "Vpair: cannot split the postcondition: its first conjunct also constrains the \
      second component `o₂`:{indentExpr A}"
  if B.containsFVar o1.fvarId! then
    throwError "Vpair: cannot split the postcondition: its second conjunct also constrains the \
      first component `o₁`:{indentExpr B}"
  return (A, B)

/-- The work of `Vpair`: read the component types off the goal's output type, recover the two
    postconditions from the goal's postcondition, and apply `PairTactic`. -/
def vpairCore : TacticM Unit := do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← whnf (← goal.getType))
  unless tgt.isAppOf ``Impl do
    throwError "Vpair: goal is not `Impl s O Pre Post`:{indentExpr tgt}"
  let #[s, O, Pre, Post] := tgt.getAppArgs
    | throwError "Vpair: malformed `Impl` goal:{indentExpr tgt}"
  let Ow ← whnf O
  unless Ow.isAppOfArity ``Tpe.pair 2 do
    throwError "Vpair: the output type of the goal is not a pair:{indentExpr Ow}"
  let #[t, u] := Ow.getAppArgs
    | throwError "Vpair: malformed pair type:{indentExpr Ow}"
  -- Recover `Post1` and `Post2` by inspecting `Post` at an explicit pair of fresh components.
  let (post1, post2) ←
    withLocalDeclD `inp (denoteExpr s) fun inp =>
    withLocalDeclD `o₁ (denoteExpr t) fun o1 =>
    withLocalDeclD `o₂ (denoteExpr u) fun o2 => do
      let out ← mkAppM ``Prod.mk #[o1, o2]
      let (A, B) ← splitPairPost o1 o2 (mkAppN Post #[inp, out])
      return (← mkLambdaFVars #[inp, o1] A, ← mkLambdaFVars #[inp, o2] B)
  let gs ← goal.apply (mkAppN (mkConst ``PairTactic) #[s, t, u, Pre, post1, post2])
  replaceMainGoal gs

/-- **`Vpair` : `PairTactic` with the types and the two postconditions inferred.**

On a goal
```
Impl s (.pair t u) Pre (fun inp out => A[out.1] ∧ B[out.2])
```
`Vpair` reads the component types `t` and `u` off the goal's output type and recovers
`Post1 := fun inp o₁ => A[o₁]` and `Post2 := fun inp o₂ => B[o₂]` from the goal's
postcondition, then applies `PairTactic`. So instead of
```
refine PairTactic (s := …) (t := …) (u := …) (fun inp out => …) (fun inp out => …) ?_ ?_
```
one just writes `Vpair`, which leaves the two independent subgoals `Impl s t Pre Post1` and
`Impl s u Pre Post2`.

The postcondition is inspected at an explicit pair `(o₁, o₂)` of fresh components, so a
postcondition written as a match on the output (`fun inp ⟨x, xs⟩ => …`, as produced by
`ConsTactic`) and one written with projections (`fun inp out => out.1 = … ∧ out.2 = …`, as
produced by `simp`) are both recognised.

A postcondition that is still an *equation* between the built output and a target — `out = (a, b)`
or `out.1 :: out.2 = l` — is not literally a conjunction, and componentwise equality is only
propositionally (not definitionally) the same as equality of the constructed values. `Vpair`
therefore first tries the split as is, and on failure splits the equation with
`simp only [Tpe.denote, Prod.ext_iff, Prod.mk.injEq, List.cons.injEq]` and retries.
It fails, reporting the shape it could not handle, when the two components cannot be
separated — e.g. when a conjunct constrains both of them. -/
elab "Vpair" : tactic => do
  let st ← saveState
  try
    vpairCore
  catch e =>
    st.restore
    -- The postcondition is an equation between the built pair and a target: split it first.
    try
      evalTactic (← `(tactic|
        simp only [Tpe.denote, Prod.ext_iff, Prod.mk.injEq, List.cons.injEq]))
    catch _ =>
      st.restore
      throw e
    try
      vpairCore
    catch _ =>
      st.restore
      throw e
