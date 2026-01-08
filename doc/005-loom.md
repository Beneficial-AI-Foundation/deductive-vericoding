# Loom

Use the machinery in loom to work with monads

## Insertion sort

The following [Loom Velvet code](https://github.com/verse-lab/loom/blob/master/CaseStudies/Velvet/VelvetExamples/Examples.lean)
```
method insertionSort
  (mut arr: Array Int) return (u: Unit)
  require 1 ≤ arr.size
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.size → arr[i]! ≤ arr[j]!
  ensures arr.toMultiset = arrOld.toMultiset
  do
    let mut n := 1
    while n ≠ arr.size
    invariant arr.size = arrOld.size
    invariant 1 ≤ n ∧ n ≤ arr.size
    invariant forall i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i]! ≤ arr[j]!
    invariant arr.toMultiset = arrOld.toMultiset
    done_with n = arr.size
    do
      let mut mind := n
      while mind ≠ 0
      invariant arr.size = arrOld.size
      invariant mind ≤ n
      invariant forall i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
      invariant arr.toMultiset = arrOld.toMultiset
      done_with mind = 0
      do
        if arr[mind]! < arr[mind - 1]! then
          swap! arr[mind - 1]! arr[mind]!
        mind := mind - 1
      n := n + 1
    return
```

unpacks to become
```
def insertionSort : Array ℤ → VelvetM (Unit × Array ℤ) :=
fun arrOld ↦
  have arr := arrOld;
  have n := 1;
  do
  let r ←
    forIn Lean.Loop.mk
        (MProdWithNames.mk' arr (WithName.mk' n (Lean.Name.anonymous.mkStr "n")) (Lean.Name.anonymous.mkStr "arr"))
        fun x r ↦
        have arr := r.fst;
        have n := r.snd.erase;
        do
        invariantGadget
            [WithName (arr.size = arrOld.size) (Lean.Name.anonymous.mkStr "invariant_1"),
              WithName (1 ≤ n ∧ n ≤ arr.size) (Lean.Name.anonymous.mkStr "invariant_2"),
              WithName (∀ (i j : ℕ), 0 ≤ i ∧ i < j ∧ j ≤ n - 1 → arr[i]! ≤ arr[j]!)
                (Lean.Name.anonymous.mkStr "invariant_3"),
              WithName (arr.toMultiset = arrOld.toMultiset) (Lean.Name.anonymous.mkStr "invariant_4")]
        onDoneGadget (WithName (n = arr.size) (Lean.Name.anonymous.mkStr "done_1"))
        decreasingGadget none
        if n ≠ arr.size then
            have mind := n;
            do
            let r ←
              forIn Lean.Loop.mk
                  (MProdWithNames.mk' arr (WithName.mk' mind (Lean.Name.anonymous.mkStr "mind"))
                    (Lean.Name.anonymous.mkStr "arr"))
                  fun x r ↦
                  have arr := r.fst;
                  have mind := r.snd.erase;
                  do
                  invariantGadget
                      [WithName (arr.size = arrOld.size) (Lean.Name.anonymous.mkStr "invariant_5"),
                        WithName (mind ≤ n) (Lean.Name.anonymous.mkStr "invariant_6"),
                        WithName (∀ (i j : ℕ), 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!)
                          (Lean.Name.anonymous.mkStr "invariant_7"),
                        WithName (arr.toMultiset = arrOld.toMultiset) (Lean.Name.anonymous.mkStr "invariant_8")]
                  onDoneGadget (WithName (mind = 0) (Lean.Name.anonymous.mkStr "done_2"))
                  decreasingGadget none
                  if mind ≠ 0 then
                      have __do_jp := fun arr mind y ↦
                        have mind := mind - 1;
                        do
                        pure PUnit.unit
                        pure
                            (ForInStep.yield
                              (MProdWithNames.mk' arr (WithName.mk' mind (Lean.Name.anonymous.mkStr "mind"))
                                (Lean.Name.anonymous.mkStr "arr")));
                      if arr[mind]! < arr[mind - 1]! then
                        have lhs := arr[mind - 1]!;
                        have rhs := arr[mind]!;
                        have arr := arr.set! (mind - 1) rhs;
                        have arr := arr.set! mind lhs;
                        do
                        let y ← pure PUnit.unit
                        __do_jp arr mind y
                      else do
                        let y ← pure PUnit.unit
                        __do_jp arr mind y
                    else
                      pure
                        (ForInStep.done
                          (MProdWithNames.mk' arr (WithName.mk' mind (Lean.Name.anonymous.mkStr "mind"))
                            (Lean.Name.anonymous.mkStr "arr")))
            match r with
              | { fst := arr, snd := mind } =>
                have n := n + 1;
                do
                pure PUnit.unit
                pure
                    (ForInStep.yield
                      (MProdWithNames.mk' arr (WithName.mk' n (Lean.Name.anonymous.mkStr "n"))
                        (Lean.Name.anonymous.mkStr "arr")))
          else
            pure
              (ForInStep.done
                (MProdWithNames.mk' arr (WithName.mk' n (Lean.Name.anonymous.mkStr "n"))
                  (Lean.Name.anonymous.mkStr "arr")))
  match r with
    | { fst := arr, snd := n } => pure ((), arr)
```

## Explanation of how Loom works 

The following explanation was generated by Claude Code.

### Transformation Pipeline Overview

``` 
Velvet DSL (method)
    ↓
Monadic Computation (VelvetM = NonDetT DivM)
    ↓
Hoare Triple (triple pre computation post)
    ↓
Weakest Precondition Goals
    ↓
Elementary Constraints → Solved by grind/SMT
```

### Step 1: The method Macro → Monadic Computation

The method macro in CaseStudies/Velvet/Syntax.lean:68-71 transforms Velvet syntax into a monadic computation:

-- Your Velvet code:
```
method insertionSort (mut arr: Array Int) return (u: Unit)
  require 1 ≤ arr.size
  ensures ...
  do ...
```

-- Becomes a definition like:
```
def insertionSort (arrOld: Array Int) : VelvetM (Unit × Array Int) := ...
```

Key transformations:
- Mutable parameters (mut arr: Array Int) create an arrOld binding for the pre-state
- Returns are wrapped as tuples (retValue, mutVar1, mutVar2, ...) when mutable vars exist
- The body is elaborated into VelvetM which is defined in VelvetTheory.lean:3 as:

abbrev VelvetM α := NonDetT DivM α

### Step 2: prove_correct → Hoare Triple

The prove_correct command (Syntax.lean:328-367) generates a lemma with the Hoare triple form:

```
@[loomSpec]
lemma insertionSort_correct (arrOld: Array Int) :
  triple
    (1 ≤ arrOld.size)                    -- precondition
    (insertionSort arrOld)                -- computation
    (fun (u, arr) =>                      -- postcondition
      (∀ i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.size → arr[i]! ≤ arr[j]!) ∧
      (arr.toMultiset = arrOld.toMultiset))
```

Where triple is defined in Loom/MonadAlgebras/WP/Basic.lean:20-22:

```
def triple (pre : l) (c : m α) (post : α -> l) : Prop :=
  pre ≤ wp c post
```

### Step 3: Weakest Precondition Semantics

The core WP is computed using Monad Transformer Algebras (Loom/MonadAlgebras/Defs.lean:58-59):

```
def wp (c : m α) (post : α -> l) : l := liftM (n := Cont l) c post
```

WP rules for key operations:
- pure: wp (pure x) post = post x
- bind: wp (x >>= f) post = wp x (λ x => wp (f x) post)
- demonic choice (while loops): wp (pick p) post = ⨅ a ∈ p, post a (infimum = all branches must satisfy)

For NonDetT specifically (Loom/MonadAlgebras/NonDetT/Basic.lean:86-95):
```
def NonDetT.wp : NonDetT m α -> Cont l α
  | .pickCont τ p f => fun post => ⨅ a ∈ p, wp (f a) post  -- Universal quantification
  | .repeatCont init f cont => fun post => ⨆ inv, ...      -- Loop invariant handling
```

### Step 4: loom_solve Tactic

The loom_solve tactic (CaseStudies/Tactic.lean:121-156) orchestrates proof:

1. loom_goals_intro - Sets up the goal structure
2. wpgen - Automatically generates WP by pattern-matching on monadic structure
3. loom_solver - Delegates to backend (grind, Z3, or CVC5)

The wpgen tactic (Loom/MonadAlgebras/WP/Tactic.lean:71-142) recursively walks the monadic computation:
- Matches on pure, bind, match expressions
- Looks up @[loomSpec] lemmas for verified sub-methods
- Generates WPGen structures that soundly approximate the true WP

### Concrete Example: While Loop

For the outer while loop in insertionSort:

```
while n ≠ arr.size
invariant arr.size = arrOld.size
invariant 1 ≤ n ∧ n ≤ arr.size
invariant forall i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i]! ≤ arr[j]!
invariant arr.toMultiset = arrOld.toMultiset
done_with n = arr.size
do ...
```

The WP involves:
1. Invariant must hold initially (from precondition)
2. Invariant is preserved by each iteration (inductive case)
3. Invariant + termination condition implies postcondition (final case)

These become separate proof goals that loom_solve dispatches to the solver.

### Key Files Summary

| File                                  | Purpose                             |
|---------------------------------------|-------------------------------------|
| CaseStudies/Velvet/Syntax.lean        | method macro, prove_correct command |
| CaseStudies/Velvet/VelvetTheory.lean  | VelvetM monad definition            |
| Loom/MonadAlgebras/WP/Basic.lean      | wp, triple definitions              |
| Loom/MonadAlgebras/NonDetT/Basic.lean | WP for non-determinism/loops        |
| CaseStudies/Tactic.lean               | loom_solve, loom_solver tactics     |
| Loom/MonadAlgebras/WP/Tactic.lean     | wpgen automatic WP generation       |

## Main take-away

The core machinary of weakest preconditions (WP) is clarified as the monadLift of a monad program to the monad of $L$-continuations, where $L$ is some complete lattice. In Loom, $L$ is chosen to be `Prop`, where the lattice relation $P \rightarrow Q$ is given by implication. This way of defining WP is more general than what the Std.Do framework does (which looks at SPred continuations where SPred is an deep embedding of Prop in Lean).

It then defines a Triple ${P}c{Q}$ to be $P \leq \text{wp} \,c \,Q$ in the lattice $L$. We can use this notion of Triple for deductive vericoding. Namely, we define goals as triples. Then, given a goal, we can decompose it into smaller goals using tactics (which apply lemmas involving composition of goals).