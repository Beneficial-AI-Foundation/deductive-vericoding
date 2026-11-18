# Deductive vericoding in a small list language

See `DeductiveVericoding/ListLanguage/`.

## The idea

There are two ways to get a program that provably meets a specification. One is to *generate* a
candidate and then try to prove it correct, retrying until the proof goes through. The other is to
*derive* the program from the specification: break the specification into smaller ones, solve those,
and combine the solutions. Each step is a small rule that is proved correct once and for all, so
the finished program needs no separate proof. This project explores the second way, which we call
**deductive vericoding**, in Lean 4.

The setting is deliberately small: a typed functional language over natural numbers and lists of
natural numbers. Small enough that every rule can be proved, and still rich enough to need
recursion, case splits and helper functions. It is large enough to express list reversal, filtering,
partitioning, merging and insertion sort.

## The language

Types are a small universe with a denotation into Lean types (`Basic.lean`):

```lean
inductive Tpe where
  | unit | bool | nat | list
  | pair : Tpe → Tpe → Tpe
  | arrow : Tpe → Tpe → Tpe
```

Terms are written in PHOAS style (`Trm' rep t`), so binding is handled by Lean functions and
evaluation needs no environment. Besides the usual `lam`/`app`/pairs/lists/`le`/`ite`, there is one
recursion construct, parametrized by a **recursor**:

```lean
structure Recursor (s u : Tpe) (d : Nat) where
  split   : s.denote → u.denote × (dup s d).denote
  unsplit : u.denote × (dup s d).denote → s.denote
  depth   : s.denote → Nat
  unsplit_split : ∀ x, depth x > 0 → unsplit (split x) = x
  descending : ∀ x, depth x > 0 → ((dup.toList (split x).2).map depth).foldl max 0 < depth x
```

A recursor says how to split a value into a piece of data (`u`) and `d` smaller values of the same
type, and proves that the splitting terminates. `Recursors.lean` provides:
- `UnCons`, which splits a list into its head and tail;
- `Param`, which carries an extra parameter along with another recursor;
- `Halve`, which splits a list into two halves (the shape merge sort needs).

`listRec R base step` then folds with `R`.

A problem, and its solution, is an `Impl`: a program together with its correctness proof.

```lean
structure Impl (inTpe outTpe : Tpe) (Pre : inTpe.denote → Prop)
    (Post : inTpe.denote → outTpe.denote → Prop) where
  code : Trm (.arrow inTpe outTpe)
  correct : ∀ inp, Pre inp → Post inp (code.eval inp)
```

Stating a problem means writing down the type `Impl I O Pre Post`. For example (`Problems.lean`):

```lean
abbrev ReverseProblem := Impl .list .list (fun _ => True) (fun l out => out = l.reverse)
```

## Combinators: refinement steps you can apply

A **combinator** (`Tactics.lean`) is a Lean function that builds an `Impl` from smaller `Impl`s,
so `apply`-ing it turns one goal into a few simpler ones. Some examples:

- **Leaf closers** produce a constant and leave a plain logical obligation:
  `NilTactic (h : ∀ inp, Pre inp → Post inp []) : Impl t .list Pre Post`.
- **`ConsTactic`** reduces "produce a list" to "produce a head and a tail".
  **`PairTactic`/`Vpair`** split a pair-valued goal into two independent ones.
- **`CasesTactic cond`** produces an `ite`. It leaves three goals: compute the boolean `cond`, solve
  the problem when `cond` holds, and solve it when it doesn't.
- **`RelaxPostTactic`/`RelaxPreTactic`** change the specification instead of the code: replace
  `Post` by a stronger `Post'`, or `Pre` by a weaker `Pre'`.
- **`ListRecTactic R`** is the induction principle. It produces a `listRec` and leaves three goals:
  1. a base case, under the extra precondition `R.depth inp = 0`;
  2. a step case, whose input carries the split-off data, the smaller values and the results of the
     recursive calls on them, with their postconditions available as a precondition;
  3. a proof that the precondition survives the split.
- **`AppTactic`/`IntroTactic`** apply and introduce *helper functions*. A step can call a separately
  derived function on part of its input.

A derivation by hand is ordinary Lean tactic code. Here is `out = inp ++ [1]`, from
`Solutions.lean`:

```lean
def AppendConstantSolution' : AppendConstantProblem := by
  apply ListRecTactic UnCons
  · simp
  · apply ConsTactic
    simp [denote, UnCons.depth_eq_zero_iff, List.append_eq]
    pushpre
    simp
    Vpair
    · apply NumTactic 1
      simp
    · apply NilTactic
      simp
  · simp [Tpe.denote, dup, UnCons]
    pushpre
    apply ConsTactic
    Vpair
    · apply FstTactic
      apply IdentityTactic
      simp
    · apply SndTactic
      apply SndTactic
      apply IdentityTactic
      simp
```

`pushpre` uses an equation in the precondition to rewrite the postcondition. In the step case the
precondition says the recursive result `res` equals `tl ++ [1]`, so `pushpre` turns the goal
`out = hd :: (tl ++ [1])` into `out = hd :: res`. That rewriting is the inductive step.

## `vericode`: searching for the derivation

Since every step is just `apply`ing a combinator, the derivation can be *searched for*.
`vericode` (`VericodeTactic.lean`) is a backtracking search over the combinators, built on aesop
(rule set `VericodeL`). The nine smoke tests at the end of `Solutions.lean`, four of them
recursive, are solved without guidance:

```lean
def AppendSolution''  : AppendProblem  := by vericode
def ReverseSolution'' : ReverseProblem := by vericode
def ConcatSolution''  : ConcatProblem  := by vericode
```

A plain `apply` cannot recover some combinator arguments by unification, so most of the work went
into small **front-ends** that compute those arguments from the goal:

- `projClose` builds a whole chain of projections `inp.2.1` in one step.
- `numClose` reads the constant `n` off `out = n`.
- `LEEqTactic` and `PairEqTactic` handle the shapes `out = Nat.ble a b` and `out = (a, b)`.
- `listRecUC` chooses the recursor from the input type (`UnCons` for `.list`, `Param … UnCons` for
  `_ ×L .list`). It then normalizes the base and step goals and applies `pushpre` once. It refuses
  to recurse when the postcondition doesn't mention the list, or when the precondition already says
  the list is empty.
- `appList` and `introTac` let the search *invent a helper function*: apply a function to a sub-list
  of the input, then derive that function separately.

Reverse shows how these fit together. After one `listRecUC` the step goal is
`out = res ++ [hd]`, which no combinator builds directly. `appList` abstracts `res` and asks for a
helper `f` with `f x = x ++ [hd]`. `introTac` turns that into an ordinary problem with input
`(…, x)`, and a second `listRecUC` solves it: it's the append-constant problem again. The resulting
program is a nested `listRec`, and it runs:

```
#eval ReverseSolution''.code.eval [1,2,3,4]   -- [4, 3, 2, 1]
```

A search can also make choices that look right but fail later. The search rules are tuned with that
in mind:
- Leaf closers are *unsafe* rules. `NilTactic` applies to every list-valued goal, and if its
  obligation turns out false (`inp.1 :: inp.2 = []`), aesop has to be able to backtrack.
- `pushpre` is not a free-standing rule. A step precondition `res = f l` can be used in either
  direction, and as a rule it flips the goal back and forth forever.

The printed programs are correct, but they are full of administrative redexes, since every
combinator wraps its sub-programs in a lambda. `#eval Trm.pretty …` shows them unsimplified; the
programs below are simplified by hand.

## Relational specifications

Every specification in `Problems.lean` *names* its answer (`out = l.reverse`). The interesting
problems don't (`HarderProblems.lean`):

```lean
def FilterSpec : Nat × List Nat → List Nat → Prop := fun (a, l) out =>
  out.Sublist l ∧ (∀ x ∈ out, x ≤ a) ∧ (∀ x ∈ l, x ≤ a → x ∈ out)
```

This specification admits several outputs, and it never mentions the comparison `b ≤ a` that the
program needs. The search gets two more capabilities for this:

- **`relaxPost` with user lemmas.** `vericode [l₁, …]` takes facts *about the specification*. Each
  lemma is used in one of two ways:
  - as a rewrite: an `Iff` whose side conditions are discharged from the precondition;
  - backwards, as an implication: its conclusion is matched against the postcondition, the
    hypotheses that follow from the precondition are discharged, and the rest become the new
    postcondition.

  For Filter the lemmas are:

  ```lean
  theorem FilterSpec_keep (a b : Nat) (l res out : List Nat) (hres : FilterSpec (a, l) res)
      (hb : b ≤ a) (h : out = b :: res) : FilterSpec (a, b :: l) out
  ```

  and `relaxPost` turns the step goal `FilterSpec (a, b :: l) out` into `out = b :: res`. It gets
  `res` from the precondition and `b ≤ a` from the branch condition.

- **`natCases` invents the case split.** The only decisions the language can make are comparisons
  of numbers. So at a goal whose output the postcondition doesn't determine, `natCases` offers one
  `CasesTactic` per comparison of two `.nat` values in the input, and the search picks one. The
  candidates are restricted to comparisons with the element currently being processed.

With these, the derivation is one line:

```lean
def FilterSolution : FilterProblem := by
  vericode [FilterSpec_nil, FilterSpec_keep, FilterSpec_drop]
```

It produces, after simplifying by hand, `listRec(λ _ => [], λ (b, ((a, l), res)) => if b ≤ a then
b :: res else res)`:

```
#eval FilterSolution.code.eval (3, [5,1,4,2,3,7])   -- [1, 2, 3]
```

The lemmas say nothing about *how* to compute the answer. They are true facts about the
specification, and the program falls out of the search. All 13 problems in `HarderProblems.lean`
are solved:

| Problem | Output | How |
|---|---|---|
| Witness, Cmp, UB, Order | a number, boolean or pair from two numbers | `vericode [lemmas]` |
| Perm | any permutation (the identity is found) | `vericode [perm_of_eq]` |
| Append (relational) | `a :: l` reordered with `a` last | `vericode [lemmas]` |
| Filter, Partition | sub-list / pair of lists | `vericode [lemmas]` |
| MaxList, Min, AllLE | folds into `.nat` / `.bool` | `vericode [lemmas]` |
| MinMax | min and max in one pass | guided: the two comparisons are given |
| Merge (of sorted lists) | sorted merge | guided: reuses `InsertionSolution` |

Some sample runs:

```
#eval PartSolution.code.eval (3, [5,1,4,2,3,7])   -- ([1, 2, 3], [5, 4, 7])
#eval OrderSolution.code.eval (7, 2)              -- (2, 7)
#eval MinMaxSolution.code.eval (4, [7,1,9])       -- (1, 9)
```

## A parametrized variant

`ListLanguage/Parametrized/` is a second, de Bruijn-style language. Terms carry a typed parameter
context, and problems are `ImplP Γ t Cond`. It comes with its own search, `vericodeP`. With the
problem-specific definitions handed to it, `vericodeP [insertVal, sorted]` derives insertion sort
outright (`InsertionSort_hacky.lean`). `Translation.lean` translates solutions back into the list
language. Its `.listRec` becomes `listRec` with the `UnCons` recursor, and the translation is proved
to preserve meaning (`toList'_eval`), so `toImpl` turns a solved parametrized problem into a genuine
`ListLanguage.Impl`.

## Limitations

- **Recursion in `vericode`** only uses `UnCons` and `Param UnCons`, always on the last input
  component. `Halve` exists, but nothing derives with it yet; a merge-sort derivation was attempted
  and not finished.
- **The parametrized translation** always goes through `UnCons`.
- **Two of the harder problems are guided.** MinMax needs two nested case splits, which is more
  than the search can afford. Merge needs an insertion helper that the search can't invent.
- **Search cost.** `FilterSolution` needs 4× Lean's default heartbeat budget, and
  `HarderProblems.lean` takes about a minute to build.
- **Specifications must be shaped for the search.** A postcondition headed by `∀` defeats the
  lemma matching (frontier item 2 in `HarderProblems.lean`). Equality tests, testing a list for
  emptiness, folds that return functions, and arithmetic are all out of reach (items 3–6).
- **The output is unsimplified.** There is no simplifier for the synthesized terms yet.

## Where to look

| File | Contents |
|---|---|
| `ListLanguage/Basic.lean` | types, terms, `Recursor`, `Impl` |
| `ListLanguage/Recursors.lean` | `UnCons`, `Param`, `Halve` |
| `ListLanguage/Tactics.lean` | the combinators |
| `ListLanguage/VericodeTactic.lean` | `vericode`, its front-ends, `relaxPost`, `natCases` |
| `ListLanguage/Problems.lean`, `Solutions.lean` | specs; solutions by hand, by combinators, by `vericode` |
| `ListLanguage/InsertionSort.lean` | sorting specs, guided insertion sort |
| `ListLanguage/HarderProblems.lean` | relational specs, their solutions, the frontier |
| `ListLanguage/Parametrized/` | de Bruijn variant, `vericodeP`, verified translation |
