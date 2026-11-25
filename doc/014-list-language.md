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

The programs live in a small, made-up programming language (`Basic.lean`). Its types are `unit`,
`bool`, `nat`, `list` (lists of naturals), pairs `s ⊗ t`, and functions `s ⇒ t`. Terms are
what you would expect: numbers, `true`/`false`, a comparison `le`, `if … then … else`, pairs with
their projections, and lambda and application. Lists have two constructors, `nil` and `cons`.

Types of the language are just data (an inductive type `Tpe`). `Tpe.denote` maps each of them to
the Lean type its values live in, so that specifications can talk about inputs and outputs using
ordinary Lean functions and lemmas (`List.reverse`, `List.Perm`, `≤`, …):

```lean
abbrev Tpe.denote : Tpe → Type
  | .unit => Unit
  | .bool => Bool
  | .nat => Nat
  | .list => List Nat
  | t ⊗ u => t.denote × u.denote
  | t ⇒ u => t.denote → u.denote
```

The language's own symbols `⊗` and `⇒` keep its types apart from Lean's `×` and `→`, which are
what they denote. A program of type `t` evaluates to a value of type `t.denote`: a program of type
`list ⇒ list` evaluates to an actual Lean function `List Nat → List Nat`.

## Problems and combinators

A **problem** is a type `Impl I O Pre Post`, and a solution is a program from `I` to `O` together
with a proof that it maps inputs satisfying `Pre` to outputs satisfying `Post`:

```lean
structure Impl (inTpe outTpe : Tpe) (Pre : inTpe.denote → Prop)
    (Post : inTpe.denote → outTpe.denote → Prop) where
  code : Trm (inTpe ⇒ outTpe)
  correct : ∀ inp, Pre inp → Post inp (code.eval inp)
```

Stating a problem means writing down such a type. The simplest kind of problem names its answer
outright, e.g. "return the list `[1, 2, 3]`" (`Problems.lean`):

```lean
abbrev List123Problem := Impl .unit .list (fun _ => True) (fun _ out => out = [1,2,3])
```

### Combinators

A **combinator** (`Tactics.lean`) is a Lean function that builds an `Impl` from smaller `Impl`s.
It's a refinement rule with its proof built in, so `apply`-ing it turns one goal into a few simpler
ones. Three small examples:

`NilTactic` returns the empty list. Its only requirement is a plain logical fact: the empty list
satisfies the postcondition.

```lean
def NilTactic {t : Tpe} {Pre : t.denote → Prop} {Post : t.denote → List Nat → Prop}
  (h : ∀ inp : t.denote, Pre inp → Post inp []) :
    Impl t .list Pre Post :=
  {code := .lam fun _ => .nil, correct := h}
```

`IdentityTactic` returns the input unchanged, provided the input itself satisfies the
postcondition.

```lean
def IdentityTactic {t : Tpe} {Pre : t.denote → Prop} {Post : t.denote → t.denote → Prop}
  (h : ∀ inp : t.denote, Pre inp → Post inp inp) :
    Impl t t Pre Post :=
  { code := .lam fun k => .var k, correct := h}
```

`ConsTactic` doesn't finish anything. It turns "produce a list" into "produce a pair (head, tail)",
which is a new, smaller `Impl` goal, and builds `head :: tail` from its solution:

```lean
def ConsTactic {t : Tpe} {Pre : t.denote → Prop} {Post : t.denote → List Nat → Prop}
  (impl : Impl t (.nat ⊗ .list) Pre (fun inp ⟨x, xs⟩ => Post inp (x :: xs))) :
    Impl t .list Pre Post :=
  { code := .lam fun k => .cons (.fst (.app impl.code (.var k))) (.snd (.app impl.code (.var k)))
    correct := impl.correct
  }
```

The others follow the same pattern. The ones used below are:
- `NumTactic n`, which returns a constant;
- `Vpair`, which splits a pair-valued goal into one goal per component;
- `FstTactic`/`SndTactic`, which take a component of the input;
- `CasesTactic`, which produces an `if`;
- `RelaxPostTactic`/`RelaxPreTactic`, which change the specification instead of the code.

### Example: three ways to solve `List123Problem`

**By hand.** A solution can be written directly, as a program together with its proof. Here the
proof is just `rfl`, because the program evaluates to `[1, 2, 3]` by computation (`Solutions.lean`):

```lean
def List123Solution : List123Problem := {
  code := .lam fun _ => .cons (.num 1) (.cons (.num 2) (.cons (.num 3) .nil))
  correct _ _ := rfl
}
```

**By applying combinators.** Instead of writing the program, we refine the goal. `apply ConsTactic`
asks for a head and a tail:

```
⊢ Impl unit (nat ⊗ list) (fun x => True) fun inp x =>
    match x with
    | (x, xs) => x :: xs = [1, 2, 3]
```

`Vpair` splits that pair goal into one goal per component:

```
⊢ Impl unit nat  (fun x => True) fun inp o₁ => o₁ = 1
⊢ Impl unit list (fun x => True) fun inp o₂ => o₂ = [2, 3]
```

`NumTactic 1` closes the first, leaving only the logical obligation `∀ inp, True → 1 = 1`, which
`simp` proves. The second is the same kind of problem again, one element shorter, so the same steps
repeat until `NilTactic` closes `o₂ = []`:

```lean
def List123Solution' : List123Problem := by
  apply ConsTactic
  Vpair
  · apply NumTactic 1
    simp
  · apply ConsTactic
    Vpair
    · apply NumTactic 2
      simp
    · apply ConsTactic
      Vpair
      · apply NumTactic 3
        simp
      · apply NilTactic
        simp
```

The program is assembled by the combinators and its correctness proof comes with it; nobody wrote
either down:

```
#eval List123Solution'.code.eval ()   -- [1, 2, 3]
```

**By search.** Every step above was "`apply` some combinator, then prove a small obligation", so the
derivation can be searched for. `vericode`, described below, finds it on its own:

```lean
def List123Solution'' : List123Problem := by vericode
```

## Recursion

There is no general recursion in the language; instead a list is folded with `listRec R base step`,
where `R` is a **recursor**. A recursor says how to take a value apart:
- whether it is a base case (its `depth` is `0`);
- otherwise, how to `split` it into some data plus smaller values of the same type, and how to put
  it back together (`unsplit`).

It also carries two proofs: that `unsplit` undoes `split`, and that the smaller values really are
smaller, so every `listRec` terminates. A recursor `Recursor s u d` splits a value of type `s` into
data of type `u` and `d` smaller values of type `s` (`dup s d` is the `d`-fold product of `s`):

```lean
structure Recursor (s u : Tpe) (d : Nat) where
  split : s.denote → u.denote × (dup s d).denote
  unsplit : u.denote × (dup s d).denote → s.denote
  depth : s.denote → Nat
  unsplit_split : ∀ x, depth x > 0 → unsplit (split x) = x
  descending : ∀ x, depth x > 0 → ((dup.toList (split x).2).map depth).foldl max 0 < depth x
```

`listRec` then runs like this:

```
                  listRec R base step x
                            │
            ┌─────── R.depth x = 0 ? ───────┐
            │                               │
           yes                             no
            ▼                               ▼
         base x                R.split x = (u, x₁, …, xₙ)
                                            │
                                            │  recurse on each smaller value:
                                            │    res₁ = listRec R base step x₁
                                            │      ⋮
                                            │    resₙ = listRec R base step xₙ
                                            ▼
                         step (u, (x₁, …, xₙ), (res₁, …, resₙ))
```

The recursor used most is `UnCons` (`Recursors.lean`): depth is the length of the list, `split`
takes `a :: l` to `(a, l)`, and there is one smaller value (`d = 1`):

```lean
def UnCons : Recursor .list .nat 1 := {
  split l := match l with
    | [] => ((0 : Nat), [])
    | x :: xs => (x, xs)
  unsplit y := y.1 :: y.2
  depth l := l.length
  unsplit_split l := by grind
  descending l := by grind
}
```

With it, `listRec` is ordinary head/tail recursion:

```
listRec UnCons base step [5, 6]
  = step (5, [6], listRec UnCons base step [6])
  = step (5, [6], step (6, [], listRec UnCons base step []))
  = step (5, [6], step (6, [], base []))
```
The combinator for recursion is **`ListRecTactic R`**, the induction principle. It produces
`listRec R base step` and leaves a goal for `base`, a goal for `step`, and a side condition. In the
step goal, the precondition says that the recursive results already satisfy the postcondition.

### Walking through an example

Take the problem "append `1` to the end of a list" (`Problems.lean`):

```lean
abbrev AppendConstantProblem :=
  Impl .list .list (fun _ => True) (fun inp out => out = inp.append [1])
```

Here is its derivation (`AppendConstantSolution'` in `Solutions.lean`), with the goal Lean shows
after each step.

**Recursion.** `apply ListRecTactic UnCons` leaves (among others) a base goal and a step goal:

```
case base
⊢ Impl list list (fun inp => UnCons.depth inp = 0 ∧ True) fun inp out => out = List.append inp [1]

case step
⊢ Impl (nat ⊗ list ⊗ list) list (fun x => x.2.2 = x.2.1 ++ [1])
       fun x out => out = x.1 :: (x.2.1 ++ [1])
```

The step goal is shown after `simp`. Its input is the triple `(hd, tl, res)` from the diagram, and
its precondition is the *induction hypothesis*: `res = tl ++ [1]`.

**The step case.** `pushpre` uses that equation to rewrite the postcondition, replacing
`tl ++ [1]` by `res`:

```
⊢ Impl (nat ⊗ list ⊗ list) list (fun x => x.2.2 = x.2.1 ++ [1]) fun inp out => out = inp.1 :: inp.2.2
```

Now the goal says what to build: `hd :: res`. `ConsTactic` followed by `Vpair` splits it into one
goal per component:

```
⊢ Impl (nat ⊗ list ⊗ list) nat  … fun inp o₁ => o₁ = inp.1      -- the head: take hd
⊢ Impl (nat ⊗ list ⊗ list) list … fun inp o₂ => o₂ = inp.2.2    -- the tail: take res
```

Both are closed by projecting out of the input (`FstTactic`/`SndTactic`, then `IdentityTactic`).

**The base case.** Here the input is `[]`, and the goal is `out = [] ++ [1]`. After `ConsTactic`,
`pushpre` and `simp` it becomes a pair goal:

```
⊢ Impl list (nat ⊗ list) (fun inp => inp = []) fun inp out => out.1 = 1 ∧ out.2 = []
```

`Vpair` splits it, `NumTactic 1` closes `o₁ = 1`, and `NilTactic` closes `o₂ = []`.

The finished `Impl` contains the program `listRec(λ _ => [1], λ (hd, tl, res) => hd :: res)`
(simplified by hand; the printed term has many administrative redexes), and its correctness proof
was assembled along the way:

```
#eval AppendConstantSolution'.code.eval [5, 6]   -- [5, 6, 1]
```

The full tactic script:

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

### Recursing with a parameter: `Param`

Now take "append `a` to the end of `l`", where `a` is part of the input (`Problems.lean`):

```lean
abbrev AppendProblem := Impl (.nat ⊗ .list) .list (fun _ => True) (fun ⟨a, l⟩ out => out = l.append [a])
```

The recursion should still run over the list `l`, but the input is now a pair `(a, l)`, which
`UnCons` can't split. Simply dropping `a` doesn't work either: the base case has to return `[a]`,
so every recursive call needs to know `a`. What's needed is a recursor that splits `l` as `UnCons`
does and hands the unchanged `a` along to each smaller value.

`Param` builds exactly that from any recursor. Given `R : Recursor s u d`, it gives a
`Recursor (t ⊗ s) u d` that splits the `s` part with `R` and pairs every smaller value with the same
parameter:

```
(Param UnCons).split (9, [5, 6]) = (5, (9, [6]))
```

The derivation is the AppendConstant one with this recursor: `apply ListRecTactic (Param (t := .nat)
Nat.one_pos UnCons)`. The base case now returns `[a]` by taking `a` from the input instead of the
constant `1`. `vericode` finds it too:

```lean
def AppendSolution'' : AppendProblem := by vericode
```

```
#eval AppendSolution'.code.eval (9, [5, 6])   -- [5, 6, 9]
```

Recursors are a parameter of `listRec`, rather than built in, so that other shapes of recursion
can be added the same way. `Recursors.lean` also defines `Halve`, which splits a list into *two*
halves: the shape merge sort needs, where the step receives two recursive results.

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
  `_ ⊗ .list`). It then normalizes the base and step goals and applies `pushpre` once. It refuses
  to recurse when the postcondition doesn't mention the list, or when the precondition already says
  the list is empty.
- `appList` and `introTac` let the search *invent a helper function*: apply a function to a sub-list
  of the input, then derive that function separately.

Reverse shows how these fit together. Its specification is
`Impl .list .list (fun _ => True) (fun l out => out = l.reverse)`. After one `listRecUC` the step
goal is
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

## Sorting

The specification of sorting is relational too (`InsertionSort.lean`). It doesn't say *how* to
sort, only what a sorted output is: ordered, and a permutation of the input.

```lean
def Ordered : List Nat → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => x ≤ y ∧ Ordered (y :: xs)

def Sorted (inp out : List Nat) : Prop := Ordered out ∧ (List.Perm inp out)

abbrev SortingProblem := Impl .list .list (fun _ => True) (fun inp out => Sorted inp out)
```

Insertion sort is derived in two layers:

1. **Insertion into an already sorted list.** This is a problem of its own, with a precondition:

   ```lean
   abbrev InsertProblem := Impl (.nat ⊗ .list) .list (fun inp => Ordered inp.2)
     (fun ⟨a, l⟩ out => Sorted (a :: l) out)
   ```

   `InsertionSolution` solves it with `ListRecTactic (Param UnCons)` (recurse over `l`, carrying
   `a`), and `CasesTactic` on the comparison of `a` with the head of the list:
   - if `a` is at most the head, the answer is `a :: l`;
   - otherwise, it's the head followed by the recursive result.

   Each branch picks its output with `UseTactic`, and leaves a proof obligation that this output
   satisfies `Sorted`. Those obligations are proved with lemmas about `Ordered` and `Perm`.

2. **Sorting.** `InsertionSortSolution` recurses over the input with `UnCons`. In the step, the
   recursive result `res` is a sorted permutation of the tail. So by `RelaxPostTactic` it's enough
   to produce *some* sorted version of `hd :: res`: an insertion problem. `SplitTactic` feeds
   `(hd, res)` into it, and `InsertionSolution` is reused as is:

   ```lean
   def InsertionSortSolution : SortingProblem := by
     apply ListRecTactic UnCons
     · simp
     · refine UseTactic (fun inp => []) ?_ ?_
       · apply NilTactic
         simp
       · simp [Sorted, Ordered]
     simp [dup, UnCons]
     refine RelaxPostTactic _ (fun (a, l, res) out => Sorted (a :: res) out) ?_ ?_
     · refine RelaxPreTactic (fun (a, l, res) => Ordered res) (fun _ pre => pre.1) ?_
       refine SplitTactic (.nat ⊗ .list ⊗ .list) (.nat ⊗ .list) .list (fun (a, l, res) => (a, res)) (fun (a, res) out => Sorted (a :: res) out) ?_ ?_
       · Vpair
         · apply FstTactic
           apply IdentityTactic
           simp
         · apply SndTactic
           apply SndTactic
           apply IdentityTactic
           simp
       refine RelaxPreTactic (fun (a, res) => Ordered res) ?_ ?_
       · intro (a, res) ⟨s, hs1, hs2⟩
         have : res = s.2.2 := by grind
         exact this ▸ hs1
       exact InsertionSolution
     · intro (a, l, res) pre out
       exact (SortedPerm_iff _ _ _ (List.Perm.cons _ pre.2.symm)).mp
   ```

```
#eval InsertionSolution.code.eval (4, [1, 3, 5, 7])           -- [1, 3, 4, 5, 7]
#eval InsertionSortSolution.code.eval [3, 1, 4, 1, 5, 9, 2, 6]  -- [1, 1, 2, 3, 4, 5, 6, 9]
```

Both derivations are guided: the case split, the outputs chosen with `UseTactic`, and the
reduction of sorting to insertion are all written by hand. `vericode` can't find them, because they
need a *helper with a precondition* (insertion only works into an ordered list), and the
specification lemmas about `Ordered` and `Perm` need real proofs. Two related results elsewhere in
the repository:
- `MergeSolution` in `HarderProblems.lean` reuses `InsertionSolution` the same way, to merge two
  sorted lists.
- In the parametrized language, `vericodeP [insertVal, sorted]` derives insertion sort
  automatically, but from a *functional* specification (`out = sorted l`, with `sorted` defined by
  insertion) rather than the relational `Sorted`.

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
