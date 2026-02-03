# How `insertionSort` Becomes a Triple

## 1. The Triple Definition

The fundamental `triple` is defined in `Loom/MonadAlgebras/WP/Basic.lean:21-22`:

```lean
def triple (pre : l) (c : m α) (post : α -> l) : Prop :=
  pre ≤ wp c post
```

A triple states that if the precondition `pre` holds, executing computation `c` will satisfy postcondition `post`. This is defined in terms of weakest preconditions (`wp`).

## 2. The Method Macro Transformation

When you write:

```lean
method insertionSort
  (mut arr: Array Int) return (u: Unit)
  require 1 ≤ arr.size
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.size → arr[i]! ≤ arr[j]!
  ensures arr.toMultiset = arrOld.toMultiset
  do ...
```

The `method` macro in `CaseStudies/Velvet/Syntax.lean:248-316` does two things:

### A) Creates a Lean function definition:

```lean
def insertionSort (arrOld : Array Int) : VelvetM (Unit × Array Int) := do
  let mut arr := arrOld
  -- ... body with loops/invariants elaborated
```

Note: Mutable parameters get an `Old` suffix (e.g., `arr` → `arrOld`), and the return type becomes a tuple `(Unit × Array Int)` to capture both the return value and final mutable state.

### B) Stores a `VelvetObligation`

Defined in `CaseStudies/Extension.lean:27-35`:

```lean
structure VelvetObligation where
  binderIdents : TSyntaxArray `Lean.Parser.Term.bracketedBinder  -- (arrOld : Array Int)
  modIds : Array Ident                                           -- [arr]
  ids : Array Ident                                              -- [arrOld]
  retId : Ident                                                  -- u
  ret : Term                                                     -- (u, arr)
  pre : Term                                                     -- 1 ≤ arr.size
  post : Term                                                    -- the ensures clauses
```

## 3. The Triple Generation (`prove_correct`)

When you write:

```lean
prove_correct insertionSort by
  loom_solve
```

The `prove_correct` command (`Syntax.lean:328-367`) retrieves the stored obligation and generates a theorem:

```lean
@[loomSpec]
lemma insertionSort_correct (arrOld : Array Int) :
  triple
    (let arr := arrOld; with_name_prefix `require (1 ≤ arr.size))  -- precondition
    (insertionSort arrOld)                                          -- computation
    (fun (u, arr) =>                                                -- postcondition
      with_name_prefix `ensures (∀ i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.size → arr[i]! ≤ arr[j]!) ∧
      with_name_prefix `ensures (arr.toMultiset = arrOld.toMultiset)) := by
  unfold insertionSort
  loom_solve
```

## 4. Key Transformations

| Velvet Syntax | Triple Component |
|---------------|------------------|
| `(mut arr: Array Int)` | Binder `(arrOld : Array Int)`, return includes `arr` |
| `require P` | Precondition: `let arr := arrOld; P` |
| `ensures Q` | Postcondition: `fun (ret, arr) => Q` |
| Method body | The `VelvetM` computation `c` |
| `arrOld` in ensures | References initial value of mutable `arr` |

## 5. Semantics Context

The interpretation depends on the semantic options:

- `set_option loom.semantics.termination "partial"` → Uses `PartialCorrectness` (divergence allowed)
- `set_option loom.semantics.choice "demonic"` → Uses `DemonicChoice` (all non-deterministic choices must satisfy postcondition)

## 6. The Full Picture

```
┌─────────────────────────────────────────────────────────────────┐
│  method insertionSort (mut arr: Array Int) return (u: Unit)     │
│    require 1 ≤ arr.size                                         │
│    ensures ∀ i j, ... → arr[i]! ≤ arr[j]!                       │
│    ensures arr.toMultiset = arrOld.toMultiset                   │
│    do ...                                                       │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│  1. def insertionSort (arrOld : Array Int) : VelvetM (Unit ×    │
│       Array Int)                                                │
│                                                                 │
│  2. VelvetObligation stored with pre, post, binders, etc.       │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│  prove_correct insertionSort by loom_solve                      │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│  lemma insertionSort_correct (arrOld : Array Int) :             │
│    triple                                                       │
│      (let arr := arrOld; 1 ≤ arr.size)                          │
│      (insertionSort arrOld)                                     │
│      (fun (u, arr) => ∀ i j, ... ∧ arr.toMultiset = ...)        │
└─────────────────────────────────────────────────────────────────┘
```

The triple connects the Hoare logic specification (`{P} c {Q}`) to weakest precondition semantics (`pre ≤ wp c post`), enabling automated verification via the `loom_solve` tactic.

## 7. The Triple Bind

This is how the triple bind theorem, informally `{P}c{Q} -> {Q}d{R} -> {Q}c;d{R}`, is represented in Loom:

```lean
lemma triple_bind {β} (pre : l) (x : m α) (cut : α -> l)
  (f : α -> m β) (post : β -> l) :
  triple pre x cut ->
  (∀ y, triple (cut y) (f y) post) ->
  triple pre (x >>= f) post := by
    intros; simp [triple, wp_bind]
    solve_by_elim [le_trans', wp_cons]
```

See also `DeductiveVericoding/Triples.lean`.

See `DeductiveVericoding/Reified.lean` for an example where the derived program can be printed.