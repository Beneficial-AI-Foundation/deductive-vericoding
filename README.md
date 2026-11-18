# Deductive Vericoding
Tactics-driven vericoding

## What is Deductive Vericoding?

Vericoding (verified coding) uses formal methods to generate provably correct code. There are two approaches:

**Inductive Vericoding** learns from examples. Given input-output pairs or spec-code examples, a model generalizes these patterns to synthesize code for new specs. If verification fails, generation is retried until it succeeds.

**Deductive Vericoding** reasons from first principles. Starting with a formal spec, it decomposes the problem into smaller sub-specs, solves each one (via generation or further decomposition), and composes the verified solutions into a correct implementation.

## Project Overview

A talk I gave in May 2025 about double operadic theory of systems (DOTS) view of refinement-based tactics-driven vericoding (verified coding).
* https://shaoweilin.github.io/posts/2025-05-30-refine-yourself-a-code-for-great-good/

Towards a double operadic theory of systems (2025) - Sophie Libkind, David Jaz Myers
* https://arxiv.org/abs/2505.18329

## Building

The project uses Lean `v4.24.0` (see `lean-toolchain`), Mathlib and Loom. With
[elan](https://github.com/leanprover/elan) installed:

```
lake exe cache get   # download prebuilt Mathlib
lake build
```

## Repository layout

- `DeductiveVericoding/ListLanguage/`: a small typed list language with combinators and the
  `vericode` search (the main development, described below).
- `DeductiveVericoding/ListLanguage/Parametrized/`: a de Bruijn variant with a verified
  translation back into the list language.
- `DeductiveVericoding/Function/`: an earlier string/nat language with `Codable` combinators.
- `DeductiveVericoding/CategoryTheory/`: pseudo-double categories, with specifications and
  refinements as an instance.
- `doc/`: design notes.

## The list language and `vericode`

A problem is a type `Impl I O Pre Post`, and a solution is a program together with its proof of
`Pre inp → Post inp (program inp)`. Combinators are proved refinement steps that reduce one such
goal to smaller ones. `vericode` searches over them, so many problems are solved in one line:

```lean
abbrev ReverseProblem := Impl .list .list (fun _ => True) (fun l out => out = l.reverse)

def ReverseSolution'' : ReverseProblem := by vericode
```

For specifications that don't name their output, `vericode` takes facts about the specification and
finds the program itself, including the case split it needs:

```lean
def FilterSpec : Nat × List Nat → List Nat → Prop := fun (a, l) out =>
  out.Sublist l ∧ (∀ x ∈ out, x ≤ a) ∧ (∀ x ∈ l, x ≤ a → x ∈ out)

def FilterSolution : FilterProblem := by
  vericode [FilterSpec_nil, FilterSpec_keep, FilterSpec_drop]
```

Suggested reading order: `ListLanguage/Problems.lean` → `Solutions.lean` → `HarderProblems.lean`.
The write-up is [`doc/014-list-language.md`](doc/014-list-language.md).
