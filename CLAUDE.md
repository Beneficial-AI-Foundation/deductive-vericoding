# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

A Lean 4 library for **deductive vericoding**: deriving verified programs by refining a
specification step by step with *combinators* (each one a small, proved refinement rule), either by
hand or by an automated search (`vericode`). The main development is a small typed list language
in `DeductiveVericoding/ListLanguage/`.

## Build System & Commands

- **Build everything**: `lake build` (the `lakefile.toml` globs list every module explicitly,
  so this compiles all of `CategoryTheory/`, `Function/` and `ListLanguage/`).
- **Build one module**: `lake build DeductiveVericoding.ListLanguage.Solutions`
- **Check a scratch file against the project**: `lake env lean path/to/File.lean`

Toolchain: Lean `v4.24.0` (`lean-toolchain`). Dependencies (`lakefile.toml`): Mathlib `v4.24.0`
and Loom (`verse-lab/loom`, used by `Function/FunctionLoom.lean`).

## Layout

- `CategoryTheory/` — `DoubleCat.lean` (pseudo-double categories), `DoubleCodable.lean`
  (specifications and refinements as a double category instance).
- `Function/` — `Function.lean`, `FunctionLoom.lean`: an earlier string/nat language with
  `Codable` combinators and a simple `vericode` macro; `doc/011-function.md`.
- `ListLanguage/` — the main development:
  - `Basic.lean`: types `Tpe`, PHOAS terms `Trm'`, `Recursor` + `Recursor.fold`, and
    `Impl I O Pre Post` (code together with its correctness proof).
  - `Recursors.lean`: `UnCons`, `Param`, `Halve`.
  - `Tactics.lean`: the combinators (`NilTactic`, `ConsTactic`, `PairTactic`/`Vpair`,
    `ListRecTactic`, `CasesTactic`, `RelaxPreTactic`, `RelaxPostTactic`, `UseTactic`, …).
  - `VericodeTactic.lean`: the `vericode` search (aesop rule set `VericodeL`), its front-ends
    (`projClose`, `numClose`, `listRecUC`, `appList`, `introTac`, `natCases`, `pushpre`) and
    `relaxPost`.
  - `Problems.lean` / `Solutions.lean`: specifications and their solutions.
  - `InsertionSort.lean`: sorting specs and a guided insertion-sort derivation.
  - `HarderProblems.lean`: relational specifications solved by `vericode [lemmas]`, plus the
    documented frontier of what is out of reach.
  - `Parametrized/`: a de Bruijn variant (`ImplP`, `vericodeP`) with a verified translation back
    into the list language (`Translation.lean`: `toList'`, `toImpl`, `toList'_eval`).
- `doc/` — design notes; `doc/014-list-language.md` describes the list-language work.

## Conventions

- In `Solutions.lean`: `XXXSolution` is a hand-written term + proof, `XXXSolution'` is derived by
  applying combinators by hand, `XXXSolution''` is found by `vericode`.
- `vericode [l₁, …]` takes facts about the *specification*; it uses them via `relaxPost`
  (rewrite or implication) and as simp lemmas.
- A solution produced by search must be checked with `#print axioms`: aesop can fill unsolved
  metavariables with `sorry`, which shows up as `sorryAx`.
- The project is currently `sorry`-free; keep it that way, or mark any new `sorry` clearly.
