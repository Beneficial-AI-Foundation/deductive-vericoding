# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Lean 4 mathematics library focused on "tactics-driven vericoding" - using proof-assistants and tactics to construct verified computational modules. The project explores formal verification of arithmetic algorithms using mixed radix numbers (MRNs) and Fiat-style computational refinement.

## Build System & Commands

This project uses Lake (Lean's build system):

- **Build the project**: `lake build`
- **Build a specific target**: `lake build Modularity`
- **Run Lean server**: `lean --server` (for IDE integration)
- **Check a specific file**: `lean Modularity/Demo.lean`

The project requires Lean 4 version `v4.21.0` (specified in `lean-toolchain`).

## Dependencies

- **Mathlib**: Core mathematics library for Lean 4 (`v4.21.0`)
- **Canonical**: Additional utility library (`v4.21.0`)

Dependencies are managed through Lake and specified in `lakefile.toml`.

## Architecture

### Core Modules

1. **Modularity/Basic.lean**: Foundational theorems and induction proofs
   - Contains `sum_spec` proof using mathematical induction
   - Demonstrates basic proof techniques and recursion patterns

2. **Modularity/Core.lean**: Fiat computational framework
   - Implements monadic computational model using `Set A` for nondeterminism
   - Defines `Return`, `Bind`, `Pick` operations for specification refinement
   - Contains refinement relations and proof tactics for program derivation

3. **Modularity/Demo.lean**: Associational arithmetic implementation
   - Mixed radix number representation as `List (Int × Int)` 
   - Polynomial evaluation via `eval` function
   - Arithmetic operations (`mul`, `split`, `reduce`) with correctness proofs
   - Demonstrates tactics-driven program synthesis for modular arithmetic

4. **Modularity/Ensembles.lean**: Set theory foundations
   - Naive set theory implementation using predicates (`U → Prop`)
   - Basic set operations (union, intersection, complement)
   - Extensionality axiom and set equality definitions

### Key Concepts

- **Mixed Radix Numbers (MRNs)**: Represented as `List (Int × Int)` where each pair `(coeff, base)` contributes `coeff * base` to the total value
- **Refinement**: Using lemmas like `eval_mul` and `eval_app` to transform high-level specifications into executable implementations
- **Tactics-driven synthesis**: Using `rw`, `grind`, and other tactics to automatically derive arithmetic circuits

## Development Patterns

- Proofs use structured tactics (`induction`, `cases`, `simp`, `ring`)
- Computational definitions are accompanied by correctness lemmas (e.g., `eval_mul`, `eval_app`)
- Some proofs contain `sorry` placeholders indicating incomplete verification
- Heavy use of Mathlib tactics for algebraic manipulation

## File Structure

- Root module: `Modularity.lean` (imports `Modularity.Basic`)
- Source files: `Modularity/` directory
- Documentation: `doc/` directory with explanatory markdown files
- Build configuration: `lakefile.toml`, `lean-toolchain`