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
