# System Architecture For Double Operadic AtomWorld

## Overview
* BAIF wants to build an "AtomWorld" where each atom is an implementation function/class or a spec definition/theorem/lemma.
* [Pi Squared](https://pi2.network/) is a startup that is also trying to build a kind of AtomWorld on top of blockchain, with diverse kinds of verifiers and certs.

## Some characteristics of AtomWorld
* Each atom is an "interface" or "open system" or "partial evaluation" (see DOTS)
* Functions/classes, specs/theorems and proofs are examples of interfaces
* Each interface can be verified in many ways, either by a human (e.g. for a spec) or an algorithm (e.g. for a proof)
* The proofs can be stored cryptographically to prevent tampering without permission. But it need NOT be blockchain.
* Arrows in AtomWorld are of two kinds: refinements/interactions and translations/transforms/projections.
* Arrows are themselves atoms of AtomWorld, so we can have arrows between arrows.
* The refinements/interactions are explicit dependencies between the atoms. An interaction is the composition of atoms/interfaces. A refinement is a decomposition of an atom/interface into smaller atoms/interfaces. There is an inverse relationship between them - in fact, if refinements and interactions are functors, then the relationship might be some kind of adjunction.
* The translations/transforms/projections of an atom are the different views of an atom - e.g. as a boolean function or as a Prop (small scale refection), as a nat language intent or as a formal spec, as a Lean proof or as an Isabelle proof.
* If we have a selection of atoms and arrows for viewing, this selection can be called a View of AtomWorld which can be represented also as an (meta-)atom in AtomWorld. You can write (meta-)transforms for changing between views.
* There is version control of the atoms and arrows.

## Relationship to Git
* In Git, the blobs are atoms. The deltas are arrows.
* But we can't represent anything smaller than a file as an atom. This makes syncing betwen AtomWorld and FileWorld tricky but not impossible
