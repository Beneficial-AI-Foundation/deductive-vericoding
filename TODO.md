# TODO: Pseudo-Double Category Definition Fixes

## Overview

The current pseudo-double category implementation in `DeductiveVericoding/DoubleCat.lean` is **weaker** than the standard definition from Grandis-Paré and the nLab. This document tracks the missing components that should be added for a complete formalization.

## References

- [nLab: double category](https://ncatlab.org/nlab/show/double+category)
- [nLab: double bicategory](https://ncatlab.org/nlab/show/double+bicategory)
- Grandis & Paré, "Limits in double categories", *Cahiers de Topologie*, 1999
- Grandis & Paré, "Composition of Modules for Lax Functors", *Theory and Applications of Categories*, Vol. 27, 2013

## Missing Components

### 1. Bicategory Coherence for `HorizBicat` (High Priority)

**File:** `DoubleCat.lean`, lines 77-105

The `HorizBicat` class provides associators and unitors as data but doesn't require them to satisfy the bicategory coherence axioms.

**Missing: Pentagon Identity**
```lean
-- For all h : Horiz a b, k : Horiz b c, m : Horiz c d, n : Horiz d e:
-- The following diagram commutes:
--
--   ((h ⬝ k) ⬝ m) ⬝ n  --hAssoc-->  (h ⬝ k) ⬝ (m ⬝ n)  --hAssoc-->  h ⬝ (k ⬝ (m ⬝ n))
--          |                                                              ^
--    hAssoc⊗id                                                            |
--          v                                                         id⊗hAssoc
--   (h ⬝ (k ⬝ m)) ⬝ n  ----------------hAssoc---------------------->  h ⬝ ((k ⬝ m) ⬝ n)

class HorizBicatCoherence (Obj : Type u) [HorizBicat.{u,v,w} Obj] : Prop where
  pentagon : ∀ {a b c d e : Obj}
    (h : Horiz a b) (k : Horiz b c) (m : Horiz c d) (n : Horiz d e),
    -- Composition of hAssoc forms commuting pentagon
    sorry
```

**Missing: Triangle Identity**
```lean
-- For all h : Horiz a b, k : Horiz b c:
--
--   (h ⬝ id) ⬝ k  --hAssoc-->  h ⬝ (id ⬝ k)
--         |                         |
--   hRightUnitor⊗id            id⊗hLeftUnitor
--         v                         v
--       h ⬝ k  ========  h ⬝ k

  triangle : ∀ {a b c : Obj} (h : Horiz a b) (k : Horiz b c),
    -- Triangle commutes
    sorry
```

### 2. `Horiz₂` Category Structure (Medium Priority)

**File:** `DoubleCat.lean`, `HorizBicat` class

The 2-morphisms `Horiz₂` between horizontal morphisms should form a category.

**Missing fields in `HorizBicat`:**
```lean
  /-- Identity 2-morphism -/
  h2Id : {a b : Obj} → (h : Horiz a b) → Horiz₂ h h

  /-- Composition of 2-morphisms -/
  h2Comp : {a b : Obj} → {h k m : Horiz a b} →
    Horiz₂ h k → Horiz₂ k m → Horiz₂ h m

  /-- 2-morphism composition is associative -/
  h2Comp_assoc : ∀ {a b : Obj} {h k m n : Horiz a b}
    (α : Horiz₂ h k) (β : Horiz₂ k m) (γ : Horiz₂ m n),
    h2Comp (h2Comp α β) γ = h2Comp α (h2Comp β γ)

  /-- Left identity for 2-morphism composition -/
  h2Id_comp : ∀ {a b : Obj} {h k : Horiz a b} (α : Horiz₂ h k),
    h2Comp (h2Id h) α = α

  /-- Right identity for 2-morphism composition -/
  h2Comp_id : ∀ {a b : Obj} {h k : Horiz a b} (α : Horiz₂ h k),
    h2Comp α (h2Id k) = α
```

### 3. Horizontal Whiskering (Medium Priority)

**File:** `DoubleCat.lean`, `HorizBicat` class

Bicategories require horizontal composition of 2-morphisms with 1-morphisms (whiskering).

**Missing:**
```lean
  /-- Left whiskering: h ⊗ α for α : k → m gives h ⬝ k → h ⬝ m -/
  hWhiskerLeft : {a b c : Obj} → (h : Horiz a b) → {k m : Horiz b c} →
    Horiz₂ k m → Horiz₂ (hComp h k) (hComp h m)

  /-- Right whiskering: α ⊗ k for α : h → m gives h ⬝ k → m ⬝ k -/
  hWhiskerRight : {a b c : Obj} → {h m : Horiz a b} →
    Horiz₂ h m → (k : Horiz b c) → Horiz₂ (hComp h k) (hComp m k)
```

### 4. Horizontal Cell Composition Coherence (Medium Priority)

**File:** `DoubleCat.lean`, `CellStruct` class

The standard definition requires that `hCellComp` is coherent with the horizontal bicategory structure.

**Missing coherence cells:**
```lean
  /-- Associator cell: witnesses hCellComp associativity -/
  cellHAssoc : {a b c d : Obj} →
    (h : Horiz a b) → (k : Horiz b c) → (m : Horiz c d) →
    Cell (vId a) (vId d) (hComp (hComp h k) m) (hComp h (hComp k m))

  /-- Left unitor cell -/
  cellHLeftUnitor : {a b : Obj} → (h : Horiz a b) →
    Cell (vId a) (vId b) (hComp (hId a) h) h

  /-- Right unitor cell -/
  cellHRightUnitor : {a b : Obj} → (h : Horiz a b) →
    Cell (vId a) (vId b) (hComp h (hId b)) h
```

### 5. Horizontal Cell Unit and Associativity Laws (Low Priority)

**File:** `DoubleCat.lean`

Add coherence classes for horizontal cell composition analogous to the vertical ones.

```lean
/-- Unit laws for horizontal cell composition -/
class HCellUnitLaws (Obj : Type u) [VertCat Obj] [HorizBicat Obj] [CellStruct Obj] : Prop where
  hCellComp_cellVId_left : ∀ ... (α : Cell f g h k),
    HEq (hCellComp (cellVId f) α) α  -- up to coherence
  hCellComp_cellVId_right : ∀ ... (α : Cell f g h k),
    HEq (hCellComp α (cellVId g)) α  -- up to coherence

/-- Associativity for horizontal cell composition -/
class HCellAssoc (Obj : Type u) [VertCat Obj] [HorizBicat Obj] [CellStruct Obj] : Prop where
  hCellComp_assoc : ∀ ... (α β γ : Cell ...),
    HEq (hCellComp (hCellComp α β) γ) (hCellComp α (hCellComp β γ))
```

## Current Status

### What Works

- ✅ Vertical category structure is correct and strict
- ✅ Horizontal morphisms have associators and unitors (as data)
- ✅ Cell structure with vertical and horizontal composition
- ✅ Interchange law
- ✅ Vertical cell unit laws and associativity
- ✅ `SpecCell` composition in `DoubleCodable.lean` (all proofs complete, no sorries)

### What's Missing

- ❌ Pentagon and triangle identities for `HorizBicat`
- ❌ `Horiz₂` category structure (composition, identities)
- ❌ Whiskering operations
- ❌ Horizontal cell coherence cells
- ❌ Horizontal cell unit/associativity laws

## Notes

1. **For the Libkind-Myers application**: The current weaker definition is likely sufficient because:
   - The main operations (operadic composition via `hCellComp`) work correctly
   - Interchange law holds
   - Vertical refinement is strict

2. **For a complete formalization**: All missing components should be added to claim we have a proper pseudo-double category in the sense of Grandis-Paré.

3. **The `SpecCell` structure** in `DoubleCodable.lean` has four fields (`pre_backward`, `pre_forward`, `post_transfer`, `post_surj`) that are application-specific and don't affect the abstract structure. These are correctly composed in all cases (vCellComp, hCellComp, cellVId, cellHId).

## Implementation Order

Suggested order for fixing:

1. **First**: Add `Horiz₂` category structure (identity, composition, laws)
2. **Second**: Add whiskering operations
3. **Third**: Add pentagon and triangle identities
4. **Fourth**: Add horizontal cell coherence cells
5. **Fifth**: Add horizontal cell unit/associativity laws

Each step should include updating the `Unit` example instance to verify the definitions are satisfiable.
