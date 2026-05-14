# Pseudo-Double Category Implementation

## Overview

The pseudo-double category framework is fully implemented in `DoubleCat.lean` (abstract structure) and `DoubleCodable.lean` (specification instance).

## References

- [nLab: double category](https://ncatlab.org/nlab/show/double+category)
- [nLab: pseudo double category](https://ncatlab.org/nlab/show/pseudo+double+category)
- Grandis & Paré, "Limits in double categories", *Cahiers de Topologie*, 1999

## Implementation Status

### DoubleCat.lean - Complete

| Component | Status |
|-----------|--------|
| `VertCat` - strict vertical category | ✅ |
| `HorizBicat` - 2-morphisms, whiskering, coherence (10+6+6 axioms) | ✅ |
| `HorizBicatCoherence` - pentagon and triangle | ✅ |
| `CellStruct` - operations, coherence cells, inverse laws | ✅ |
| `Interchange`, `VCellUnitLaws`, `VCellAssoc` | ✅ |
| `HCellUnitLaws`, `HCellAssoc` (naturality formulation) | ✅ |
| `IsDouble` - full pseudo-double category | ✅ |
| `Unit` example instance | ✅ |

### DoubleCodable.lean - Complete

| Component | Status |
|-----------|--------|
| `VertCat SpecObj` - functions as vertical morphisms | ✅ |
| `HorizBicat SpecObj` - specs, refinements, whiskering | ✅ |
| `CellStruct SpecObj` - SpecCell with all coherence | ✅ |
| `PreDoubleCat SpecObj` | ✅ |

## Future Work

1. **Compatibility between cell coherence and Horiz₂**: Investigate the relationship between `cellHAssoc` (a cell) and `hAssoc` (a 2-morphism).

## Technical Notes

### Use of HEq

Coherence axioms use `HEq` because vertical boundaries differ by `vId_comp` vs `vComp_id` (propositionally but not definitionally equal).

### SpecRefine Composition

`post_stronger` uses `s1.pre` (not `s2.pre`) to enable composition:
```
post_stronger : ∀ a b, s1.pre a → s2.post a b → s1.post a b
```

## Architecture

```
namespace DoubleCat
  class VertCat            -- Strict vertical category
  class HorizBicat         -- Bicategory structure with whiskering
  class HorizBicatCoherence -- Pentagon and triangle
  class CellStruct         -- 2-cells with coherence
  class PreDoubleCat       -- Combined Layer 1
  class Interchange        -- Interchange law
  class VCellUnitLaws      -- Vertical cell units
  class VCellAssoc         -- Vertical cell associativity
  class HCellUnitLaws      -- Horizontal cell units (naturality)
  class HCellAssoc         -- Horizontal cell associativity (naturality)
  class IsDouble           -- Full pseudo-double category
end DoubleCat
```
