# Double Categorical Framework

Use double categories from mathlib. Add a thin typeclass layer on top. We can define double categories where each horizontal row is a domain language, and maps between the rows are translations between languages.

Each object is an _interface_, which is a collection of function types. Each loose/horizontal morphism between objects is a _package_, where the source object is a collection of imported function types, and the target object is a collection of exported function types. The composition of packages is another package. We have a terminal or unit object, the trivial or empty interface $*$ (empty collection of function types). A _system_ is a package from the trivial interface to some interface.

Each tight/vertical morphism from one interface to another is an _interface translation_. Intuitively, it maps the function types from one domain language to another. A _package translation_ (or just _translation_) is a map from one package to another, usually satisfying some naturality conditions. A map between systems will be called a _system translation_.

For more details, see "[Towards a double operadic theory of systems](https://arxiv.org/abs/2505.18329)".

No implementation of double categories in Lean MathLib, but there is an implementation of the weaker bicategories. Can perhaps be used as a stand-in for now.

---

## Formalization Strategy

### Background: Pseudo-Double Categories

A **pseudo-double category** consists of:
- **Objects** (e.g., interfaces)
- **Vertical/tight morphisms**: composition is strictly associative and unital
- **Horizontal/loose morphisms**: composition is associative and unital only up to coherent isomorphism
- **2-cells** (squares): with vertical composition (strict) and horizontal composition (weak)

The asymmetry arises because vertical composition lives "in Cat" (strict), while horizontal composition is "weak internal" (pseudo).

### Approach: Unfolded Definition with Bicategory Reuse

We proceed in layers:

1. **Layer 1**: Define the raw data structures
2. **Layer 2**: Add coherence conditions (reusing Mathlib's `Bicategory` where possible)
3. **Layer 3**: Specialize to the systems/packages application

---

## Layer 1: Core Data Structures

```lean
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Bicategory.Basic

universe u v w

namespace PseudoDoubleCat

/-- The raw data of a pseudo-double category, without coherence axioms. -/
structure Data where
  /-- The type of objects (e.g., interfaces) -/
  Obj : Type u

  /-- Vertical morphisms between objects (e.g., interface translations) -/
  Vert : Obj → Obj → Type v

  /-- Horizontal morphisms between objects (e.g., packages) -/
  Horiz : Obj → Obj → Type v

  /-- 2-cells: squares with vertical sides `f`, `g` and horizontal sides `h`, `k`
      ```
          h
      a ----→ b
      |       |
    f |   α   | g
      ↓       ↓
      c ----→ d
          k
      ```
  -/
  Cell : {a b c d : Obj} → Vert a c → Vert b d → Horiz a b → Horiz c d → Type w

end PseudoDoubleCat
```

---

## Layer 2: Structure with Coherence

```lean
/-- A pseudo-double category.

    Vertical composition is strict (a category).
    Horizontal composition is weak (a bicategory).
    Cells have both compositions with interchange law.
-/
class PseudoDoubleCat (Obj : Type u) extends CategoryTheory.Bicategory Obj where
  /-- Vertical morphisms (tight) -/
  Vert : Obj → Obj → Type v

  /-- Vertical identity -/
  vId : (a : Obj) → Vert a a

  /-- Vertical composition -/
  vComp : Vert a b → Vert b c → Vert a c

  /-- Vertical composition is associative (strict) -/
  vComp_assoc : vComp (vComp f g) h = vComp f (vComp g h)

  /-- Vertical identity laws (strict) -/
  vId_comp : vComp (vId a) f = f
  vComp_id : vComp f (vId b) = f

  /-- 2-cells (squares) -/
  Cell : {a b c d : Obj} → Vert a c → Vert b d → (a ⟶ b) → (c ⟶ d) → Type w

  /-- Vertical composition of cells (strict) -/
  vCellComp : Cell f g h k → Cell f' g' k m → Cell (vComp f f') (vComp g g') h m

  /-- Horizontal composition of cells (weak, up to the bicategory associator) -/
  hCellComp : Cell f g h k → Cell g i k' m' → Cell f i (h ≫ k') (k ≫ m')

  /-- Identity cells -/
  cellId : (f : Vert a b) → Cell f f (𝟙 a) (𝟙 b)
  cellHId : (h : a ⟶ b) → Cell (vId a) (vId b) h h

  /-- Interchange law: vertical then horizontal = horizontal then vertical -/
  interchange :
    vCellComp (hCellComp α β) (hCellComp α' β') =
    hCellComp (vCellComp α α') (vCellComp β β')
```

**Note**: The `extends CategoryTheory.Bicategory Obj` clause reuses Mathlib's bicategory structure for horizontal morphisms, giving us:
- `Hom a b` = horizontal morphisms (we can set `Horiz := Hom`)
- `associator`, `leftUnitor`, `rightUnitor` as isomorphisms
- Pentagon and triangle coherence axioms

---

## Layer 3: Alternative - Standalone Definition (No Bicategory Dependency)

If you want full control without depending on `Bicategory`:

```lean
/-- Coherent isomorphism data for horizontal composition -/
structure HorizCoherence (Obj : Type u) (Horiz : Obj → Obj → Type v) where
  /-- Horizontal identity -/
  hId : (a : Obj) → Horiz a a

  /-- Horizontal composition -/
  hComp : Horiz a b → Horiz b c → Horiz a c

  /-- 2-morphisms between horizontal morphisms (for coherence cells) -/
  Horiz₂ : Horiz a b → Horiz a b → Type w

  /-- Associator: (f ≫ g) ≫ h ≅ f ≫ (g ≫ h) -/
  associator : (f : Horiz a b) → (g : Horiz b c) → (h : Horiz c d) →
    Horiz₂ (hComp (hComp f g) h) (hComp f (hComp g h))

  associator_inv : (f : Horiz a b) → (g : Horiz b c) → (h : Horiz c d) →
    Horiz₂ (hComp f (hComp g h)) (hComp (hComp f g) h)

  /-- Left unitor: id ≫ f ≅ f -/
  leftUnitor : (f : Horiz a b) → Horiz₂ (hComp (hId a) f) f
  leftUnitor_inv : (f : Horiz a b) → Horiz₂ f (hComp (hId a) f)

  /-- Right unitor: f ≫ id ≅ f -/
  rightUnitor : (f : Horiz a b) → Horiz₂ (hComp f (hId b)) f
  rightUnitor_inv : (f : Horiz a b) → Horiz₂ f (hComp f (hId b))

  /-- Pentagon coherence -/
  pentagon : ... -- (f ≫ g) ≫ (h ≫ k) path equality

  /-- Triangle coherence -/
  triangle : ... -- (f ≫ id) ≫ g vs f ≫ g path equality
```

---

## Application: Systems and Packages

Specializing to the intended application:

```lean
/-- An interface is a collection of function types in some domain -/
structure Interface where
  funTypes : List Type  -- or more sophisticated representation

/-- A package from interface I to interface J -/
structure Package (I J : Interface) where
  /-- Implementation mapping imports to exports -/
  impl : (I.funTypes → Type) → (J.funTypes → Type)
  -- additional structure: correctness conditions, etc.

/-- Translation between interfaces (vertical morphism) -/
structure InterfaceTranslation (I J : Interface) where
  translate : I.funTypes → J.funTypes
  -- preservation properties

/-- Translation between packages (2-cell) -/
structure PackageTranslation
    {I I' J J' : Interface}
    (τ : InterfaceTranslation I I')
    (σ : InterfaceTranslation J J')
    (P : Package I J)
    (Q : Package I' J') where
  transform : ... -- naturality square

/-- The pseudo-double category of systems -/
instance : PseudoDoubleCat Interface where
  Vert := InterfaceTranslation
  -- Horiz comes from Bicategory instance
  Cell := PackageTranslation
  ...
```

---

## Implementation Roadmap

1. ✅ **Start minimal**: Define `PseudoDoubleCat.Data` without axioms
2. ✅ **Add vertical category structure**: `VertCat` class with strict composition
3. ✅ **Choose horizontal approach**: Option B (inline coherence) for now
   - `HorizBicat` class with `Horiz₂` for coherence 2-cells
   - Associator and unitors as data (axioms deferred to Layer 2)
4. ✅ **Define cells and their compositions**: `CellStruct` class
5. ✅ **Interchange law**: `Interchange` class (Layer 2)
6. ✅ **Vertical cell coherence**: `VCellUnitLaws`, `VCellAssoc` (Layer 2)
7. **TODO**: Instantiate for `Interface`/`Package`

### Implemented in `DeductiveVericoding/DoubleCat.lean`

**Layer 1: Data Structures**
```
PseudoDoubleCat.Data              -- raw bundled data
PseudoDoubleCat.VertCat           -- strict vertical category
PseudoDoubleCat.HorizBicat        -- weak horizontal bicategory (coherence data)
PseudoDoubleCat.CellStruct        -- 2-cell operations
PseudoDoubleCat.PrePseudoDoubleCat -- combined Layer 1 structure
```

**Layer 2: Coherence Axioms**
```
PseudoDoubleCat.Interchange       -- (α ⬝ᶜᵥ γ) ⬝ᶜₕ (β ⬝ᶜᵥ δ) = (α ⬝ᶜₕ β) ⬝ᶜᵥ (γ ⬝ᶜₕ δ)
PseudoDoubleCat.VCellUnitLaws     -- cellHId is unit for vertical cell composition
PseudoDoubleCat.VCellAssoc        -- vertical cell composition is associative
PseudoDoubleCat.IsPseudoDouble    -- full pseudo-double category
```

Trivial example instance on `Unit` provided as sanity check.

---

## Related Work

- **UniMath** (Coq): Has univalent double categories, code at [github.com/UniMath](https://github.com/UniMath/UniMath)
- **Mathlib Bicategory**: `Mathlib.CategoryTheory.Bicategory.Basic` provides the weak composition infrastructure
- **LeanFibredCategories**: Fibred category approach, potentially useful for displayed-style formulation

---

## Open Questions

1. **Strictification**: Should we work with strict double categories when possible? Every pseudo-double category is equivalent to a strict one.

2. **Universe levels**: The nested types (`Cell` depending on `Vert`, `Horiz`, `Obj`) require careful universe management.

3. **Companion/conjoint pairs**: For applications, we may need the theory of companions (vertical morphisms with horizontal adjoints).

4. **Monoidal structure**: The systems application likely needs monoidal double categories (tensor of interfaces/packages).