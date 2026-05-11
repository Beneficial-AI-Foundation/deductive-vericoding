/-
  Pseudo-Double Categories - Layer 1: Core Data Structures

  A pseudo-double category has:
  - Objects
  - Vertical morphisms (tight): strictly associative composition
  - Horizontal morphisms (loose): weakly associative composition
  - 2-cells (squares): with both vertical and horizontal composition

  This file defines the raw data structures without full coherence axioms.
-/

import Mathlib.CategoryTheory.Category.Basic

universe u v w

namespace PseudoDoubleCat

/-! ## Layer 1: Raw Data Structures -/

/-- The raw data of a pseudo-double category, bundled into a structure.

    A 2-cell (square) looks like:
    ```
          h
      a ----→ b
      |       |
    f |   α   | g
      ↓       ↓
      c ----→ d
          k
    ```
    where `f`, `g` are vertical morphisms and `h`, `k` are horizontal morphisms.
-/
structure Data where
  /-- The type of objects -/
  Obj : Type u
  /-- Vertical morphisms from `a` to `b` -/
  Vert : Obj → Obj → Type v
  /-- Horizontal morphisms from `a` to `b` -/
  Horiz : Obj → Obj → Type v
  /-- 2-cells with boundary (f, g, h, k) where f, g are vertical and h, k horizontal -/
  Cell : {a b c d : Obj} → Vert a c → Vert b d → Horiz a b → Horiz c d → Type w

/-! ## Vertical Category Structure (Strict) -/

/-- Vertical category structure with strict composition -/
class VertCat (Obj : Type u) where
  /-- Vertical morphisms -/
  Vert : Obj → Obj → Type v
  /-- Vertical identity -/
  vId : (a : Obj) → Vert a a
  /-- Vertical composition: f then g -/
  vComp : {a b c : Obj} → Vert a b → Vert b c → Vert a c
  /-- Vertical composition is associative -/
  vComp_assoc : ∀ {a b c d : Obj} (f : Vert a b) (g : Vert b c) (h : Vert c d),
    vComp (vComp f g) h = vComp f (vComp g h)
  /-- Left identity law -/
  vId_comp : ∀ {a b : Obj} (f : Vert a b), vComp (vId a) f = f
  /-- Right identity law -/
  vComp_id : ∀ {a b : Obj} (f : Vert a b), vComp f (vId b) = f

namespace VertCat

variable {Obj : Type u} [VertCat.{u, v} Obj]

/-- Notation for vertical identity -/
scoped notation "𝟙ᵥ" => vId

/-- Notation for vertical composition -/
scoped infixr:80 " ⬝ᵥ " => vComp

end VertCat

/-! ## Horizontal Bicategory Structure (Weak) -/

/-- Horizontal bicategory structure with weak composition.

    For now we include the coherence isomorphisms as data,
    but omit pentagon/triangle axioms (to be added in Layer 2).
-/
class HorizBicat (Obj : Type u) where
  /-- Horizontal morphisms -/
  Horiz : Obj → Obj → Type v
  /-- Horizontal identity morphism -/
  hId : (a : Obj) → Horiz a a
  /-- Horizontal composition: h then k -/
  hComp : {a b c : Obj} → Horiz a b → Horiz b c → Horiz a c
  /-- 2-morphisms between horizontal morphisms (for coherence cells) -/
  Horiz₂ : {a b : Obj} → Horiz a b → Horiz a b → Type w
  /-- Associator: (h ⬝ k) ⬝ m ≅ h ⬝ (k ⬝ m) -/
  hAssoc : {a b c d : Obj} → (h : Horiz a b) → (k : Horiz b c) → (m : Horiz c d) →
    Horiz₂ (hComp (hComp h k) m) (hComp h (hComp k m))
  /-- Inverse associator -/
  hAssoc_inv : {a b c d : Obj} → (h : Horiz a b) → (k : Horiz b c) → (m : Horiz c d) →
    Horiz₂ (hComp h (hComp k m)) (hComp (hComp h k) m)
  /-- Left unitor: id ⬝ h ≅ h -/
  hLeftUnitor : {a b : Obj} → (h : Horiz a b) → Horiz₂ (hComp (hId a) h) h
  /-- Inverse left unitor -/
  hLeftUnitor_inv : {a b : Obj} → (h : Horiz a b) → Horiz₂ h (hComp (hId a) h)
  /-- Right unitor: h ⬝ id ≅ h -/
  hRightUnitor : {a b : Obj} → (h : Horiz a b) → Horiz₂ (hComp h (hId b)) h
  /-- Inverse right unitor -/
  hRightUnitor_inv : {a b : Obj} → (h : Horiz a b) → Horiz₂ h (hComp h (hId b))

namespace HorizBicat

variable {Obj : Type u} [HorizBicat.{u, v, w} Obj]

/-- Notation for horizontal identity -/
scoped notation "𝟙ₕ" => hId

/-- Notation for horizontal composition -/
scoped infixr:80 " ⬝ₕ " => hComp

end HorizBicat

/-! ## Cell Structure -/

/-- Operations on 2-cells (squares) -/
class CellStruct (Obj : Type u) [VertCat.{u, v} Obj] [HorizBicat.{u, v, w} Obj] where
  /-- 2-cells with the given boundary -/
  Cell : {a b c d : Obj} →
    VertCat.Vert a c → VertCat.Vert b d →
    HorizBicat.Horiz a b → HorizBicat.Horiz c d → Type w

  /-- Vertical composition of cells (strict)
      ```
          h           h
      a ---→ b    a ---→ b
      |      |    |      |
    f |  α   | g  |      |
      ↓      ↓    | f⬝f' | α⬝ᵥβ
      c ---→ d  = |      |
      |      |    |      |
   f' |  β   | g' |      |
      ↓      ↓    ↓      ↓
      e ---→ z    e ---→ z
          m           m
      ```
  -/
  vCellComp : {a b c d e z : Obj} →
    {vf : VertCat.Vert a c} → {vg : VertCat.Vert b d} →
    {vf' : VertCat.Vert c e} → {vg' : VertCat.Vert d z} →
    {h : HorizBicat.Horiz a b} → {k : HorizBicat.Horiz c d} →
    {m : HorizBicat.Horiz e z} →
    Cell vf vg h k → Cell vf' vg' k m →
    Cell (VertCat.vComp vf vf') (VertCat.vComp vg vg') h m

  /-- Horizontal composition of cells (weak)
      ```
          h       k           h ⬝ₕ k
      a ---→ b ---→ c     a -------→ c
      |      |      |     |          |
    f |  α   | g  β | i = f | α⬝ₕβ  | i
      ↓      ↓      ↓     ↓          ↓
      d ---→ e ---→ z     d -------→ z
          m       n           m ⬝ₕ n
      ```
  -/
  hCellComp : {a b c d e z : Obj} →
    {vf : VertCat.Vert a d} → {vg : VertCat.Vert b e} →
    {vi : VertCat.Vert c z} →
    {h : HorizBicat.Horiz a b} → {k : HorizBicat.Horiz b c} →
    {m : HorizBicat.Horiz d e} → {n : HorizBicat.Horiz e z} →
    Cell vf vg h m → Cell vg vi k n →
    Cell vf vi (HorizBicat.hComp h k) (HorizBicat.hComp m n)

  /-- Identity cell on a vertical morphism -/
  cellVId : {a b : Obj} → (f : VertCat.Vert a b) →
    Cell f f (HorizBicat.hId a) (HorizBicat.hId b)

  /-- Identity cell on a horizontal morphism -/
  cellHId : {a b : Obj} → (h : HorizBicat.Horiz a b) →
    Cell (VertCat.vId a) (VertCat.vId b) h h

namespace CellStruct

variable {Obj : Type u} [VertCat.{u, v} Obj] [HorizBicat.{u, v, w} Obj]
variable [CellStruct.{u, v, w} Obj]

/-- Notation for vertical cell composition -/
scoped infixr:80 " ⬝ᶜᵥ " => vCellComp

/-- Notation for horizontal cell composition -/
scoped infixr:80 " ⬝ᶜₕ " => hCellComp

end CellStruct

/-! ## Full Layer 1 Bundle -/

/-- A pre-pseudo-double category: all structure without coherence axioms for cells.

    This combines:
    - Strict vertical category
    - Weak horizontal bicategory (with coherence isomorphisms but no pentagon/triangle yet)
    - Cell structure with vertical and horizontal composition
-/
class PrePseudoDoubleCat (Obj : Type u) extends
    VertCat.{u, v} Obj,
    HorizBicat.{u, v, w} Obj,
    CellStruct.{u, v, w} Obj

/-! ## Layer 2: Coherence Axioms -/

/-- The interchange law for 2-cells.

    Given a 2×2 grid of cells:
    ```
          h₁      h₂
      a ----→ b ----→ c
      |       |       |
    f₁|   α   |g₁  β  |i₁
      ↓       ↓       ↓
      d ----→ e ----→ f
      |       |       |
    f₂|   γ   |g₂  δ  |i₂
      ↓       ↓       ↓
      x ----→ y ----→ z
          k₁      k₂
    ```

    The interchange law states:
      (α ⬝ᶜᵥ γ) ⬝ᶜₕ (β ⬝ᶜᵥ δ) = (α ⬝ᶜₕ β) ⬝ᶜᵥ (γ ⬝ᶜₕ δ)

    That is, composing vertically first then horizontally equals
    composing horizontally first then vertically.
-/
class Interchange (Obj : Type u) [VertCat.{u, v} Obj] [HorizBicat.{u, v, w} Obj]
    [CellStruct.{u, v, w} Obj] : Prop where
  /-- The interchange law -/
  interchange :
    ∀ {a b c d e f x y z : Obj}
      {f₁ : VertCat.Vert a d} {g₁ : VertCat.Vert b e} {i₁ : VertCat.Vert c f}
      {f₂ : VertCat.Vert d x} {g₂ : VertCat.Vert e y} {i₂ : VertCat.Vert f z}
      {h₁ : HorizBicat.Horiz a b} {h₂ : HorizBicat.Horiz b c}
      {m₁ : HorizBicat.Horiz d e} {m₂ : HorizBicat.Horiz e f}
      {k₁ : HorizBicat.Horiz x y} {k₂ : HorizBicat.Horiz y z}
      (α : CellStruct.Cell f₁ g₁ h₁ m₁)
      (β : CellStruct.Cell g₁ i₁ h₂ m₂)
      (γ : CellStruct.Cell f₂ g₂ m₁ k₁)
      (δ : CellStruct.Cell g₂ i₂ m₂ k₂),
    CellStruct.hCellComp (CellStruct.vCellComp α γ) (CellStruct.vCellComp β δ) =
    CellStruct.vCellComp (CellStruct.hCellComp α β) (CellStruct.hCellComp γ δ)

/-- Unit laws for vertical cell composition -/
class VCellUnitLaws (Obj : Type u) [VertCat.{u, v} Obj] [HorizBicat.{u, v, w} Obj]
    [CellStruct.{u, v, w} Obj] : Prop where
  /-- Left unit: cellHId ⬝ᶜᵥ α = α (up to reindexing by vId_comp) -/
  vCellComp_cellHId_left :
    ∀ {a b c d : Obj}
      {f : VertCat.Vert a c} {g : VertCat.Vert b d}
      {h : HorizBicat.Horiz a b} {k : HorizBicat.Horiz c d}
      (α : CellStruct.Cell f g h k),
    HEq (CellStruct.vCellComp (CellStruct.cellHId h) α) α
  /-- Right unit: α ⬝ᶜᵥ cellHId = α (up to reindexing by vComp_id) -/
  vCellComp_cellHId_right :
    ∀ {a b c d : Obj}
      {f : VertCat.Vert a c} {g : VertCat.Vert b d}
      {h : HorizBicat.Horiz a b} {k : HorizBicat.Horiz c d}
      (α : CellStruct.Cell f g h k),
    HEq (CellStruct.vCellComp α (CellStruct.cellHId k)) α

/-- Associativity for vertical cell composition -/
class VCellAssoc (Obj : Type u) [VertCat.{u, v} Obj] [HorizBicat.{u, v, w} Obj]
    [CellStruct.{u, v, w} Obj] : Prop where
  /-- Vertical cell composition is associative (up to reindexing by vComp_assoc) -/
  vCellComp_assoc :
    ∀ {a b c d e f x y : Obj}
      {f₁ : VertCat.Vert a c} {g₁ : VertCat.Vert b d}
      {f₂ : VertCat.Vert c e} {g₂ : VertCat.Vert d f}
      {f₃ : VertCat.Vert e x} {g₃ : VertCat.Vert f y}
      {h : HorizBicat.Horiz a b} {k : HorizBicat.Horiz c d}
      {m : HorizBicat.Horiz e f} {n : HorizBicat.Horiz x y}
      (α : CellStruct.Cell f₁ g₁ h k)
      (β : CellStruct.Cell f₂ g₂ k m)
      (γ : CellStruct.Cell f₃ g₃ m n),
    HEq (CellStruct.vCellComp (CellStruct.vCellComp α β) γ)
        (CellStruct.vCellComp α (CellStruct.vCellComp β γ))

/-- A pseudo-double category with all coherence laws.

    Layer 2 adds:
    - Interchange law
    - Unit laws for vertical cell composition
    - Associativity for vertical cell composition

    Note: Horizontal cell composition coherence is inherited from the
    bicategory structure (associator, unitors act on cells).
-/
class IsPseudoDouble (Obj : Type u) extends PrePseudoDoubleCat.{u, v, w} Obj where
  [interchange : Interchange.{u, v, w} Obj]
  [vCellUnitLaws : VCellUnitLaws.{u, v, w} Obj]
  [vCellAssoc : VCellAssoc.{u, v, w} Obj]

attribute [instance] IsPseudoDouble.interchange
attribute [instance] IsPseudoDouble.vCellUnitLaws
attribute [instance] IsPseudoDouble.vCellAssoc

/-! ## Example: Trivial pseudo-double category on a single object -/

/-- The trivial pre-pseudo-double category with one object and only identity morphisms -/
instance : PrePseudoDoubleCat Unit where
  -- Vertical category
  Vert := fun _ _ => Unit
  vId := fun _ => ()
  vComp := fun _ _ => ()
  vComp_assoc := fun _ _ _ => rfl
  vId_comp := fun _ => rfl
  vComp_id := fun _ => rfl
  -- Horizontal bicategory
  Horiz := fun _ _ => Unit
  hId := fun _ => ()
  hComp := fun _ _ => ()
  Horiz₂ := fun _ _ => Unit
  hAssoc := fun _ _ _ => ()
  hAssoc_inv := fun _ _ _ => ()
  hLeftUnitor := fun _ => ()
  hLeftUnitor_inv := fun _ => ()
  hRightUnitor := fun _ => ()
  hRightUnitor_inv := fun _ => ()
  -- Cell structure
  Cell := fun _ _ _ _ => Unit
  vCellComp := fun _ _ => ()
  hCellComp := fun _ _ => ()
  cellVId := fun _ => ()
  cellHId := fun _ => ()

/-- Interchange law holds trivially for Unit -/
instance : Interchange Unit where
  interchange := fun _ _ _ _ => rfl

/-- Vertical cell unit laws hold trivially for Unit -/
instance : VCellUnitLaws Unit where
  vCellComp_cellHId_left := fun _ => HEq.rfl
  vCellComp_cellHId_right := fun _ => HEq.rfl

/-- Vertical cell associativity holds trivially for Unit -/
instance : VCellAssoc Unit where
  vCellComp_assoc := fun _ _ _ => HEq.rfl

/-- The trivial pseudo-double category with one object -/
instance : IsPseudoDouble Unit where

end PseudoDoubleCat
