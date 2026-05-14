/-
  Pseudo-Double Categories

  A pseudo-double category has:
  - Objects
  - Vertical morphisms (tight): strictly associative composition
  - Horizontal morphisms (loose): weakly associative composition (bicategory structure)
  - 2-cells (squares): with both vertical and horizontal composition

  This file defines the complete structure including:
  - Layer 1: Raw data structures (VertCat, HorizBicat, CellStruct)
  - Layer 2: Coherence axioms (Interchange, pentagon/triangle, cell unit/assoc laws)

  References:
  - Grandis & Paré, "Limits in double categories", Cahiers de Topologie, 1999
  - nLab: https://ncatlab.org/nlab/show/pseudo+double+category
-/

import Mathlib.CategoryTheory.Category.Basic
import Aesop

universe u v w

namespace DoubleCat

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

    Includes coherence isomorphisms, 2-morphism category structure, and whiskering.
    Pentagon/triangle axioms are in `HorizBicatCoherence`.
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

  -- 2-morphism category structure
  /-- Identity 2-morphism -/
  h2Id : {a b : Obj} → (h : Horiz a b) → Horiz₂ h h
  /-- Vertical composition of 2-morphisms -/
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

  -- Whiskering operations
  /-- Left whiskering: h ⊳ α for α : k → m gives h ⬝ k → h ⬝ m -/
  hWhiskerLeft : {a b c : Obj} → (h : Horiz a b) → {k m : Horiz b c} →
    Horiz₂ k m → Horiz₂ (hComp h k) (hComp h m)
  /-- Right whiskering: α ⊲ k for α : h → m gives h ⬝ k → m ⬝ k -/
  hWhiskerRight : {a b c : Obj} → {h m : Horiz a b} →
    Horiz₂ h m → (k : Horiz b c) → Horiz₂ (hComp h k) (hComp m k)

  -- Coherence isomorphisms
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

  -- Isomorphism laws for associators and unitors
  /-- Associator composed with inverse is identity on (h⬝k)⬝m -/
  hAssoc_hAssoc_inv : ∀ {a b c d : Obj} (h : Horiz a b) (k : Horiz b c) (m : Horiz c d),
    h2Comp (hAssoc h k m) (hAssoc_inv h k m) = h2Id (hComp (hComp h k) m)
  /-- Inverse associator composed with associator is identity on h⬝(k⬝m) -/
  hAssoc_inv_hAssoc : ∀ {a b c d : Obj} (h : Horiz a b) (k : Horiz b c) (m : Horiz c d),
    h2Comp (hAssoc_inv h k m) (hAssoc h k m) = h2Id (hComp h (hComp k m))
  /-- Left unitor composed with inverse is identity on id⬝h -/
  hLeftUnitor_hLeftUnitor_inv : ∀ {a b : Obj} (h : Horiz a b),
    h2Comp (hLeftUnitor h) (hLeftUnitor_inv h) = h2Id (hComp (hId a) h)
  /-- Inverse left unitor composed with left unitor is identity on h -/
  hLeftUnitor_inv_hLeftUnitor : ∀ {a b : Obj} (h : Horiz a b),
    h2Comp (hLeftUnitor_inv h) (hLeftUnitor h) = h2Id h
  /-- Right unitor composed with inverse is identity on h⬝id -/
  hRightUnitor_hRightUnitor_inv : ∀ {a b : Obj} (h : Horiz a b),
    h2Comp (hRightUnitor h) (hRightUnitor_inv h) = h2Id (hComp h (hId b))
  /-- Inverse right unitor composed with right unitor is identity on h -/
  hRightUnitor_inv_hRightUnitor : ∀ {a b : Obj} (h : Horiz a b),
    h2Comp (hRightUnitor_inv h) (hRightUnitor h) = h2Id h

  -- Whiskering axioms: functoriality
  /-- Left whiskering preserves identity -/
  hWhiskerLeft_id : ∀ {a b c : Obj} (f : Horiz a b) (g : Horiz b c),
    hWhiskerLeft f (h2Id g) = h2Id (hComp f g)
  /-- Left whiskering preserves composition -/
  hWhiskerLeft_comp : ∀ {a b c : Obj} (f : Horiz a b) {g h k : Horiz b c}
    (η : Horiz₂ g h) (θ : Horiz₂ h k),
    hWhiskerLeft f (h2Comp η θ) = h2Comp (hWhiskerLeft f η) (hWhiskerLeft f θ)
  /-- Right whiskering preserves identity -/
  hWhiskerRight_id : ∀ {a b c : Obj} (f : Horiz a b) (g : Horiz b c),
    hWhiskerRight (h2Id f) g = h2Id (hComp f g)
  /-- Right whiskering preserves composition -/
  hWhiskerRight_comp : ∀ {a b c : Obj} {f g h : Horiz a b}
    (η : Horiz₂ f g) (θ : Horiz₂ g h) (k : Horiz b c),
    hWhiskerRight (h2Comp η θ) k = h2Comp (hWhiskerRight η k) (hWhiskerRight θ k)

  -- Whiskering with identity morphisms (naturality with unitors)
  /-- Left whiskering with identity relates to left unitor -/
  id_hWhiskerLeft : ∀ {a b : Obj} {f g : Horiz a b} (η : Horiz₂ f g),
    hWhiskerLeft (hId a) η = h2Comp (hLeftUnitor f) (h2Comp η (hLeftUnitor_inv g))
  /-- Right whiskering with identity relates to right unitor -/
  hWhiskerRight_hId : ∀ {a b : Obj} {f g : Horiz a b} (η : Horiz₂ f g),
    hWhiskerRight η (hId b) = h2Comp (hRightUnitor f) (h2Comp η (hRightUnitor_inv g))

  -- Whiskering with composite morphisms (naturality with associators)
  /-- Left whiskering with a composite relates to associator -/
  hComp_hWhiskerLeft : ∀ {a b c d : Obj} (f : Horiz a b) (g : Horiz b c) {h h' : Horiz c d}
    (η : Horiz₂ h h'),
    hWhiskerLeft (hComp f g) η =
      h2Comp (hAssoc f g h) (h2Comp (hWhiskerLeft f (hWhiskerLeft g η)) (hAssoc_inv f g h'))
  /-- Right whiskering with a composite relates to associator -/
  hWhiskerRight_hComp : ∀ {a b c d : Obj} {f f' : Horiz a b} (η : Horiz₂ f f')
    (g : Horiz b c) (h : Horiz c d),
    hWhiskerRight η (hComp g h) =
      h2Comp (hAssoc_inv f g h) (h2Comp (hWhiskerRight (hWhiskerRight η g) h) (hAssoc f' g h))

  -- Whisker associativity
  /-- Whiskering associativity: moving whiskers across associators -/
  whisker_assoc : ∀ {a b c d : Obj} (f : Horiz a b) {g g' : Horiz b c} (η : Horiz₂ g g')
    (h : Horiz c d),
    hWhiskerRight (hWhiskerLeft f η) h =
      h2Comp (hAssoc f g h) (h2Comp (hWhiskerLeft f (hWhiskerRight η h)) (hAssoc_inv f g' h))

  -- Exchange law
  /-- Exchange law: left and right whiskering commute -/
  whisker_exchange : ∀ {a b c : Obj} {f g : Horiz a b} {h k : Horiz b c}
    (η : Horiz₂ f g) (θ : Horiz₂ h k),
    h2Comp (hWhiskerLeft f θ) (hWhiskerRight η k) =
    h2Comp (hWhiskerRight η h) (hWhiskerLeft g θ)

namespace HorizBicat

variable {Obj : Type u} [HorizBicat.{u, v, w} Obj]

/-- Notation for horizontal identity -/
scoped notation "𝟙ₕ" => hId

/-- Notation for horizontal composition -/
scoped infixr:80 " ⬝ₕ " => hComp

/-- Notation for 2-morphism vertical composition -/
scoped infixr:80 " ⬝₂ " => h2Comp

/-- Notation for left whiskering -/
scoped infixr:70 " ⊳ " => hWhiskerLeft

/-- Notation for right whiskering -/
scoped infixl:70 " ⊲ " => hWhiskerRight

end HorizBicat

/-- Pentagon and triangle coherence axioms for horizontal bicategory structure.

    Pentagon: For h : a → b, k : b → c, m : c → d, n : d → e:
    ```
      ((h ⬝ k) ⬝ m) ⬝ n  --α-->  (h ⬝ k) ⬝ (m ⬝ n)  --α-->  h ⬝ (k ⬝ (m ⬝ n))
             |                                                      ^
           α⊲n                                                    h⊳α
             v                                                      |
      (h ⬝ (k ⬝ m)) ⬝ n  ----------------α---------------------->  h ⬝ ((k ⬝ m) ⬝ n)
    ```

    Triangle: For h : a → b, k : b → c:
    ```
      (h ⬝ id) ⬝ k  --α-->  h ⬝ (id ⬝ k)
            |                     |
          ρ⊲k                   h⊳λ
            v                     v
          h ⬝ k  =========  h ⬝ k
    ```
-/
class HorizBicatCoherence (Obj : Type u) [HorizBicat.{u, v, w} Obj] : Prop where
  /-- Pentagon identity -/
  pentagon : ∀ {a b c d e : Obj}
    (h : HorizBicat.Horiz a b) (k : HorizBicat.Horiz b c)
    (m : HorizBicat.Horiz c d) (n : HorizBicat.Horiz d e),
    HorizBicat.h2Comp
      (HorizBicat.h2Comp (HorizBicat.hWhiskerRight (HorizBicat.hAssoc h k m) n) (HorizBicat.hAssoc h (HorizBicat.hComp k m) n))
      (HorizBicat.hWhiskerLeft h (HorizBicat.hAssoc k m n)) =
    HorizBicat.h2Comp (HorizBicat.hAssoc (HorizBicat.hComp h k) m n) (HorizBicat.hAssoc h k (HorizBicat.hComp m n))
  /-- Triangle identity -/
  triangle : ∀ {a b c : Obj}
    (h : HorizBicat.Horiz a b) (k : HorizBicat.Horiz b c),
    HorizBicat.h2Comp (HorizBicat.hAssoc h (HorizBicat.hId b) k) (HorizBicat.hWhiskerLeft h (HorizBicat.hLeftUnitor k)) =
    HorizBicat.hWhiskerRight (HorizBicat.hRightUnitor h) k

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

  /-- Associator cell: witnesses hCellComp associativity -/
  cellHAssoc : {a b c d : Obj} →
    (h : HorizBicat.Horiz a b) → (k : HorizBicat.Horiz b c) → (m : HorizBicat.Horiz c d) →
    Cell (VertCat.vId a) (VertCat.vId d)
      (HorizBicat.hComp (HorizBicat.hComp h k) m)
      (HorizBicat.hComp h (HorizBicat.hComp k m))

  /-- Left unitor cell -/
  cellHLeftUnitor : {a b : Obj} → (h : HorizBicat.Horiz a b) →
    Cell (VertCat.vId a) (VertCat.vId b) (HorizBicat.hComp (HorizBicat.hId a) h) h

  /-- Right unitor cell -/
  cellHRightUnitor : {a b : Obj} → (h : HorizBicat.Horiz a b) →
    Cell (VertCat.vId a) (VertCat.vId b) (HorizBicat.hComp h (HorizBicat.hId b)) h

  /-- Inverse associator cell -/
  cellHAssoc_inv : {a b c d : Obj} →
    (h : HorizBicat.Horiz a b) → (k : HorizBicat.Horiz b c) → (m : HorizBicat.Horiz c d) →
    Cell (VertCat.vId a) (VertCat.vId d)
      (HorizBicat.hComp h (HorizBicat.hComp k m))
      (HorizBicat.hComp (HorizBicat.hComp h k) m)

  /-- Inverse left unitor cell -/
  cellHLeftUnitor_inv : {a b : Obj} → (h : HorizBicat.Horiz a b) →
    Cell (VertCat.vId a) (VertCat.vId b) h (HorizBicat.hComp (HorizBicat.hId a) h)

  /-- Inverse right unitor cell -/
  cellHRightUnitor_inv : {a b : Obj} → (h : HorizBicat.Horiz a b) →
    Cell (VertCat.vId a) (VertCat.vId b) h (HorizBicat.hComp h (HorizBicat.hId b))

  -- Isomorphism laws for cell coherence (up to HEq due to vertical identity composition)
  /-- cellHAssoc ⬝ᵥ cellHAssoc_inv = cellHId (up to vId_comp reindexing) -/
  cellHAssoc_cellHAssoc_inv : {a b c d : Obj} →
    (h : HorizBicat.Horiz a b) → (k : HorizBicat.Horiz b c) → (m : HorizBicat.Horiz c d) →
    HEq (vCellComp (cellHAssoc h k m) (cellHAssoc_inv h k m))
        (cellHId (HorizBicat.hComp (HorizBicat.hComp h k) m))
  /-- cellHAssoc_inv ⬝ᵥ cellHAssoc = cellHId (up to vId_comp reindexing) -/
  cellHAssoc_inv_cellHAssoc : {a b c d : Obj} →
    (h : HorizBicat.Horiz a b) → (k : HorizBicat.Horiz b c) → (m : HorizBicat.Horiz c d) →
    HEq (vCellComp (cellHAssoc_inv h k m) (cellHAssoc h k m))
        (cellHId (HorizBicat.hComp h (HorizBicat.hComp k m)))
  /-- cellHLeftUnitor ⬝ᵥ cellHLeftUnitor_inv = cellHId (up to vId_comp reindexing) -/
  cellHLeftUnitor_cellHLeftUnitor_inv : {a b : Obj} → (h : HorizBicat.Horiz a b) →
    HEq (vCellComp (cellHLeftUnitor h) (cellHLeftUnitor_inv h))
        (cellHId (HorizBicat.hComp (HorizBicat.hId a) h))
  /-- cellHLeftUnitor_inv ⬝ᵥ cellHLeftUnitor = cellHId (up to vId_comp reindexing) -/
  cellHLeftUnitor_inv_cellHLeftUnitor : {a b : Obj} → (h : HorizBicat.Horiz a b) →
    HEq (vCellComp (cellHLeftUnitor_inv h) (cellHLeftUnitor h))
        (cellHId h)
  /-- cellHRightUnitor ⬝ᵥ cellHRightUnitor_inv = cellHId (up to vId_comp reindexing) -/
  cellHRightUnitor_cellHRightUnitor_inv : {a b : Obj} → (h : HorizBicat.Horiz a b) →
    HEq (vCellComp (cellHRightUnitor h) (cellHRightUnitor_inv h))
        (cellHId (HorizBicat.hComp h (HorizBicat.hId b)))
  /-- cellHRightUnitor_inv ⬝ᵥ cellHRightUnitor = cellHId (up to vId_comp reindexing) -/
  cellHRightUnitor_inv_cellHRightUnitor : {a b : Obj} → (h : HorizBicat.Horiz a b) →
    HEq (vCellComp (cellHRightUnitor_inv h) (cellHRightUnitor h))
        (cellHId h)

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
class PreDoubleCat (Obj : Type u) extends
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

/-- Unit laws for horizontal cell composition.

    In a pseudo-double category, horizontal composition with identity cells
    is unital only up to coherence isomorphisms. These laws express naturality
    of the cell unitors with respect to arbitrary cells.

    For a cell α : Cell f g h k, the left unit naturality says:
      cellHLeftUnitor h ⬝ᶜᵥ α = (cellVId f ⬝ᶜₕ α) ⬝ᶜᵥ cellHLeftUnitor k
    (up to HEq because vertical boundaries differ by vId_comp vs vComp_id)
-/
class HCellUnitLaws (Obj : Type u) [VertCat.{u, v} Obj] [HorizBicat.{u, v, w} Obj]
    [CellStruct.{u, v, w} Obj] : Prop where
  /-- Left unit naturality: cellHLeftUnitor ⬝ᶜᵥ α = (cellVId ⬝ᶜₕ α) ⬝ᶜᵥ cellHLeftUnitor -/
  hCellComp_cellVId_left :
    ∀ {a b c d : Obj}
      {f : VertCat.Vert a c} {g : VertCat.Vert b d}
      {h : HorizBicat.Horiz a b} {k : HorizBicat.Horiz c d}
      (α : CellStruct.Cell f g h k),
    HEq (CellStruct.vCellComp (CellStruct.cellHLeftUnitor h) α)
        (CellStruct.vCellComp (CellStruct.hCellComp (CellStruct.cellVId f) α)
                              (CellStruct.cellHLeftUnitor k))
  /-- Right unit naturality: cellHRightUnitor ⬝ᶜᵥ α = (α ⬝ᶜₕ cellVId) ⬝ᶜᵥ cellHRightUnitor -/
  hCellComp_cellVId_right :
    ∀ {a b c d : Obj}
      {f : VertCat.Vert a c} {g : VertCat.Vert b d}
      {h : HorizBicat.Horiz a b} {k : HorizBicat.Horiz c d}
      (α : CellStruct.Cell f g h k),
    HEq (CellStruct.vCellComp (CellStruct.cellHRightUnitor h) α)
        (CellStruct.vCellComp (CellStruct.hCellComp α (CellStruct.cellVId g))
                              (CellStruct.cellHRightUnitor k))

/-- Associativity for horizontal cell composition.

    In a pseudo-double category, horizontal composition is associative only
    up to the cell associator. This is the naturality of cellHAssoc:

    For cells α, β, γ that can be horizontally composed:
      cellHAssoc ⬝ᶜᵥ (α ⬝ᶜₕ (β ⬝ᶜₕ γ)) = ((α ⬝ᶜₕ β) ⬝ᶜₕ γ) ⬝ᶜᵥ cellHAssoc
    (up to HEq because vertical boundaries differ by vId_comp vs vComp_id)
-/
class HCellAssoc (Obj : Type u) [VertCat.{u, v} Obj] [HorizBicat.{u, v, w} Obj]
    [CellStruct.{u, v, w} Obj] : Prop where
  /-- Naturality of cell associator -/
  hCellComp_assoc :
    ∀ {a b c d e f g h : Obj}
      {f₁ : VertCat.Vert a e} {g₁ : VertCat.Vert b f}
      {h₁ : VertCat.Vert c g} {i₁ : VertCat.Vert d h}
      {hm₁ : HorizBicat.Horiz a b} {hm₂ : HorizBicat.Horiz b c} {hm₃ : HorizBicat.Horiz c d}
      {km₁ : HorizBicat.Horiz e f} {km₂ : HorizBicat.Horiz f g} {km₃ : HorizBicat.Horiz g h}
      (α : CellStruct.Cell f₁ g₁ hm₁ km₁)
      (β : CellStruct.Cell g₁ h₁ hm₂ km₂)
      (γ : CellStruct.Cell h₁ i₁ hm₃ km₃),
    HEq (CellStruct.vCellComp
           (CellStruct.cellHAssoc hm₁ hm₂ hm₃)
           (CellStruct.hCellComp α (CellStruct.hCellComp β γ)))
        (CellStruct.vCellComp
           (CellStruct.hCellComp (CellStruct.hCellComp α β) γ)
           (CellStruct.cellHAssoc km₁ km₂ km₃))

/-- A pseudo-double category with all coherence laws.

    Layer 2 adds:
    - Pentagon and triangle identities for horizontal bicategory
    - Interchange law
    - Unit laws for vertical and horizontal cell composition
    - Associativity for vertical and horizontal cell composition
    - Naturality of cell coherence isomorphisms
-/
class IsDouble (Obj : Type u) extends PreDoubleCat.{u, v, w} Obj where
  [horizBicatCoherence : HorizBicatCoherence.{u, v, w} Obj]
  [interchange : Interchange.{u, v, w} Obj]
  [vCellUnitLaws : VCellUnitLaws.{u, v, w} Obj]
  [vCellAssoc : VCellAssoc.{u, v, w} Obj]
  [hCellUnitLaws : HCellUnitLaws.{u, v, w} Obj]
  [hCellAssoc : HCellAssoc.{u, v, w} Obj]

attribute [instance] IsDouble.horizBicatCoherence
attribute [instance] IsDouble.interchange
attribute [instance] IsDouble.vCellUnitLaws
attribute [instance] IsDouble.vCellAssoc
attribute [instance] IsDouble.hCellUnitLaws
attribute [instance] IsDouble.hCellAssoc

/-! ## Example: Trivial pseudo-double category on a single object -/

/-- The trivial pre-pseudo-double category with one object and only identity morphisms -/
instance : PreDoubleCat Unit where
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
  -- 2-morphism category structure
  h2Id := fun _ => ()
  h2Comp := fun _ _ => ()
  h2Comp_assoc := fun _ _ _ => rfl
  h2Id_comp := fun _ => rfl
  h2Comp_id := fun _ => rfl
  -- Whiskering
  hWhiskerLeft := @fun _ _ _ _ _ _ _ => ()
  hWhiskerRight := @fun _ _ _ _ _ _ _ => ()
  -- Coherence isomorphisms
  hAssoc := fun _ _ _ => ()
  hAssoc_inv := fun _ _ _ => ()
  hLeftUnitor := fun _ => ()
  hLeftUnitor_inv := fun _ => ()
  hRightUnitor := fun _ => ()
  hRightUnitor_inv := fun _ => ()
  -- Isomorphism laws
  hAssoc_hAssoc_inv := fun _ _ _ => rfl
  hAssoc_inv_hAssoc := fun _ _ _ => rfl
  hLeftUnitor_hLeftUnitor_inv := fun _ => rfl
  hLeftUnitor_inv_hLeftUnitor := fun _ => rfl
  hRightUnitor_hRightUnitor_inv := fun _ => rfl
  hRightUnitor_inv_hRightUnitor := fun _ => rfl
  -- Whiskering axioms
  hWhiskerLeft_id := fun _ _ => rfl
  hWhiskerLeft_comp := @fun _ _ _ _ _ _ _ _ _ => rfl
  hWhiskerRight_id := fun _ _ => rfl
  hWhiskerRight_comp := @fun _ _ _ _ _ _ _ _ _ => rfl
  id_hWhiskerLeft := @fun _ _ _ _ _ => rfl
  hWhiskerRight_hId := @fun _ _ _ _ _ => rfl
  hComp_hWhiskerLeft := @fun _ _ _ _ _ _ _ _ _ => rfl
  hWhiskerRight_hComp := @fun _ _ _ _ _ _ _ _ _ => rfl
  whisker_assoc := @fun _ _ _ _ _ _ _ _ _ => rfl
  whisker_exchange := @fun _ _ _ _ _ _ _ _ _ => rfl
  -- Cell structure
  Cell := fun _ _ _ _ => Unit
  vCellComp := fun _ _ => ()
  hCellComp := fun _ _ => ()
  cellVId := fun _ => ()
  cellHId := fun _ => ()
  -- Cell coherence isomorphisms
  cellHAssoc := fun _ _ _ => ()
  cellHLeftUnitor := fun _ => ()
  cellHRightUnitor := fun _ => ()
  cellHAssoc_inv := fun _ _ _ => ()
  cellHLeftUnitor_inv := fun _ => ()
  cellHRightUnitor_inv := fun _ => ()
  -- Cell coherence isomorphism inverse laws
  cellHAssoc_cellHAssoc_inv := fun _ _ _ => HEq.rfl
  cellHAssoc_inv_cellHAssoc := fun _ _ _ => HEq.rfl
  cellHLeftUnitor_cellHLeftUnitor_inv := fun _ => HEq.rfl
  cellHLeftUnitor_inv_cellHLeftUnitor := fun _ => HEq.rfl
  cellHRightUnitor_cellHRightUnitor_inv := fun _ => HEq.rfl
  cellHRightUnitor_inv_cellHRightUnitor := fun _ => HEq.rfl

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

/-- Horizontal bicategory coherence holds trivially for Unit -/
instance : HorizBicatCoherence Unit where
  pentagon := fun _ _ _ _ => rfl
  triangle := fun _ _ => rfl

/-- Horizontal cell unit laws hold trivially for Unit -/
instance : HCellUnitLaws Unit where
  hCellComp_cellVId_left := fun _ => HEq.rfl
  hCellComp_cellVId_right := fun _ => HEq.rfl

/-- Horizontal cell associativity holds trivially for Unit -/
instance : HCellAssoc Unit where
  hCellComp_assoc := fun _ _ _ => HEq.rfl

/-- The trivial pseudo-double category with one object -/
instance : IsDouble Unit where

end DoubleCat

/-! ## Vericode Tactic Infrastructure

The `vericode` tactic synthesizes 2-cells (implementations) by searching through
registered combinators. Combinators are registered using the `@[aesop]` attribute
with the `Vericode` rule set.

To register a combinator for a specific pseudo-double category:
```
@[aesop safe apply (rule_sets := [Vericode])] def myCombinator := ...
```

Then use `vericode` to automatically search for applicable combinators.
-/

-- Rule set for the vericode tactic. Register combinators with:
-- `@[aesop safe apply (rule_sets := [Vericode])]`
declare_aesop_rule_sets [Vericode]

/-- Tactic for synthesizing 2-cells by searching registered combinators.
    Works with any pseudo-double category whose combinators are registered
    in the `Vericode` rule set. -/
syntax "vericode" : tactic
macro_rules | `(tactic| vericode) => `(tactic| aesop (rule_sets := [Vericode]))
