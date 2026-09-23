/-!
# `ListLike`: an abstract interface for list-shaped types

`ListLike T` says that the type family `T` is usable as a list type: it supplies
the two constructors and the recursor. Every field has exactly the signature of
its `List` counterpart, with `List A` replaced by `T A`:

| `List`      | `ListLike`  |
| ----------- | ----------- |
| `List`      | `T`         |
| `List.nil`  | `Nil`       |
| `List.cons` | `Cons`      |
| `List.rec`  | `ListRec`   |

`T` is the sole class parameter, and the element type `A` is bound inside each
field — mirroring `List` itself, which is one type family polymorphic in its
element type. So instance search dispatches on `T` alone, with nothing left
undetermined.

Because `ListRec` eliminates into `Sort v`, the class carries a second universe
parameter `v` alongside the universe `u` of the elements.
-/

namespace ListLanguage

universe u v

/-- `T` is an abstract list type: it has the constructors `Nil` and `Cons`, and
    the list recursor `ListRec`, each polymorphic in the element type `A`.

    The intended instance is `T := List`, for which the fields are literally
    `List.nil`, `List.cons` and `List.rec`. -/
class ListLike (T : Type u → Type u) where
  /-- The empty list, mirroring `List.nil : {A : Type u} → List A`. -/
  Nil : {A : Type u} → T A
  /-- Prepending, mirroring `List.cons : {A : Type u} → A → List A → List A`. -/
  Cons : {A : Type u} → A → T A → T A
  /-- The recursor, mirroring
      `List.rec : {A : Type u} → {motive : List A → Sort v} → motive .nil →
        ((head : A) → (tail : List A) → motive tail → motive (.cons head tail)) →
        (t : List A) → motive t`. -/
  ListRec : {A : Type u} → {motive : T A → Sort v} → motive Nil →
    ((head : A) → (tail : T A) → motive tail → motive (Cons head tail)) →
    (t : T A) → motive t

/-- `List.rec` written as structural recursion, so that it is compiled by the
    equation compiler rather than by the (code-generator-unsupported) recursor. -/
def listRec {A : Type u} {motive : List A → Sort v} (base : motive [])
    (step : (head : A) → (tail : List A) → motive tail → motive (head :: tail)) :
    (t : List A) → motive t
  | [] => base
  | head :: tail => step head tail (listRec base step tail)

/-- `List` is the prototypical `ListLike`. -/
instance instListLikeList : ListLike List where
  Nil := List.nil
  Cons := List.cons
  ListRec := listRec

/-! ## Further instances

With the expected computation rules (`ListRec b s Nil = b` and
`ListRec b s (Cons h t) = s h t (ListRec b s t)`), `ListRec` says that `T A` is
the initial algebra of `X ↦ Unit ⊕ (A × X)`. So the instances are exactly the
alternative *representations* of a list — order and multiplicity must survive.
Collection types that quotient those away have no instance: for `Multiset` the
cons rule already forces `[a, b] = [b, a]` (via `cons_swap`), and for
`Finset`/`Set` it clashes with idempotence of `insert`. That is why Mathlib's
`Multiset.rec` carries an extra coherence hypothesis and `Finset` has only a
`Prop`-valued induction principle. -/

/-- `Array` is `List` in a different representation: the same order, but `Cons`
    rebuilds rather than sharing, so it is `O(n)` instead of `O(1)`. -/
instance instListLikeArray : ListLike Array where
  Nil := ⟨[]⟩
  Cons a s := ⟨a :: s.toList⟩
  ListRec {_A} {motive} base step s :=
    listRec (motive := fun l => motive ⟨l⟩) base (fun h t ih => step h ⟨t⟩ ih) s.toList

/-! ### Snoc-lists

A list built from the other end. This is the instructive instance: `ListLike`
peels elements off the *far* end of a `SnocList`, so `ListRec` is emphatically
**not** `SnocList.rec`. It is `listRec` transported across `SnocList A ≅ List A`,
which is what `ofList_toList` is for. -/

/-- Lists that grow at the tail. -/
inductive SnocList (A : Type u) where
  | nil
  | snoc : SnocList A → A → SnocList A

namespace SnocList

variable {A : Type u}

/-- Prepend at the far end, rebuilding the spine. -/
def cons (a : A) : SnocList A → SnocList A
  | .nil => .snoc .nil a
  | .snoc s b => .snoc (cons a s) b

/-- Forget the representation. -/
def toList : SnocList A → List A
  | .nil => []
  | .snoc s b => s.toList ++ [b]

/-- Rebuild from a `List`; inverse to `toList`. -/
def ofList : List A → SnocList A
  | [] => .nil
  | a :: l => cons a (ofList l)

theorem toList_cons (a : A) : ∀ s : SnocList A, (cons a s).toList = a :: s.toList
  | .nil => rfl
  | .snoc s _ => by simp [cons, toList, toList_cons a s]

theorem ofList_append_singleton (b : A) :
    ∀ l : List A, ofList (l ++ [b]) = (ofList l).snoc b
  | [] => rfl
  | a :: l => by rw [List.cons_append, ofList, ofList_append_singleton b l, ofList, cons]

theorem ofList_toList : ∀ s : SnocList A, ofList s.toList = s
  | .nil => rfl
  | .snoc s b => by rw [toList, ofList_append_singleton, ofList_toList s]

end SnocList

/-- `SnocList` is `ListLike` against its *own* grain: the recursion runs from the
    tail end, transported along `SnocList.ofList_toList`. -/
instance instListLikeSnocList : ListLike SnocList where
  Nil := .nil
  Cons := SnocList.cons
  ListRec {_A} {motive} base step s :=
    SnocList.ofList_toList s ▸
      listRec (motive := fun l => motive (SnocList.ofList l)) base
        (fun h t ih => step h (SnocList.ofList t) ih) s.toList

end ListLanguage
