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

/-- `T` is an abstract list type: it has the constructors `Nil` and `Cons`, and
    the list recursor `ListRec`, each polymorphic in the element type `A`.

    The intended instance is `T := List`, for which the fields are literally
    `List.nil`, `List.cons` and `List.rec`. -/
class ListLike.{u, v} (T : Type u → Type u) where
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
def listRec.{u, v} {A : Type u} {motive : List A → Sort v} (base : motive [])
    (step : (head : A) → (tail : List A) → motive tail → motive (head :: tail)) :
    (t : List A) → motive t
  | [] => base
  | head :: tail => step head tail (listRec base step tail)

/-- `List` is the prototypical `ListLike`. -/
instance instListLikeList.{u, v} : ListLike.{u, v} List where
  Nil := List.nil
  Cons := List.cons
  ListRec := listRec

end ListLanguage
