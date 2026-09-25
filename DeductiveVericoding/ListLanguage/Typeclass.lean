/-!
# `ListRep`: types that represent `List`

`ListRep L A` says that the type `L` is usable as a type of lists of `A`: it
supplies the two constructors and a recursor. For the prototypical instance
`L := List A` the fields are exactly their `List` counterparts:

| `List`      | `ListRep`   |
| ----------- | ----------- |
| `List A`    | `L`         |
| `List.nil`  | `Nil`       |
| `List.cons` | `Cons`      |
| `List.rec`  | `ListRec`   |

## Why the recursor is abstract

`List.rec` recurses into *pointwise* judgments: from a motive `motive : L → Sort v`
it produces a section `(t : L) → motive t`, one value per list. That is not the
only useful form. The vericoding tactic `ListRecTactic` (see `Tactics.lean`)
recurses into *uniform* judgments: from a specification it produces a single
`Impl`, one synthesized program that is correct for every list. No choice of
`motive : L → Sort v` expresses that, since the result is not a per-list family.

So `ListRep` abstracts the judgment form. Each instance chooses
- `Motive`, what a recursion is about,
- `NilCase motive` and `ConsCase motive`, the types of the two minor premises,
- `Result motive`, what the recursion produces,

and `ListRec` turns the two minor premises into the result. `ListRep.ofRec`
builds the pointwise instances, where these four are the ones of `List.rec`.

The element type `A` is an `outParam`: the carrier determines its elements.
-/

namespace ListLanguage

universe u v

/-- `L` is an abstract type of lists of `A`: it has the constructors `Nil` and
    `Cons`, and a recursor `ListRec` into the judgments described by `Motive`,
    `NilCase`, `ConsCase` and `Result`.

    The intended instance is `L := List A`, for which the constructors are
    literally `List.nil` and `List.cons` and the recursor is `List.rec`. -/
class ListRep.{u', w', n', c', r'} (L : Type u') (A : outParam (Type u')) where
  /-- The empty list, mirroring `List.nil : List A`. -/
  Nil : L
  /-- Prepending, mirroring `List.cons : A → List A → List A`. -/
  Cons : A → L → L
  /-- What a recursion is about; `L → Sort v` for pointwise instances. -/
  Motive : Type w'
  /-- The base case's type; `motive Nil` for pointwise instances. -/
  NilCase : Motive → Sort n'
  /-- The step case's type;
      `(head : A) → (tail : L) → motive tail → motive (Cons head tail)` for
      pointwise instances. -/
  ConsCase : Motive → Sort c'
  /-- What the recursion produces; `(t : L) → motive t` for pointwise instances. -/
  Result : Motive → Sort r'
  /-- The recursor, mirroring `List.rec` for pointwise instances. -/
  ListRec : {motive : Motive} → (nil : NilCase motive) → (cons : ConsCase motive) →
    Result motive

/-- The pointwise `ListRep`, whose recursor has exactly the shape of `List.rec`
    with `List A` replaced by `L`. -/
abbrev ListRep.ofRec {L A : Type u} (nil : L) (cons : A → L → L)
    (rec : {motive : L → Sort v} → (nil : motive nil) →
      (cons : (head : A) → (tail : L) → motive tail → motive (cons head tail)) →
      (t : L) → motive t) :
    ListRep.{u, max u v, v, imax (u + 1) (u + 1) v, imax (u + 1) v} L A where
  Nil := nil
  Cons := cons
  Motive := L → Sort v
  NilCase motive := motive nil
  ConsCase motive := (head : A) → (tail : L) → motive tail → motive (cons head tail)
  Result motive := (t : L) → motive t
  ListRec := rec

/-- `List.rec` written as structural recursion, so that it is compiled by the
    equation compiler rather than by the (code-generator-unsupported) recursor.

    Being in eliminator form, it also serves `induction l using listRec with
    | nil => .. | cons head tail ih => ..`, which the abstract `ListRep.ListRec`
    cannot: its result type `Result motive` is not an application of the motive. -/
def listRec {A : Type u} {motive : List A → Sort v} (nil : motive [])
    (cons : (head : A) → (tail : List A) → motive tail → motive (head :: tail)) :
    (t : List A) → motive t
  | [] => nil
  | head :: tail => cons head tail (listRec nil cons tail)

/-- `List` is the prototypical `ListRep`. -/
instance instListRepList {A : Type u} : ListRep.{u, max u v, v, imax (u + 1) (u + 1) v, imax (u + 1) v} (List A) A :=
  .ofRec List.nil List.cons listRec

/-! ## Further pointwise instances

With the expected computation rules (`ListRec b s Nil = b` and
`ListRec b s (Cons h t) = s h t (ListRec b s t)`), a pointwise `ListRec` says
that `L` is the initial algebra of `X ↦ Unit ⊕ (A × X)`. So the pointwise
instances are exactly the alternative *representations* of a list — order and
multiplicity must survive. Collection types that quotient those away have no
instance: for `Multiset` the cons rule already forces `[a, b] = [b, a]` (via
`cons_swap`), and for `Finset`/`Set` it clashes with idempotence of `insert`.
That is why Mathlib's `Multiset.rec` carries an extra coherence hypothesis and
`Finset` has only a `Prop`-valued induction principle. -/

/-- `Array` is `List` in a different representation: the same order, but `Cons`
    rebuilds rather than sharing, so it is `O(n)` instead of `O(1)`. -/
instance instListRepArray {A : Type u} : ListRep.{u, max u v, v, imax (u + 1) (u + 1) v, imax (u + 1) v} (Array A) A :=
  .ofRec ⟨[]⟩ (fun a s => ⟨a :: s.toList⟩) fun {motive} base step s =>
    listRec (motive := fun l => motive ⟨l⟩) base (fun h t ih => step h ⟨t⟩ ih) s.toList

/-! ### Snoc-lists

A list built from the other end. This is the instructive pointwise instance:
`ListRep` peels elements off the *far* end of a `SnocList`, so `ListRec` is
emphatically **not** `SnocList.rec`. It is `listRec` transported across
`SnocList A ≅ List A`, which is what `ofList_toList` is for. -/

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

/-- `SnocList` is `ListRep` against its *own* grain: the recursion runs from the
    tail end, transported along `SnocList.ofList_toList`. -/
instance instListRepSnocList {A : Type u} : ListRep.{u, max u v, v, imax (u + 1) (u + 1) v, imax (u + 1) v} (SnocList A) A :=
  .ofRec .nil SnocList.cons fun {motive} base step s =>
    SnocList.ofList_toList s ▸
      listRec (motive := fun l => motive (SnocList.ofList l)) base
        (fun h t ih => step h (SnocList.ofList t) ih) s.toList

end ListLanguage
