import DeductiveVericoding.ListLanguage.Basic

open ListLanguage

/-
Here we have a collection of vericoding Problems in the List language defined in ListLanguage.lean.

This file holds only the *specifications*; the implementations that meet them live in
`Solutions.lean`.
-/

abbrev UnitProblem := Impl .unit .unit (fun _ => True) (fun _ out => out = ())

abbrev NilProblem := Impl .unit .list (fun _ => True) (fun _ out => out = [])

abbrev FstProblem := Impl (.pair .nat .nat) .nat (fun _ => True) (fun ⟨x, _⟩ out => out = x)

abbrev SndProblem := Impl (.pair .nat .nat) .nat (fun _ => True) (fun ⟨_, x⟩ out => out = x)

abbrev SwapProblem (s : Tpe) := Impl (.pair s s) (.pair s s) (fun _ => True) (fun ⟨y, x⟩ out => out = ⟨x, y⟩)

abbrev ConsProblem := Impl (.pair .nat .list) .list (fun _ => True) (fun ⟨x, xs⟩ out => out = x :: xs)

abbrev NumToListProblem := Impl .nat .list (fun _ => True) (fun x out => out = [x])

abbrev List123Problem := Impl .unit .list (fun _ => True) (fun _ out => out = [1,2,3])

abbrev AppendConstantProblem := Impl .list .list (fun _ => True) (fun inp out => out = inp.append [1])

abbrev AppendProblem := Impl (.pair .nat .list) .list (fun _ => True) (fun ⟨a, l⟩ out => out = l.append [a])

abbrev ReverseProblem := Impl .list .list (fun _ => True) (fun l out => out = l.reverse)

abbrev ConcatProblem := Impl (.pair .list .list) .list (fun _ => True) (fun ⟨l1, l2⟩ out => out = l2.append l1)

/- # HARDER PROBLEMS-/

abbrev SplitProblem := Impl .list (.pair .nat .list) (fun l => l ≠ []) (fun l ⟨x, xs⟩ => l = x :: xs)

abbrev AndProblem := Impl (.pair .bool .bool) .bool (fun _ => True) (fun inp out => out = Bool.and inp.1 inp.2)
