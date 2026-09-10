import DeductiveVericoding.ListLanguage.Basic

open ListLanguage

/-
Here we have a collection of vericoding Problems in the List language defined in ListLanguage.lean
-/

abbrev UnitProblem := Impl .unit .unit (fun _ => True) (fun _ out => out = ())

def UnitSolution : UnitProblem := {
  code := .lam fun _ => .unit
  correct _ _ := rfl
}

abbrev NilProblem := Impl .unit .list (fun _ => True) (fun _ out => out = [])

def NilSolution : NilProblem := {
  code := .lam fun _ => .nil
  correct _ _ := rfl
}

abbrev FstProblem := Impl (.pair .nat .nat) .nat (fun _ => True) (fun ⟨x, _⟩ out => out = x)

def FstSolution : FstProblem := {
  code := .lam fun k => .fst (.var k)
  correct _ _ := rfl
}

abbrev SndProblem := Impl (.pair .nat .nat) .nat (fun _ => True) (fun ⟨_, x⟩ out => out = x)

def SndSolution : SndProblem := {
  code := .lam fun k => .snd (.var k)
  correct _ _ := rfl
}

abbrev SwapProblem (s : Tpe) := Impl (.pair s s) (.pair s s) (fun _ => True) (fun ⟨y, x⟩ out => out = ⟨x, y⟩)

def SwapSolution (s : Tpe) : SwapProblem s := {
  code := .lam fun k => .mkPair (.snd (.var k)) (.fst (.var k))
  correct _ _ := rfl
}

abbrev ConsProblem := Impl (.pair .nat .list) .list (fun _ => True) (fun ⟨x, xs⟩ out => out = x :: xs)

def ConsSolution : ConsProblem := {
  code := .lam fun k => .cons (.fst (.var k)) (.snd (.var k))
  correct _ _ := rfl
}

abbrev NumToListProblem := Impl .nat .list (fun _ => True) (fun x out => out = [x])

def NumToListSolution : NumToListProblem := {
  code := .lam fun k => .cons (.var k) .nil
  correct _ _ := rfl
}

abbrev List123Problem := Impl .unit .list (fun _ => True) (fun _ out => out = [1,2,3])

def List123Solution : List123Problem := {
  code := .lam fun _ => .cons (.num 1) (.cons (.num 2) (.cons (.num 3) .nil))
  correct _ _ := rfl
}

abbrev AppendConstantProblem := Impl .list .list (fun _ => True) (fun inp out => out = inp.append [1])

def AppendConstantSolution : AppendConstantProblem := {
  code := .lam fun l => .app
    (.listRec (.lam fun _ => .cons (.num 1) .nil)
      (.lam fun p => .cons (.fst (.snd (.snd (.var p)))) (.fst (.snd (.var p)))))
    (.mkPair .unit (.var l))
  correct inp _ := by
    induction inp with
    | nil => rfl
    | cons a l ih =>
      simp [Trm.eval, Trm'.eval, Trm'.eval.go] at ⊢ ih
      congr
}

abbrev AppendProblem := Impl (.pair .nat .list) .list (fun _ => True) (fun ⟨a, l⟩ out => out = l.append [a])

def AppendSolution : AppendProblem := {
  code := .listRec (.lam fun k => .cons (.var k) .nil) (.lam fun p => .cons (.fst (.snd (.snd (.var p)))) (.fst (.snd (.var p))))
  correct inp _ := by
    obtain ⟨a, l⟩ := inp
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp [Trm.eval, Trm'.eval, Trm'.eval.go] at ⊢ ih
      congr
}

abbrev ReverseProblem := Impl .list .list (fun _ => True) (fun l out => out = l.reverse)

-- def ReverseSolution : ReverseProblem := {
--   code := .lam fun l => .app (.listRec (.lam fun _ => .nil) AppendSolution.code)
--     (.mkPair .unit (.var l))
--   correct inp _ := by
--     induction inp with
--     | nil => rfl
--     | cons a l ih =>
--       simp [Trm.eval, Trm'.eval, Trm'.eval.go] at ih ⊢
--       rw [ih]
--       exact AppendSolution.correct (a, l.reverse) trivial
-- }

abbrev ConcatProblem := Impl (.pair .list .list) .list (fun _ => True) (fun ⟨l1, l2⟩ out => out = l2.append l1)

def ConcatSolution : ConcatProblem := {
  code := .listRec (.lam fun k => (.var k)) (.lam fun p => .cons (.fst (.snd (.snd (.var p)))) (.fst (.snd (.var p))))
  correct inp _ := by
    obtain ⟨l1, l2⟩ := inp
    induction l2 with
    | nil => rfl
    | cons a l ih =>
      simp [Trm.eval, Trm'.eval, Trm'.eval.go] at ih ⊢
      rw [ih]
}

/- # HARDER PROBLEMS-/

abbrev SplitProblem := Impl .list (.pair .nat .list) (fun l => l ≠ []) (fun l ⟨x, xs⟩ => l = x :: xs)

def SplitSolution : SplitProblem := {
  code := .lam fun k => .app (.listRec (.lam fun _ => .mkPair (.num 0) .nil) (.lam fun p => .mkPair (.fst (.snd (.snd (.var p)))) (.snd (.snd (.snd (.var p)))))) (.mkPair .nil (.var k))
  correct inp pre := by
    induction inp with
    | nil => contradiction
    | cons a l ih => rfl
}

abbrev AndProblem := Impl (.pair .bool .bool) .bool (fun _ => True) (fun inp out => out = Bool.and inp.1 inp.2)
