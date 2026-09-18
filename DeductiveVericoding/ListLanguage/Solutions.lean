import DeductiveVericoding.ListLanguage.Problems
import DeductiveVericoding.ListLanguage.Tactics
import DeductiveVericoding.ListLanguage.VericodeTactic

open ListLanguage Tpe

/-!
# Solutions

Implementations for the specifications in `Problems.lean`. Each `XXXSolution` is a hand-written
term together with its correctness proof; each `XXXSolution'` is the same problem derived by
`apply`ing the combinators from `Tactics.lean` instead.
-/

/-! # Hand-written solutions -/

def UnitSolution : UnitProblem := {
  code := .lam fun _ => .unit
  correct _ _ := rfl
}

def NilSolution : NilProblem := {
  code := .lam fun _ => .nil
  correct _ _ := rfl
}

def FstSolution : FstProblem := {
  code := .lam fun k => .fst (.var k)
  correct _ _ := rfl
}

def SndSolution : SndProblem := {
  code := .lam fun k => .snd (.var k)
  correct _ _ := rfl
}

def SwapSolution (s : Tpe) : SwapProblem s := {
  code := .lam fun k => .mkPair (.snd (.var k)) (.fst (.var k))
  correct _ _ := rfl
}

def ConsSolution : ConsProblem := {
  code := .lam fun k => .cons (.fst (.var k)) (.snd (.var k))
  correct _ _ := rfl
}

def NumToListSolution : NumToListProblem := {
  code := .lam fun k => .cons (.var k) .nil
  correct _ _ := rfl
}

def List123Solution : List123Problem := {
  code := .lam fun _ => .cons (.num 1) (.cons (.num 2) (.cons (.num 3) .nil))
  correct _ _ := rfl
}

def AppendConstantSolution : AppendConstantProblem := {
  code := .lam fun l => .app
    (.listRec (.lam fun _ => .cons (.num 1) .nil)
      (.lam fun p => .cons (.fst (.snd (.snd (.var p)))) (.fst (.snd (.var p)))))
    (.mkPair .unit (.var l))
  correct inp _ := by
    induction inp with
    | nil => rfl
    | cons a l ih =>
      simp [Trm.eval, Trm'.eval] at ⊢ ih
      congr
}

def AppendSolution : AppendProblem := {
  code := .listRec (.lam fun k => .cons (.var k) .nil) (.lam fun p => .cons (.fst (.snd (.snd (.var p)))) (.fst (.snd (.var p))))
  correct inp _ := by
    obtain ⟨a, l⟩ := inp
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp [Trm.eval, Trm'.eval] at ⊢ ih
      congr
}

-- def ReverseSolution : ReverseProblem := {
--   code := .lam fun l => .app (.listRec (.lam fun _ => .nil) AppendSolution.code)
--     (.mkPair .unit (.var l))
--   correct inp _ := by
--     induction inp with
--     | nil => rfl
--     | cons a l ih =>
--       simp [Trm.eval, Trm'.eval] at ih ⊢
--       rw [ih]
--       exact AppendSolution.correct (a, l.reverse) trivial
-- }

def ConcatSolution : ConcatProblem := {
  code := .listRec (.lam fun k => (.var k)) (.lam fun p => .cons (.fst (.snd (.snd (.var p)))) (.fst (.snd (.var p))))
  correct inp _ := by
    obtain ⟨l1, l2⟩ := inp
    induction l2 with
    | nil => rfl
    | cons a l ih =>
      simp [Trm.eval, Trm'.eval] at ih ⊢
      rw [ih]
}

def IsEmptySolution : IsEmptyProblem := {
  code := .lam fun l => .app (.listRec (.lam fun k => .true) (.lam fun p => .false)) (.mkPair .unit (.var l))
  correct inp _ := by
    obtain ⟨_, _⟩ := inp <;> simp [Trm'.eval, Trm.eval]
}

/- # HARDER PROBLEMS-/

def SplitSolution : SplitProblem := {
  code := .lam fun k => .app (.listRec (.lam fun _ => .mkPair (.num 0) .nil) (.lam fun p => .mkPair (.fst (.snd (.snd (.var p)))) (.snd (.snd (.snd (.var p)))))) (.mkPair .nil (.var k))
  correct inp pre := by
    induction inp with
    | nil => contradiction
    | cons a l ih => rfl
}

/-! # Derivations via the vericoding combinators

Every combinator now takes the goal's postcondition as a parameter and asks for a proof `h`
that the value it builds satisfies it. So a step is `refine XTactic … ?_ … (fun _ _ => rfl)`:
the trailing `rfl` discharges `h` and, in doing so, fixes the `target` metavariables from the
goal — the job the conclusion's unification used to do under a bare `apply`. -/

def UnitSolution' : UnitProblem := by
  exact UnitTactic (fun _ _ => rfl)

#eval ListLanguage.Trm.pretty UnitSolution'.code

def NilSolution' : NilProblem := by
  exact NilTactic (fun _ _ => rfl)

#eval ListLanguage.Trm.pretty NilSolution'.code

def FstSolution' : FstProblem := by
  apply FstTactic
  apply IdentityTactic
  simp [Tpe.denote]

#eval ListLanguage.Trm.pretty FstSolution'.code

def SndSolution' : SndProblem := by
  apply SndTactic
  apply IdentityTactic
  simp [Tpe.denote]

#eval ListLanguage.Trm.pretty SndSolution'.code

def SwapSolution' (s : Tpe) : SwapProblem s := by
  unfold SwapProblem
  Vpair
  · apply SndTactic
    apply IdentityTactic
    simp
  · apply FstTactic
    apply IdentityTactic
    simp

#eval ListLanguage.Trm.pretty (SwapSolution' .nat).code

def ConsSolution' : ConsProblem := by
  apply ConsTactic
  Vpair
  · apply FstTactic
    apply IdentityTactic
    simp [Tpe.denote]
  · apply SndTactic
    apply IdentityTactic
    simp [Tpe.denote]

#eval ListLanguage.Trm.pretty ConsSolution'.code

def NumToListSolution' : NumToListProblem := by
  apply ConsTactic
  Vpair
  · apply IdentityTactic
    simp
  · apply NilTactic
    simp

#eval ListLanguage.Trm.pretty NumToListSolution'.code

def List123Solution' : List123Problem := by
  apply ConsTactic
  Vpair
  · apply NumTactic 1
    simp
  · apply ConsTactic
    Vpair
    · apply NumTactic 2
      simp
    · apply ConsTactic
      Vpair
      · apply NumTactic 3
        simp
      · apply NilTactic
        simp

#eval ListLanguage.Trm.pretty List123Solution'.code

def AppendConstantSolution' : AppendConstantProblem := by
  apply ListRecTactic'
  · simp
  · apply ConsTactic
    simp [Tpe.denote]
    Vpair
    · apply NumTactic 1
      simp
    · apply NilTactic
      simp
  · simp [Tpe.denote]
    pushpre
    apply ConsTactic
    Vpair
    · apply FstTactic
      apply SndTactic
      apply IdentityTactic
      simp
    · apply FstTactic
      apply IdentityTactic
      simp

#eval ListLanguage.Trm.pretty AppendConstantSolution'.code

def AppendSolution' : AppendProblem := by
  apply ListRecTactic
  · simp
  · apply ConsTactic
    simp
    Vpair
    · apply IdentityTactic
      simp
    apply NilTactic
    simp
  simp [Tpe.denote]
  pushpre
  apply ConsTactic
  Vpair
  · apply FstTactic
    apply SndTactic
    apply SndTactic
    apply IdentityTactic
    simp
  · apply FstTactic
    apply SndTactic
    apply IdentityTactic
    simp

#eval ListLanguage.Trm.pretty AppendSolution'.code

def ConcatSolution' : ConcatProblem := by
  apply ListRecTactic
  · simp
  · apply IdentityTactic
    simp
  simp [Tpe.denote]
  pushpre
  apply ConsTactic
  Vpair
  · apply FstTactic
    apply SndTactic
    apply SndTactic
    apply IdentityTactic
    simp
  · apply FstTactic
    apply SndTactic
    apply IdentityTactic
    simp

#eval ListLanguage.Trm.pretty ConcatSolution'.code

def SplitSolution' : SplitProblem := by
  apply ListRecTactic''
  · apply ContradictionTactic
    simp
  · simp [Tpe.denote]
    Vpair
    · apply FstTactic
      apply IdentityTactic
      simp
    · apply SndTactic
      apply IdentityTactic
      simp

def ReverseSolution' : ReverseProblem := by
  apply ListRecTactic'
  · simp
  · apply NilTactic
    simp
  simp [Tpe.denote]
  pushpre
  apply RelaxPreTactic (fun _ => True)
  · simp
  apply SwapTactic
  apply ListRecTactic
  · simp
  · apply ConsTactic
    simp
    Vpair
    · apply FstTactic
      apply IdentityTactic
      simp
    · apply NilTactic
      simp
  · simp [Tpe.denote]
    pushpre
    apply ConsTactic
    Vpair
    · apply FstTactic
      apply SndTactic
      apply SndTactic
      apply IdentityTactic
      simp
    · apply FstTactic
      apply SndTactic
      apply IdentityTactic
      simp

/-! # `vericode` smoke tests currently broken

The same problems, solved automatically by the `vericode` search over the `VericodeL` rule
set — no manual guidance. `ReverseSolution''` in particular exercises the full pipeline:
`listRec` → `pushpre` → `appList` (apply an append helper to the recursive result) → `introTac`
→ nested `listRec`. -/

-- def UnitSolution'' : UnitProblem := by vericode
-- def NilSolution'' : NilProblem := by vericode
-- def ConsSolution'' : ConsProblem := by vericode
-- def NumToListSolution'' : NumToListProblem := by vericode
-- def List123Solution'' : List123Problem := by vericode
-- def AppendConstantSolution'' : AppendConstantProblem := by vericode
-- def AppendSolution'' : AppendProblem := by vericode
-- def ReverseSolution'' : ReverseProblem := by vericode
-- def ConcatSolution'' : ConcatProblem := by vericode

-- #eval ListLanguage.Trm.pretty ReverseSolution''.code
