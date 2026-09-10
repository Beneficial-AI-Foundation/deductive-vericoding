import DeductiveVericoding.ListLanguage.Problems
import DeductiveVericoding.ListLanguage.Tactics
import DeductiveVericoding.ListLanguage.VericodeTactic

/-! # Manual solutions

Every combinator now takes the goal's postcondition as a parameter and asks for a proof `h`
that the value it builds satisfies it. So a step is `refine XTactic … ?_ … (fun _ _ => rfl)`:
the trailing `rfl` discharges `h` and, in doing so, fixes the `target` metavariables from the
goal — the job the conclusion's unification used to do under a bare `apply`. -/

open ListLanguage Tpe

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
  · simp
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
  simp
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
  simp
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
  · Vpair
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
  simp
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
  · simp
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
