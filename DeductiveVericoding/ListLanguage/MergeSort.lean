import DeductiveVericoding.ListLanguage.InsertionSort

open ListLanguage List

abbrev MergeProblem := Impl (.pair .list .list) .list (fun inp => Ordered inp.1 ∧ Ordered inp.2) (fun ⟨l1, l2⟩ out => Sorted (l1 ++ l2) out ∧ Perm (l1 ++ l2) out)

def MergeSolution : MergeProblem := by
  apply ListRecTactic (Recursor.Prod UnCons UnCons)
  · simp [Recursor.Prod, UnCons]
    aesop
    · exact Ordered_tail x xs a_1
    exact Ordered_tail x_1 xs_1 a_2
  · simp [Recursor.Prod, UnCons] --this is the base case
    apply CasesTactic (fun (inp : _ × _) => inp.1 = []) ?_ ?_ ?_ -- we know one of the two input lists is empty, so split cases on which is empty
    · apply SwapTactic
      apply ListRecTactic (Param Nat.zero_lt_one UnCons)
      · simp [Param, UnCons]
        intro l1 l2 h1 h2 h3 h4
        cases l2
        · contradiction
        simp [h1, Ordered]
        apply Ordered_tail _ _ h2
      · apply TrueTactic
        simp [Param, UnCons]
      · apply FalseTactic
        simp [Param, UnCons]
    · simp
      apply UseTactic (fun (inp : _ × _) => inp.2)
      · apply SndTactic
        apply IdentityTactic
        simp
      · simp
        intro a b _ _ h _
        simp_all only [true_or, nil_append, Perm.refl, and_true]
        exact (SortedSelf_iff _).2 h
    · apply UseTactic (fun (inp : _ × _) => inp.1)
      · apply FstTactic
        apply IdentityTactic
        simp
      · simp
        intro a b _ h _ _
        simp_all only [false_or, append_nil, Perm.refl, and_true]
        exact (SortedSelf_iff _).2 h
  · simp [Recursor.Prod, UnCons, dup] --step case
    refine CasesTactic (fun inp => Nat.ble inp.1.1 inp.1.2) ?_ ?_ ?_ -- merging x :: xs with y :: ys check if x ≤ y
    · apply LETactic
      · simp
        refine UseTactic (fun inp => (inp.1.1, inp.1.2)) ?_ ?_
        · Vpair
          · apply FstTactic
            apply FstTactic
            apply IdentityTactic
            simp
          · apply SndTactic
            apply FstTactic
            apply IdentityTactic
            simp
        · simp
    · simp
      refine UseTactic (fun inp => inp.1.1 :: inp.2.2.1) ?_ ?_
      · simp
        apply ConsTactic
        Vpair
        · apply FstTactic
          apply FstTactic
          apply IdentityTactic
          simp
        · apply FstTactic
          apply SndTactic
          apply SndTactic
          apply IdentityTactic
          simp
      · simp [Tpe.denote]
        intro a b l1 l2 l3 l4 res1 res2 h1 h2 h3 h4 h5 h6 hab
        
        simp [_root_.Sorted, Ordered, hab]
        sorry -- wrong :(
    · simp -- the case y < x
      refine UseTactic (fun inp => inp.1.2 :: inp.1.1 :: inp.2.2) ?_ ?_
      · simp
        apply ConsTactic
        Vpair
        · apply SndTactic
          apply FstTactic
          apply IdentityTactic
          simp
        · apply ConsTactic
          Vpair
          · apply FstTactic
            apply FstTactic
            apply IdentityTactic
            simp
          · apply SndTactic
            apply SndTactic
            apply IdentityTactic
            simp
      · simp [Tpe.denote]
        intro a b l1 l2 res ih1 ih2 hl1 hl2 hab
        sorry

def MergeSortSolution : SortingProblem := by
  apply ListRecTactic Halve
  · simp
  · simp [Halve]
    apply UseTactic (fun inp => inp)
    · apply IdentityTactic
      simp
    simp [SortedSelf_iff, Tpe.denote]
    intro inp h
    apply Nat.sub_eq_zero_iff_le.1 at h
    apply Nat.le_one_iff_eq_zero_or_eq_one.1 at h
    obtain h|h := h
    · simp at h
      rw [h]
      trivial
    apply List.length_eq_one_iff.1 at h
    obtain ⟨a, rfl⟩ := h
    trivial
  apply ElimUnitTactic
  simp [Halve, dup]
  apply RelaxPostTactic _ (fun (inp : _ × _) out => _root_.Sorted (inp.2.1 ++ inp.2.2) out)
  · apply RelaxPreTactic (fun (inp : _ × _) => Ordered inp.2.1 ∧ Ordered inp.2.2)
    · simp [_root_.Sorted]
      grind
    · sorry
  · intro inp h1 out h2
    refine (SortedPerm_iff _ _ _ ?_).1 h2
    exact List.Perm.append h1.1.2.symm h1.2.2.symm
