import DeductiveVericoding.ListLanguage.Basic

/- Here we provide a list of splits -/

open ListLanguage

def helper_prod {s t : Type} (x : s) : t → s × t := by exact fun a ↦ (x, a)

def Param {s u t : Tpe} {d : Nat} (hd : d > 0) (R : Recursor s u d) : Recursor (t ×L s) u d := {
  split x := by
    refine ((R.split x.2).1, dup.map ?_ (R.split x.2).2)
    exact fun y => (x.1, y)
  unsplit y := by
    refine (?_, R.unsplit (y.1, dup.map ?_ y.2))
    · refine ((dup.toList y.2).head (List.ne_nil_of_length_pos ?_)).fst
      rwa [dup.toList_length y.2]
    exact fun x ↦ x.2
  depth x := R.depth x.2
  unsplit_split := by
    simp [← dup.map_toList]
    intro a b hb
    have : ((fun (x : (t ×L s).denote) ↦ x.snd) ∘ fun y ↦ (a, y)) = id := rfl
    simp [this]
    exact R.unsplit_split b hb
  descending x h := by
    simp only [← dup.map_toList, List.map_map]
    exact R.descending _ h
}

def UnCons : Recursor .list .nat 1 := {
  split l := match l with
    | [] => ((0 : Nat), [])
    | x :: xs => (x, xs)
  unsplit y := y.1 :: y.2
  depth l := l.length
  unsplit_split l := by grind
  descending l := by grind
}

@[simp]
theorem UnCons.depth_eq_zero_iff (l : List Nat) : UnCons.depth l = 0 ↔ [] = l := by
  simp [UnCons, List.length_eq_zero_iff]

@[simp]
def leading_part : Nat → List Nat → List Nat
  | 0, _ => []
  | _, [] => []
  | n + 1, x :: xs => x :: leading_part n xs

@[simp]
def trailing_part : Nat → List Nat → List Nat
  | 0, l => l
  | _, [] => []
  | n + 1, _ :: xs => trailing_part n xs

@[simp]
theorem leading_length (l : List Nat) (n : Nat) :
    (leading_part n l).length = min n l.length := by
  revert l
  induction n
  · simp [leading_part]
  · intro l
    induction l
    · simp [leading_part]
    · expose_names
      simp [leading_part]
      exact h tail

@[simp]
theorem trailing_length (l : List Nat) (n : Nat) :
    (trailing_part n l).length = l.length - n := by
  revert l
  induction n
  · simp
  · intro l
    induction l
    · simp
    · expose_names
      simp
      exact h tail

@[simp]
theorem leading_append_trailing (l : List Nat) (n : Nat) :
    leading_part n l ++ trailing_part n l = l := by
  revert l
  induction n
  · simp [leading_part, trailing_part]
  · intro l
    induction l
    · simp [leading_part, trailing_part]
    · expose_names
      simp [leading_part, trailing_part]
      exact h tail

def Halve : Recursor .list .unit 2 := {
  split l := ((), (leading_part (l.length/2) l, trailing_part (l.length/2) l))
  unsplit y := y.2.1 ++ y.2.2
  depth l := l.length - 1
  unsplit_split x h := leading_append_trailing x _
  descending l h := by
    simp; grind
}
