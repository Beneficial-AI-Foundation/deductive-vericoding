# Tactics-driven vericoding

## Domain specific logic

Mixed radix numbers (MRNs). Given by list of pairs of integers. It is a representation of an integer as dot product of a vector of coefficients with a vector of bases. For example, `256 = 2*100 + 5*10 + 6*1`. The bases do not need to be powers of some integer.

```
p : List (Int × Int)
```

The `eval` function gives semantics to these MRNs. It recursively computes the sum of the product of each pair.

```
def eval (p : List (Int × Int)) : Int :=
  List.foldr (fun t acc => t.1 * t.2 + acc) 0 p
```

## Refinements

Multiplication of two MRNs.

```
def mul (p q : List (Int × Int)) : List (Int × Int) :=
  List.flatMap (fun t =>
    List.map (fun t' => (t.1 * t'.1, t.2 * t'.2))
    q) p
```

Refinement using `mul`

```
@[simp] lemma eval_mul (p q : List (Int × Int)) :
  eval (mul p q) = eval p * eval q := by
  induction p with
  | nil => simp [mul, eval_nil]
  | cons t ts ih =>
    unfold mul at ih
    simp [mul, eval_cons, ih]
    ring
```

Refinement using `app`

```
@[simp] lemma eval_app (p q : List (Int × Int)) :
  eval (p ++ q) = eval p + eval q := by
  induction p with
  | nil =>
    simp [eval_nil, List.append]
  | cons a as ih =>
    simp [eval_cons, ih]
    ring
```

## Tactics

Suppose we want to derive base-10 arithmetic to compute `a * b + c`. In the following example, the goal is to find an MRN whose value is an arithmetic combination of the values of three input MRNs `a, b, c`.

```
example (a0 a1 b0 b1 c0 c1 : Int) :
  ∃ abc, eval abc = eval [(10, a1), (1, a0)] * eval [(10, b1), (1, b0)] + eval [(10, c1), (1, c0)] 
```

We apply the `eval_mul` refinement

```
example (a0 a1 b0 b1 c0 c1 : Int) :
  ∃ abc, eval abc = eval [(10, a1), (1, a0)] * eval [(10, b1), (1, b0)] + eval [(10, c1), (1, c0)] := by
  rw [←eval_mul]
```

The goal becomes

```
a0 a1 b0 b1 c0 c1 : ℤ
⊢ ∃ abc, eval abc = eval (mul [(10, a1), (1, a0)] [(10, b1), (1, b0)]) + eval [(10, c1), (1, c0)]
```

We then apply the `eval_app` refinement

```
example (a0 a1 b0 b1 c0 c1 : Int) :
  ∃ abc, eval abc = eval [(10, a1), (1, a0)] * eval [(10, b1), (1, b0)] + eval [(10, c1), (1, c0)] := by
  rw [←eval_mul]
  rw [←eval_app]
```

The goal becomes

```
a0 a1 b0 b1 c0 c1 : ℤ
⊢ ∃ abc, eval abc = eval (mul [(10, a1), (1, a0)] [(10, b1), (1, b0)] ++ [(10, c1), (1, c0)])
```

Now, we can use the `grind` tactic to finish the proof. The tactic recognizes similar patterns on both sides of the equality and solves for the `abc` metavariable by unification. 

```
example (a0 a1 b0 b1 c0 c1 : Int) :
  ∃ abc, eval abc = eval [(10, a1), (1, a0)] * eval [(10, b1), (1, b0)] + eval [(10, c1), (1, c0)] := by
  rw [←eval_mul]
  rw [←eval_app]
  grind
```

Unfortunately, I can’t extract the code because it is in proof-irrelevant `Prop`. If I use proof-relevant `PSigma`, the `grind` tactic doesn’t work.
