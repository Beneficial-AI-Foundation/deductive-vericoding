# Symbolic Evaluators vs Weakest Preconditions

What is the difference? Are they special cases of a more general concept?

## Example 1: Simple Assignment

```c
x := x + 1
```

**Goal:** Prove that if some precondition holds, then `x > 0` after execution.

### Symbolic Execution (Forward)
```
Initial state:  x = X  (X is a symbolic value)
Execute x := x + 1
Final state:    x = X + 1

To satisfy postcondition x > 0:
    X + 1 > 0
    X > -1

∴ Precondition discovered: x > -1
```

### Weakest Precondition (Backward)
```
Postcondition: x > 0
WP(x := x + 1, x > 0) = (x > 0)[x ↦ x+1]    // substitute x+1 for x
                      = (x + 1 > 0)
                      = x > -1

∴ Precondition: x > -1
```

**Same answer, different direction!**

---

## Example 2: Conditional (Path Explosion vs Logical Combination)

```c
if (x > 0) then
    y := x
else
    y := -x
```

**Goal:** Prove postcondition `y ≥ 0`

### Symbolic Execution (Forward)
```
Initial: x = X, y = Y (symbolic)

Path 1: X > 0
    Execute y := x
    Final: y = X
    Path condition: X > 0
    Postcondition check: X ≥ 0  ✓ (implied by path condition)

Path 2: X ≤ 0  
    Execute y := -x
    Final: y = -X
    Path condition: X ≤ 0
    Postcondition check: -X ≥ 0  ✓ (implied by path condition)

Both paths satisfy postcondition → Valid for all inputs
```

### Weakest Precondition (Backward)
```
WP(if b then S₁ else S₂, Q) = (b → WP(S₁,Q)) ∧ (¬b → WP(S₂,Q))

WP(if x>0 then y:=x else y:=-x, y≥0)
    = (x > 0 → WP(y:=x, y≥0)) ∧ (x ≤ 0 → WP(y:=-x, y≥0))
    = (x > 0 → x ≥ 0) ∧ (x ≤ 0 → -x ≥ 0)
    = (x > 0 → x ≥ 0) ∧ (x ≤ 0 → x ≤ 0)
    = true ∧ true
    = true

∴ Precondition is "true" — works for all inputs
```

**Key difference:** Symbolic execution enumerated 2 paths; WP produced one formula.

---

## Example 3: Sequential Composition

```c
x := x + 1;
y := x * 2
```

**Goal:** Prove postcondition `y > 0`

### Symbolic Execution (Forward)
```
Initial: x = X
After x := x + 1:    x = X + 1
After y := x * 2:    y = (X + 1) * 2 = 2X + 2

For y > 0:  2X + 2 > 0  →  X > -1

∴ Precondition: x > -1
```

### Weakest Precondition (Backward)
```
WP(S₁; S₂, Q) = WP(S₁, WP(S₂, Q))

WP(y := x*2, y > 0) = x*2 > 0 = x > 0

WP(x := x+1, x > 0) = x+1 > 0 = x > -1

∴ Precondition: x > -1
```

---

## Example 4: Loops (Where They Diverge Most)

```c
while (x > 0) do
    x := x - 1
```

**Goal:** Prove postcondition `x ≤ 0`

### Symbolic Execution Approach
```
Problem: Potentially infinite paths!

Iteration 0: X ≤ 0 → exit immediately, final x = X
Iteration 1: X > 0, X-1 ≤ 0 → final x = X-1  (i.e., X = 1)
Iteration 2: X > 0, X-1 > 0, X-2 ≤ 0 → final x = X-2  (i.e., X = 2)
...

Options:
  • Bounded unrolling (incomplete)
  • Require loop invariant (reduces to WP-style reasoning)
  • Use loop summarization heuristics
```

### Weakest Precondition Approach
```
WP for loops requires a loop invariant I:

WP(while b do S, Q) requires finding I such that:
  1. P → I                    (invariant established)
  2. {I ∧ b} S {I}            (invariant preserved)
  3. I ∧ ¬b → Q               (invariant implies postcondition)

For our example, let I = true:
  1. true → true              ✓
  2. {true ∧ x>0} x:=x-1 {true}  →  WP(x:=x-1, true) = true  ✓
  3. true ∧ x≤0 → x≤0         ✓

∴ Precondition: true (works for all inputs)
```

---

## Summary: Key Differences

| Aspect | Symbolic Execution | Weakest Precondition |
|--------|-------------------|---------------------|
| **Direction** | Forward (inputs → outputs) | Backward (outputs → inputs) |
| **Paths** | Explicitly enumerates paths | Combines paths in single formula |
| **Scalability** | Path explosion on branches | Formula size explosion possible |
| **Loops** | Unrolling or invariants | Requires invariants |
| **Use case** | Bug finding, test generation | Full correctness proofs |
| **Duality** | Computes SP (strongest post) | Computes WP (weakest pre) |

## The Unifying Framework

Both compute aspects of the **relational semantics** ⟦S⟧ ⊆ State × State:

- **SP(P, S)** = { σ' | ∃σ. σ ∈ P ∧ (σ,σ') ∈ ⟦S⟧ }  (image of P under S)
- **WP(S, Q)** = { σ | ∀σ'. (σ,σ') ∈ ⟦S⟧ → σ' ∈ Q }  (preimage of Q under S)

They're Galois connected:  SP(P,S) ⊆ Q  ⟺  P ⊆ WP(S,Q)

## A More General Framework?

Yes—Abstract Interpretation subsumes both. You can view:

- Symbolic execution as forward abstract interpretation over a domain of symbolic constraints
- WP as backward abstract interpretation over a domain of logical predicates

Both are also subsumed by relational program logics and refinement calculi, where you reason directly about the input-output relation without committing to a direction.
