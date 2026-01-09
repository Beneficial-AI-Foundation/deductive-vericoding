# Refinement Calculus

Refinement calculus (Morgan, 1988) predates a lot of the recent stuff like WPGen. Early versions of the calculus were extremely simple and specialized. Recent versions like "Functors are Type Refinement Systems" carry out the original vision to its full generality.

https://www.irif.fr/~mellies/papers/functors-are-type-refinement-systems.pdf

## The Specification Statement

The key construct is the **specification statement**:

```
w : [P, Q]
```

Read as: "Modify variables in frame w to establish postcondition Q, assuming 
precondition P holds. May assume P; must establish Q."

This is NOT an assertion—it's an *executable* (though abstract) program piece.

### Examples

```
x : [true, x > 0]           -- Set x to something positive
x : [x = X, x = X + 1]      -- Increment x (X is initial value)  
x,y : [true, x² + y² = 25]  -- Set x,y to any point on circle of radius 5
```

---

## The Refinement Relation

**S ⊑ T** means "T refines S" or "T is at least as good as S"

Formally (via weakest preconditions):
```
S ⊑ T  ⟺  ∀Q. WP(S, Q) ⇒ WP(T, Q)
```

Intuition: T terminates at least as often as S, and whenever T terminates,
it satisfies at least what S would satisfy.

### Refinement is a Partial Order
- Reflexive: S ⊑ S
- Transitive: S ⊑ T and T ⊑ U implies S ⊑ U
- Antisymmetric (up to equivalence): S ⊑ T and T ⊑ S implies S ≡ T

### Key Insight
Programs form a **lattice** under refinement:
- ⊤ (top) = "abort" (miracle—establishes anything, including false)
- ⊥ (bottom) = "magic" (never terminates, refines everything)

Executable programs live in a sublattice between these extremes.

---

## Core Refinement Laws

### 1. Strengthen Postcondition
```
w : [P, Q]  ⊑  w : [P, Q']     if Q' ⇒ Q
```
Making a stronger promise is a valid refinement.

### 2. Weaken Precondition
```
w : [P, Q]  ⊑  w : [P', Q]     if P ⇒ P'
```
Assuming less is a valid refinement.

### 3. Assignment Introduction
```
x : [P, Q]  ⊑  x := E          if P ⇒ Q[x ↦ E]
```
Replace spec with assignment if it establishes the postcondition.

### 4. Sequential Composition
```
w : [P, Q]  ⊑  w : [P, R] ; w : [R, Q]
```
Break a spec into sequential parts via intermediate condition R.

### 5. Alternation (If Introduction)
```
w : [P, Q]  ⊑  if B then w:[P∧B, Q] else w:[P∧¬B, Q]
```
Introduce a conditional, strengthening preconditions on each branch.

### 6. Iteration (While Introduction)
```
w : [P, Q]  ⊑  while B do w:[P∧B, P] end      if P∧¬B ⇒ Q
```
Introduce a loop with invariant P, if exiting establishes Q.

---

## Complete Example: Integer Square Root

**Specification:**
```
r : [n ≥ 0, r² ≤ n < (r+1)²]
```
"Given non-negative n, find r such that r is the integer square root of n."

### Step 1: Introduce Loop Structure
We'll compute r by counting up. Invariant: r² ≤ n

```
r : [n ≥ 0, r² ≤ n < (r+1)²]
⊑  { Sequential composition with intermediate condition r² ≤ n }
r : [n ≥ 0, r² ≤ n] ;
r : [r² ≤ n, r² ≤ n < (r+1)²]
```

### Step 2: Refine First Part to Assignment
```
r : [n ≥ 0, r² ≤ n]
⊑  { 0² = 0 ≤ n when n ≥ 0 }
r := 0
```

### Step 3: Refine Second Part to Loop
```
r : [r² ≤ n, r² ≤ n < (r+1)²]
⊑  { Loop with invariant r² ≤ n, guard (r+1)² ≤ n }
while (r+1)² ≤ n do
    r : [r² ≤ n ∧ (r+1)² ≤ n, r² ≤ n]
end
```
Check: r² ≤ n ∧ ¬((r+1)² ≤ n) ⟹ r² ≤ n < (r+1)²  ✓

### Step 4: Refine Loop Body
```
r : [r² ≤ n ∧ (r+1)² ≤ n, r² ≤ n]
⊑  { Since (r+1)² ≤ n, setting r := r+1 maintains r² ≤ n }
r := r + 1
```

### Final Program
```
r := 0;
while (r+1)² ≤ n do
    r := r + 1
end
```

**Correctness is guaranteed by construction!** Each step was a valid refinement.

---

## Refinement vs. Hoare Logic vs. WP

| Aspect | Hoare Logic | WP Calculus | Refinement Calculus |
|--------|-------------|-------------|---------------------|
| Specs & code | Separate | Separate | Unified |
| Direction | Forward/Backward | Backward | Stepwise (either) |
| Loops | External invariant | External invariant | Derived via laws |
| Result | Proof of correctness | Verification condition | Correct-by-construction code |
| Compositionality | Via proof rules | Via WP transformer | Via algebraic laws |

---

## The Monotonicity Principle

All program constructors are **monotonic** with respect to refinement:

```
If S ⊑ S' then:
    S ; T  ⊑  S' ; T           (left sequential)
    T ; S  ⊑  T ; S'           (right sequential)
    if B then S else T  ⊑  if B then S' else T
    while B do S  ⊑  while B do S'
```

This is crucial: you can refine any subprogram independently, and the whole 
program remains a valid refinement of the original.

---

## Nondeterminism and Demonic/Angelic Choice

Refinement calculus elegantly handles nondeterminism:

**Demonic choice (⊓):** Environment chooses (worst case for us)
```
S ⊓ T    -- Must satisfy spec no matter which branch is taken
```

**Angelic choice (⊔):** We choose (best case for us)  
```
S ⊔ T    -- May pick whichever branch helps satisfy spec
```

Specifications like `x : [true, x > 0]` are angelically nondeterministic:
we get to pick any positive value.

Refinement *resolves* angelic choice:
```
x : [true, x > 0]  ⊑  x := 1    -- One valid refinement
x : [true, x > 0]  ⊑  x := 42   -- Another valid refinement
```

---

## Data Refinement

Refinement extends to **data representation**:

```
Abstract:  stack with operations push, pop, top
Concrete:  array + index

Coupling invariant: abstract stack = array[0..index-1]
```

## Summary
Data refinement laws let you prove that concrete operations refine abstract 
ones, enabling verified transformation of data structures.


Refinement calculi represent one of the most elegant unifications in program verification. The core insight is radical: specifications and programs are the same kind of thing, related by a partial order called refinement.

### The Central Idea
Instead of having:

- A specification language (pre/postconditions)
- A programming language (code)
- A separate verification method (Hoare logic, WP, etc.)

Refinement calculus gives you:

- One language containing both specifications and programs
- One relation (refinement ⊑) connecting them
- Algebraic laws for transforming specifications into programs

The development process becomes: start with a specification, apply refinement laws, end with executable code—and correctness is guaranteed by construction.

## Why Refinement Calculus Matters

1. It Unifies Everything

   The relationship to your previous question:

    - WP is the semantic foundation: Refinement is defined via WP: S ⊑ T ⟺ ∀Q. wp(S,Q) ⇒ wp(T,Q)
    - Symbolic execution computes refinement witnesses: When you symbolically execute and find the input-output relation, you're discovering what specifications a program refines
    - Hoare triples are refinement claims: {P} S {Q} is equivalent to [P,Q] ⊑ S (the program refines the spec)

2. Correct by Construction

    Traditional verification:
    - Write code → Write spec → Try to prove they match → Debug both
    
    Refinement approach:
    - Write spec → Apply refinement laws → Get correct code automatically
    
    Each refinement step is small and checkable. The final program is correct by construction—not verified after the fact.

3. The Key Players

    | Calculus | Originator | Key Feature |
    |---|---|---|
    | Morgan's Refinement Calculus| Carroll Morgan | Emphasis on specification statements, practical methodology|
    | Back's Refinement Calculus | Ralph-Johan Back | More algebraic, action systems, concurrency| 
    | B-Method | Jean-Raymond Abrial | Industrial tool support, used in railway systems |
    | Z + Refinement | Oxford PRG | Combines Z specifications with refinement |
    
4. The Deep Connection to Lattice Theory

    Programs under refinement form a complete lattice:
    ```
            ⊤ (abort/miracle)
        /|\
        / | \
    more refined programs
        \ | /
        \|/
            ⊥ (magic/non-termination)
    ```

    - Moving down = refining = becoming more deterministic and implementable
    - Specification statements live near the top (highly nondeterministic)
    - Executable code lives lower (deterministic)
    - magic (bottom) refines everything but isn't implementable

    This lattice structure gives you:

    - Meets (⊓): demonic choice (must satisfy both)
    - Joins (⊔): angelic choice (may satisfy either)
    - Fixed points: define loops and recursion

### A Taste of the Algebra
The laws form a genuine algebra. For example:
```
(S ⊓ T) ; U  =  (S ; U) ⊓ (T ; U)     -- demonic choice distributes left

S ; (T ⊔ U)  =  (S ; T) ⊔ (S ; U)     -- angelic choice distributes right

skip ; S  =  S  =  S ; skip            -- skip is identity

abort ; S  =  abort                    -- abort is left zero
```

You can calculate with programs the way you calculate with numbers.

### Connecting Back to Your Original Question

| Framework | Symbolic Exec | WP | Refinement | 
|---|---|---|---|
| Direction | Forward | Backward | Any | 
| Primary use | Bug finding | Verification | Derivation | 
| Handles nondeterminism | Poorly | Well | Natively | 
| Loop treatment | Unroll or summarize | Requires invariant | Derive invariant via laws |
| Output | Test cases / counterexamples | Verification conditions | Correct program |

Refinement calculus is the most general: it explains why WP and symbolic execution work, unifies them, and extends them to program derivation.
