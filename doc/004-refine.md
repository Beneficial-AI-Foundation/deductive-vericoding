# Refinements

Please read Sebastian Graf's intro to monadic verication condition generation
* https://hackmd.io/@sg-fro/BJRlurP_xg

## Key ideas in `mvcgen`

1. Capturing imperative programs or programs with computational effects with monads, i.e. programs built up with statements `return` and `do let x <- ...; f(x)`)
2. The `mvcgen` tactic generates verification conditions for each post-condition by stripping away the `do` and `return` notations, calculating weakest preconditions, and tracking the preconditions using Hoare triples.
3. Using monad transformers to extend the underlying programming language one constructor at a time. And by writing specification lemmas that describe the behavior each constructor, the proofs will decompose nicely.

## Key ideas for refinement-based vericoding

1. Capturing computational effects with algebraic effects (less general than monad transformers but easier to describe) in some cases.
2. Generating verification conditions of a more general form via functors rather than Hoare triples, by thinking of functors as type refinement systems.
    * https://www.irif.fr/~mellies/papers/functors-are-type-refinement-systems.pdf
3. Extending the programming language just by concatenating the lists of constructors. The specification lemmas for each constructor lifts through this product. Each lemma tells gives logical validity for the decompositions/refinements that we are applying to the programming task.

## Example: Sorting algorithms

Just a sketch of an example. Suppose we want to synthesize an algorithm for sorting a list of numbers. 

One can try to apply an induction principle to the structure of the list:

1. For empty lists, do nothing because they are already sorted.

2. If the list is of the form `y :: xs`, then sort the tail `xs` and then insert `y` into the right position in the `sort(xs)`.

This is insertion sort!

Note that if I have a specification lemma corresponding to this induction principle, the lemma will generate two subtasks:

1. Sorting an empty list (and proving that the result is sorted)

2. Inserting `y` into a sorted list `sort(xs)` (and proving that the result is sorted)

But in the Hoare triple view of refinement, both tasks are combined into one verification condition, which is not very useful for parallelizing subtasks.