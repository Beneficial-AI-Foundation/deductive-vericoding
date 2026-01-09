# Russell (Rocq)

Hardest part of deductive vericoding in Lean, is getting Lean to "expose the program but hide the proofs".

For example, if we have the predicate subtype `{f : (x : Bool) -> Prog Nat | \forall x : Nat, f(x) > 0 }` where `Prog Nat`  is the monad of programs that output natural numbers, then generating an element of this predicate subtype should give us a program `f` which we can print and use elsewhere, but the proof that the output is always positive should remain hidden.

This problem for Rocq is discussed in [the Russell paper](https://sozeau.gitlabpages.inria.fr/www/research/publications/Subset_Coercions_in_Coq.pdf) where Sozeau says,
> To formalise this idea in Coq, we simply weaken the type system so that it doesn’t require the terms to contain the proof components for objects of subset types. This permits to have a simple language for code while retaining the richness of Coq’s specification language.

I just need to check Lean's core language was also weakened to do this for [subtypes/subsets](https://lean-lang.org/doc/reference/latest/Basic-Types/Subtypes/). Of course, there is a way to accomplish this without weakening the core language but with a lot more inconvenience for programming and formal verification. See the Russell paper for more details. 

With predicate subtypes, pre/post-conditions P and Q can be written as `f : { x : Bool | P(x) } -> Prog { y : Nat | Q(y) }`. I'm not sure yet, but this way of writting the conditions may not make it easy to do `mvcgen` or future tactics for deductive vericoding. 