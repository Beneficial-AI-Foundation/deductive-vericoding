# Composing effects

Tutorial on algebraic effect 
* https://arxiv.org/pdf/1807.05923

Jason Gross asked about algebraic effects in Lean.
* https://leanprover-community.github.io/archive/stream/270676-lean4/topic/algebraic.20effects.20and.20handlers.3F.html

2021: Effects are too slow.
2025: There are fast implementations now.
* https://xnning.github.io/papers/haskell-evidently.pdf

Composing effects
* https://discuss.ocaml.org/t/composition-and-algebraic-effects/15468/2

Example of an effect-oriented programming language 
* https://flix.dev/
* "Why Effects? Effect systems represent the next major evolution in statically typed programming languages. By explicitly modeling side effects, effect-oriented programming enforces modularity and helps program reasoning. User-defined effects and handlers allow programmers to implement their own control structures."

Representing domain specific languages (e.g. languages that we want to code in) in Lean is an important aspect of this project. We can use monads to define these languages and monad transformers to "compose" the monads. Or we can use algebraic effects and higher order effects. The following talk on the history of programming languages, monads and effects is phenomenal!
* https://dl.acm.org/doi/10.1145/3609026.3615581

Higher order effects 
* https://arxiv.org/abs/2302.01415