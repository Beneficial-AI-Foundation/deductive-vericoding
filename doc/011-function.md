# Synthesizing functional programs

See `DeductiveVericoding/Function.lean`.

It reifies the programs so that they can be extracted, i.e. they will not be erased by normalization. Running `evalM` on the program converts it to a monadic program which can then be executed with `run`.

It has a `Codable P Q` structure where `P` and `Q` are the pre- and post-conditions. This structure stores the program `s`, and a correctness proof in the form of a `triple P s.evalM Q`.

There are combinators that look like
```
def append {P : Nat → Prop} {x y : Nat → String}
    (r1 : Codable P (fun n res => res = .str (x n)))
    (r2 : Codable P (fun n res => res = .str (y n))) :
    Codable P (fun n res => res = .str (x n ++ y n))
```

By applying these kinds of combinators, we refine or decompose the coding goal `Codable P Q `into smaller subgoals of the same form. Some pure Lean proof obligations may also be generated on the side. Right now, I have a simple tactic `vericode` that cycles through these combinators until we get a program.