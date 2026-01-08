# SuSLik

Deductive program synthesis for heap programs

https://arxiv.org/pdf/1807.07022

## SuSLik derivations

$$
\begin{aligned}
\mathcal{G} \in \text{Goal} &::= \langle f, \Sigma, \Gamma, \{\mathcal{P}\}, \{\mathcal{Q}\} \rangle \\
\mathcal{K} \in \text{Cont} &\triangleq (\text{Command})^n \to \text{Command} \\
\mathcal{S} \in \text{Deriv} &::= \langle \overline{\mathcal{G}_i}, \mathcal{K} \rangle \\
\mathcal{R} \in \text{Rule} &\triangleq \text{Goal} \to \wp(\text{Deriv})
\end{aligned}
$$

Goals are of the form $\Gamma, \Sigma; {P} \rightarrow Q \vert f$, where $\Gamma$ is the set of constants, $\Sigma$ is the set of function definitions, $P$ is the precondition (pure predicate and heap state), $Q$ is the postcondition (pure predicate and heap state), and $f$ is the function to be synthesized.

Compare with Loom goals, which are Triples in the monad. The additional parts are the contextual elements like $\Gamma, \Sigma$ which is implicit in Loom.

Both Loom and SuSLik use continuations. We want to generalize beyond continuations, e.g. 
```
<some hole>; 
remainder-of-program
```
to open systems, e.g. 
```
<some hole>; 
some-program; 
<some-other-hole>; 
some-other-program; 
<a-final-hole>;
``` 
(doesn't need to be serial). Of course, we can write the open system below in a continuation form above functionally, but not all monadic programs allow this.