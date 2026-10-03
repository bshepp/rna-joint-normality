# Hairpins and basepairs in RNA secondary structures are asymptotically jointly normal

A proof of the conjecture of AJ Bu, Manuel Kauers and Doron Zeilberger
([arXiv:2602.19255](https://arxiv.org/abs/2602.19255),
[paper page](https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/rna.html)):
for a uniformly random RNA secondary structure on *n* vertices, the pair (number of hairpins, number of basepairs),
centered and scaled, converges in distribution to a bivariate normal law with correlation
√(5√5 − 11)/2 = 0.21233…

**The note:** [`paper/rna-clt.pdf`](paper/rna-clt.pdf) (source: `paper/rna-clt.tex`). The byline is "Claude (Anthropic),
directed and checked by Brian Sheppard". `paper/arxiv/` is the same note with the byline arXiv policy requires
("Brian Sheppard", with a footnote crediting Claude); the two differ in nothing else.

## How this was made

This is not a conventional paper and I am not its mathematician. I'm a software engineer with a course in
mathematical thinking and one undergraduate paper (on topological robot motion planning,
[arXiv:2403.05570](https://arxiv.org/abs/2403.05570)). In the course of this work I learned what a secondary
structure and a hairpin are and how the argument is built; I can follow its logic in outline and I know what
questions to ask of it. I could not have produced it and I cannot certify it.

Everything mathematical here - the proof strategy, the proof, the text, the Mathematica and Lean code, the
literature search - was produced by Anthropic's Claude (Claude Fable 5.1, running as the Claude Code agent). My
part was the pipeline and the judgement calls around it: choosing the problem; demanding external validation at
every step; having a second, independent Claude instance referee the proof adversarially; having a third audit
every citation against its source (which found two prior-work papers the first draft had missed); obtaining and
reading the three papers the audit could only confirm second-hand; and insisting that the algebra be certified by a
proof assistant rather than a computer algebra system. I have not independently verified the analytic estimates.

What I'm offering is transparency: the note's first page says exactly who did what, and every computational claim
in it can be re-run from this repository. The method is standard (see "Related work and what is new" in the note).

## What is here

| Path | What it does | Trust base |
|---|---|---|
| `paper/` | The note. | human-readable proof |
| `lean_check/` | Lean 4 + Mathlib: 21 theorems covering every algebraic identity the proof uses (factorization of the discriminant, the functional equation for the generating function, the root, the full Taylor expansion at the singular point, the implicit-differentiation identities, the mean vector and covariance matrix, det H > 0, the correlation). `axioms.out` shows only the three standard axioms are used. | Lean kernel |
| `lean_check/gen/` | Mathematica script that *proposes* the long polynomials, and the Python script that assembles `Basic.lean`. Lean re-verifies everything, so these are not trusted. | none needed |
| `checks/verify.wls` | Exact Mathematica checks: generating function vs brute-force enumeration (n ≤ 14), singularity structure, Hessian, second-order terms of the means vs Theorem 3 of Bu–Kauers–Zeilberger, numerical sanity. Output in `verify.out`. | Mathematica |
| `checks/grammar_check.wls` | The published generating function satisfies the first-vertex grammar equation. | Mathematica (also in Lean) |
| `checks/cuesta_manrubia.wls` | The model is the s = m = 1 case of Cuesta–Manrubia (2017), and our code reproduces their published constants for s = 2, m = 3. | Mathematica |
| `figure/` | Exact joint distribution for n up to 800 (floating point) against the Gaussian limit. Illustration only. | numpy |

## Re-running

```
# Lean (about a minute after the Mathlib cache is downloaded)
cd lean_check && lake exe cache get && lake build && lake env lean Axioms.lean

# Mathematica
wolframscript -file checks/verify.wls
wolframscript -file checks/grammar_check.wls
wolframscript -file checks/cuesta_manrubia.wls

# Figure (about 10 minutes; needs numpy, matplotlib)
cd figure && python joint_distribution.py
```

## What is *not* machine-checked

The analytic part of the proof - Rouché's theorem, the uniform coefficient estimate (Lemma 5), Lévy's continuity
theorem - and the elementary calculus linking the Lean identities to the derivatives of −log ρ. Those are proved on
paper in the note.

## Contact

Brian Sheppard, bshepp@gmail.com. Corrections are welcome.

## License

Code: MIT. Text of the note: CC BY 4.0.
