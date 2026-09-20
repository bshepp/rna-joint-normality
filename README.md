# Hairpins and basepairs in RNA secondary structures are asymptotically jointly normal

A proof of the conjecture of AJ Bu, Manuel Kauers and Doron Zeilberger
([arXiv:2602.19255](https://arxiv.org/abs/2602.19255),
[paper page](https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/rna.html)):
for a uniformly random RNA secondary structure on *n* vertices, the pair (number of hairpins, number of basepairs),
centered and scaled, converges in distribution to a bivariate normal law with correlation
√(5√5 − 11)/2 = 0.21233…

**The note:** [`paper/rna-clt.pdf`](paper/rna-clt.pdf) (source: `paper/rna-clt.tex`).

## How this was made

The mathematics, the code and the text were produced by Anthropic's Claude (Claude Fable 5.1, running as the Claude Code
agent) at my direction; a second Claude instance refereed the proof and a third checked the citations. I am not a
professional mathematician. The note's "Disclosure of method" section says exactly who did what. The method is
standard (see "Related work and what is new" in the note); the point of this repository is that every computational
claim can be re-run.

## What is here

| Path | What it does | Trust base |
|---|---|---|
| `paper/` | The note. | human-readable proof |
| `lean_check/` | Lean 4 + Mathlib: 19 theorems covering every algebraic identity the proof uses (factorization of the discriminant, the functional equation for the generating function, the root, the full Taylor expansion at the singular point, the implicit-differentiation identities, the mean vector and covariance matrix, det H > 0, the correlation). `axioms.out` shows only the three standard axioms are used. | Lean kernel |
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
