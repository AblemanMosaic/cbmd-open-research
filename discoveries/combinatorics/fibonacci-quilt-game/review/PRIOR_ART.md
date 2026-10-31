# Prior art

- **S. J. Miller and A. Newlon, *The Fibonacci Quilt Game*, Fibonacci Quart.
  58 (2020) (arXiv 1909.01938).**
  - The rules, termination by a square-root-of-indices monovariant, the
    shortest game `n − L(n)`, and rule 2(a) used at most once.
  - Open questions: an upper bound on length, who wins, and others.
- **Catral, Ford, Harris, Miller and Nelson, Fibonacci Quart. 54–55
  (2016–2017).** These treat FQ-legal decompositions. They show that the gap
  between the largest and smallest numbers of summands is unbounded (Theorem
  1.19 of arXiv 1606.09309), which already answers another question that
  Miller and Newlon list.
- **Cusenza et al., *Bounds on Zeckendorf games* (2022).** The potential
  method for the ordinary Zeckendorf game; this dossier adapts it to the
  quilt.

Searches (October 2026) found no later bound on the length of the Fibonacci
Quilt game. Not a novelty determination.

## Relation to Miller and Newlon's simulations (audit, October 2026)

Their Section 3 says "Simulations have never given a game of length close to
or longer than `2n`", and that exploration of `n ≤ 120` suggests the mean and
maximum grow linearly. An independent audit established:

- the simulations were **10,000 uniformly random games** in Mathematica
  (distributions plotted at `n = 20` and `n = 200`), and the paper reports no
  table of mean or maximum lengths, only moment comparisons against a
  Gaussian;
- the paper claims no exhaustiveness anywhere, and proves no upper bound of
  any kind; its Theorem 1.8 gives termination only.

So there is no conflict with the results here. The exhaustive longest games
for `n ≤ 90` first reach `2n` only at `n = 78` and peak at `2.022n` at
`n = 89`, which uniformly random play would rarely find; and the `2.2782n`
figure is from a strategy at `n = 10³`–`10⁶`, far outside their range. The
correct phrasing is that these exceed the longest game their random
simulations found, not that they contradict their paper.

