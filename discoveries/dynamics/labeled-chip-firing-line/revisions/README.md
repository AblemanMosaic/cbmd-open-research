# Revisions

| Version | Change |
|---|---|
| 0.1.0 | Evidence: Conjecture 26 at n = 11; exact sorting probabilities n <= 11 (protocols 1, 2); Monte Carlo to m = 40. |
| 0.2.0 | Loops and parallel edges. Proved the two-colour criterion (§2), so sorting checks are exact. Gates in `check_loops.py`. Scans: no counterexample to Conjecture 21 (614 instances) or Conjecture 25 (529 instances). Observed a converse (2,384 non-qualifying instances, none sort) and scaling invariance (640 cases). Corrected the Klivans–Liscio prior-art entry: they treat `S = ℤ`, not general `S`. |
| 0.2.1 | Added §3: a written proof that non-sorting scales from `G` to `r(G)`, so Conjecture 25 implies Conjecture 21. The reverse direction is still only observed. Recorded that extreme thresholds (`t = 1`, `t = n − 1`) do not always witness the converse: for example, `S = {−1}`, `n = 4` is witnessed only at `t = 2`. |
