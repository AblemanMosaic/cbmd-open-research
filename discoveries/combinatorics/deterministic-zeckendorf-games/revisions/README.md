# Revisions

| Version | Note |
|---|---|
| 0.1.0 | First record: length identity (written), SS regularity (conjecture, representation checked to 120,000), closed form at Fibonacci numbers, block law, CS Hankel-rank evidence, winner descriptions. |
| 0.2.0 | Counter lemma proved (written) and gated: the SS counting phase is the lazy Fibonacci counter in radix order, with trailing-ones split counts. |
| 0.3.0 | Exact length of Split Smallest proved (written): counting phase, lazy stopping word, end-phase block formula, assembly; gated to n <= 3000 and checked to n <= 120,000. Independent review fixes: stronger run-lemma hypothesis, corrected r = 0 case, explicit conservation invariant, §3 indexing (G_k = F_{k+1}) and n − Z(n) step, mod-2 automaton and 89-state claims withdrawn. |
| 0.4.0 | Combine Smallest: L_CS(n) = c n + O(log^2 n) with c = sum 1/f_{2k-1} - 1/phi (written proof: counter, round, tail and budget lemmas); gates in cs_constant.py; C deviations to 4 x 10^9. |
| 0.4.1 | Second independent review of the CS proof applied (Q_2 coordinates, case C reason, one-feed invariant, round as multiset, tail bound 5); exact polylog CS algorithm cs_exact.py; deviation grows like -0.42 log_phi n (observed). |
