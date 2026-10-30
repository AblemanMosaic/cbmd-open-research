# Labeled chip-firing on the line: evidence for open HMP conjectures

> **Standing:** `CONJECTURE`, `EXACT_MODEL_VERIFIED` (version 0.2.1)

Permanent claim ID: `CBMD-DYN-LABELED-LINE-001`

## The question

Hopkins, McConville and Propp (*Sorting via chip-firing*, EJC 24(3) 2017)
study labeled chip-firing on `ℤ`. A site with two or more chips sends the
smaller of a chosen pair left and the larger right. With an even number of
chips the outcome is always sorted. With `n = 2m + 1` chips it is not, and two
of their conjectures remain open:

- **Conjecture 26:** the maximal number of inversions of an outcome is `m`
  (checked for `n ≤ 9`);
- **Conjecture 27:** under each of three random protocols, the probability of
  ending sorted tends to `1/3`.

## What this dossier records (evidence, no proof)

- **Conjecture 26 holds at `n = 11`.** The search covers 6,520,201 states and
  819 outcomes, and the maximal inversion count is 5.
- **Exact sorting probabilities for `n ≤ 11`** under protocols 1 (uniform over
  moves) and 2 (uniform unstable site, then uniform pair):

  | `n` | protocol 1 | protocol 2 |
  |---|---|---|
  | 3 | `1/3` | `1/3` |
  | 5 | `1/5` | `1/5` |
  | 7 | `0.2512` | `0.2501` |
  | 9 | `0.3147` | `0.3118` |
  | 11 | `0.3314` | `0.3305` |

  The values for `n ≤ 9` are exact rationals in `evidence/check_line.json`.
- **Monte Carlo up to `m = 80`.** At 20,000 runs per point, the estimates stay
  within 0.006 of `1/3`.

## Loops and parallel edges (Conjectures 21 and 25)

`ℤ⟨S⟩` is `ℤ` with one loop at each `i ∈ S`. A site with `ℓ` left edges, `m`
loops and `r` right edges fires `ℓ + m + r` chips: the `ℓ` smallest labels go
left, the `r` largest go right, and the `m` middle chips stay. `r(G)` replaces
every edge and loop by `r` parallel copies.

- **Conjecture 21 (HMP):** if the stabilization of `n` chips at 0 on `ℤ⟨S⟩`
  strictly extends that of `n − 1` chips at both ends, then `ℤ⟨S⟩` sorts
  `Δⁿ`.
- **Conjecture 25 (HMP):** under the same condition, `r(ℤ⟨S⟩)` sorts `Δ^{rn}`.

Some cases are theorems. `S = ∅` is HMP's even-`n` theorem, and a single loop
site at the origin is their Theorem 20. `S = ℤ` with `n ≡ 3 (mod 4)` is
Klivans–Liscio Theorem 3.13, and these are exactly the qualifying `n` for
`S = ℤ`. Klivans–Liscio also prove Conjecture 24 (`rℤ`). We found no
treatment of general `S`.

**Method.** Colour chips `1..t` red and the rest blue. Labeled runs project to
colour runs, and colour runs lift to labeled runs. So `G` sorts `Δⁿ` if and
only if, for every `t`, no reachable stable colour state has a blue chip
strictly left of a red one (`argument/WRITTEN_ARGUMENT.md`, §2).

**Results (no counterexample).**

| Scan | Range | Instances | Outcome |
|---|---|---|---|
| Conjecture 21 | `S ⊆ [−5,5]`, `\|S\| ≤ 3`, `n ≤ 16` | 614 qualifying | all sort |
| Conjecture 25, `r = 2` | `S ⊆ [−4,4]`, `\|S\| ≤ 3`, `n ≤ 12` (≤ 24 chips) | 287 qualifying | all sort |
| Conjecture 25, `r = 3` | `S ⊆ [−4,4]`, `\|S\| ≤ 3`, `n ≤ 8` (≤ 24 chips) | 242 qualifying | all sort |
| Converse (observation) | `S ⊆ [−5,5]`, `\|S\| ≤ 3`, `deg(0) ≤ n ≤ 14`, `n ≥ 3` | 2,384 non-qualifying | all fail to sort |
| Scaling (observation) | `S ⊆ [−3,3]`, `\|S\| ≤ 3`, `n ≤ 11`, `r ∈ {1,2,3}`, `rn ≤ 24` | 640 cases | `r(ℤ⟨S⟩)` sorts `Δ^{rn}` iff `ℤ⟨S⟩` sorts `Δⁿ` |

In these ranges, the condition of Conjecture 21 is therefore both sufficient
and necessary for sorting, once the origin can fire. (When `0 ∈ S` and
`n = 2`, nothing fires, so the chips are trivially sorted.) HMP do not discuss
a converse; their Remark 22 only relates the two end conditions to a
balance condition on `S`. The converse is not explained by the extreme chips
alone. For example, for `S = {−1}`, `n = 4`, only the threshold `t = 2`
yields an unsorted outcome.

One direction of the scaling is proved (`argument/WRITTEN_ARGUMENT.md`, §3).
If `ℤ⟨S⟩` does not sort `Δⁿ`, then `r(ℤ⟨S⟩)` does not sort `Δ^{rn}`. Hence
Conjecture 25 implies Conjecture 21.

## What is not established

- Proofs of Conjectures 26 and 27.
- Protocol 3 (a uniformly random stabilization sequence).
- Proofs of Conjectures 21 and 25 for general `S`, and of the converse and
  scaling observations. These are checked only in the stated ranges.

## Reproduction

```text
python -B discoveries/dynamics/labeled-chip-firing-line/verification/reference/check_line.py
c++ -O2 -o zline discoveries/dynamics/labeled-chip-firing-line/verification/reference/zline.cpp && ./zline 11
c++ -O2 -o exactp discoveries/dynamics/labeled-chip-firing-line/verification/reference/exactp.cpp && ./exactp 11 2
python -B discoveries/dynamics/labeled-chip-firing-line/verification/reference/check_loops.py
cd discoveries/dynamics/labeled-chip-firing-line/verification/reference/loops_scan
c++ -O2 -o zs_bin zs.cpp && c++ -O2 -o zsr_bin zsr.cpp
python3 run21c.py -5 5 3 16 out21.jsonl        # Conjecture 21 (about 5 minutes on 2 cores)
R=2 python3 run25.py -4 4 3 12 out25_r2.jsonl  # Conjecture 25, r = 2
R=3 python3 run25.py -4 4 3 8 out25_r3.jsonl   # Conjecture 25, r = 3
python3 conv21.py -5 5 3 14 conv.jsonl         # converse scan
python3 scaling.py scaling.jsonl               # scaling scan
```
