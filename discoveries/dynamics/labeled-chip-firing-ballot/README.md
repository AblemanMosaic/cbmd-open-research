# Labeled chip-firing on trees: the ballot conjecture is false

> **Standing:** `EXACT_MODEL_VERIFIED`, `PROVISIONAL_WRITTEN_ARGUMENT`

Permanent claim ID: `CBMD-DYN-LABELED-BALLOT-001`

## The question

Labeled chip-firing starts with `N = 2^ℓ − 1` labeled chips at the root of an
infinite binary tree whose root has a self-loop. A vertex holding at least 3
chips sends its smallest chosen chip left, its largest right and its middle
chip up. The process is not confluent, and counting its stable configurations
is open.

- Inagaki, Khovanova and Luo (Ann. Comb., published 2025) conjecture that every stable
  configuration has the **ballot property**: in each subtree, the `i`-th
  smallest chip on the left beats the `i`-th smallest chip on the right.
  - It is Conjecture 3.16 in the published version (3.7 on arXiv).
  - They use it for a "ballot bound" on the number of configurations.
- Inagaki and Lin (2025) conjecture the `k`-ary version.
- The only reported check is the binary one at 15 chips.

## What this dossier finds

- **The conjecture is false (certified).** Explicit legal firing sequences end
  in stable configurations that violate the ballot property:
  - with 31, 63, 127 and 255 chips on the binary tree;
  - with 40 and 121 chips on the ternary tree;
  - with 85 chips on the 4-ary tree.

  The 31-chip example fails at the root itself: the 5th smallest chips of the
  two subtrees are `10 > 9`. The ballot bound rests on the false conjecture,
  so its proof is invalid as written.
- **It holds below that (proved by exhaustive search).** It holds for 15 chips
  (binary), 13 chips (ternary) and 21 chips (4-ary). This independently
  confirms the published 15-chip check.
- **Method.** By a threshold argument, the property becomes red-count
  dominance in a two-colour chip-firing. That is a finite-state process: it can
  be searched exhaustively, and its runs lift back to labeled runs.
- **Independent review:** an independent replay with fresh code confirms every
  certificate. It also re-derived the 36,220 stable configurations at 15
  chips, none violating.

## What is not established

- Failure for every larger tree. Only the listed sizes are certified.
- Whether the ballot bound's values are nevertheless correct.
- The number of stable configurations for 31 or more chips.
- Novelty; see [`review/PRIOR_ART.md`](review/PRIOR_ART.md).

## Smallest decisive tests

- Replaying a certificate under the stated rules and finding an illegal firing
  or no violation.
- A coloured run at 15 chips that violates dominance.

## Reproduction

```text
python -B discoveries/dynamics/labeled-chip-firing-ballot/verification/reference/check_ballot.py
```

## Repository map

- `argument/`: the written argument.
- `verification/reference/`: the certificates, the checker and the search
  tools (C++).
- `evidence/`: check outputs.
- `review/`: prior art.
- `revisions/`: revision history.
