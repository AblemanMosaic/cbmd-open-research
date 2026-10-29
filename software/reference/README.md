# Exact reference toolkit

Python 3.10 or later; standard library only; no install, producer import, or
network access required. Run these commands from the repository root:

```console
python software/reference/evaluate.py 1 3 4 0
python tools/verify_standalone.py
python -m unittest discover -s software/reference -p "test_*.py"
```

The evaluator returns the integer value, both coefficient vectors, and the
declared BCM-1 arithmetic charges as JSON. Inputs are `A R delta f`. At the
native bridge, `delta` is **active-set cardinality**, and `f` is **mismatch
cardinality minus one**. This API supports natural `A,delta`, `R>=1`, and
`0<=f<R`; it refuses other inputs. The scalar formula can be evaluated beyond
native state parameters, but such an evaluation alone has no native meaning.

For degree `d=R-1-f`, the metered recurrence executes both tables once, then
the convolution and final power-of-two scaling. It charges exactly
`mul=3*d+2, div=2*d, add=d+1`, including at `A=0`. The older historical scratch
audit skipped the negative-binomial recurrence at `A=0`; this toolkit follows
the full recurrence in `BCM1CostSemantics.lean` instead. Counts exclude integer
bit complexity, parameter arithmetic, signs, power construction, comparisons,
control flow, indexing, allocation, and memory. Zero support/orbit branches
report zero **scalar** charges; their recognition is not claimed free.

The Python API is in `cbmd_reference/model.py`. `UniversalState` holds a head
word, all slot words, and a finite color count. `joint_entry` implements the
coordinatewise candidate, checking the common native Joint fiber before
evaluating a cell. It refuses arbitrary state pairs outside that fiber.
`orbit_compatible` checks unselected slots as well as each selected head/slot
pair; checking the column head alone would be insufficient.

The audit compares the recurrence with a separately coded falling-factorial
formula, with parity coefficients solved from their interpolation equations
over exact fractions, and with literal native integer-difference expansions.
Small swap orbits are independently enumerated by bit masks. It exercises
`A=0`, `R=1`, `m=0`, negative generalized-binomial upper arguments, support
zeros and live boundary cells; it must detect damaged signs, scale, delta,
ordinary-binomial conventions, orbit clauses, and support bounds. Its JSON
contains deterministic case and value digests, hashes of the actual Python
files, counts, and explicit mutant witnesses. This gives reviewers an offline
falsification tool without importing the frozen producer.

These are finite exact audits written by the project. They are not a Lean
replay, formal verification of the Python interpreter or translation, or an
external independent review. General statements belong to the separately
compiled Lean proof chain. Neither the toolkit nor its operation counts
establish a total native speedup, a SAT asymptotic improvement, novelty, or any
ECH geometric transport.
