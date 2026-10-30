# Revisions

| Version | Note |
|---|---|
| 0.13.0 | The conflict-free characterization compiled: a bad marking exists exactly when a chain certificate does; conflict-freeness makes the chain deterministic and the input-place hypothesis is used once. Fixpoint-decides-certificate bridged by census. |
| 0.12.0 | Conflict-free nets are polynomial when every transition has an input place, so zero conflict places is polynomial and one is coNP-complete. Written argument; census with three ablations and a test showing the input-place hypothesis is load-bearing. |
| 0.11.0 | Marked graphs are polynomial at any weights and capacities, by a two-occurrence orientation argument; written, with a census and two load-bearing ablations. Conflict-free nets named as the open class between. |
| 0.10.0 | Free choice does not help: the hardness survives in strict free-choice nets with every capacity 1, compiled, with a census that confirms a prediction the proof made about which gadget is idle. |
| 0.9.0 | The hardness reduction compiled end to end: the net built from the guarded form of any CNF preserves exactly when the CNF is unsatisfiable. Only the resource bounds remain prose. |
| 0.8.0 | Fixed-parameter tractable in the number of multi-input transitions, by branching on the unit literal that blocks each one; a classical backdoor argument, applied. |
| 0.7.0 | The last prose step compiled: each lowering strictly drops the total token count, so the procedure halts and a certified greatest marking always exists. |
| 0.6.0 | The polynomial side is about input places alone. With one input place the capacity-dead markings are closed under pointwise maximum, so one marking decides preservation; outputs and weights are free. |
| 0.5.0 | The polynomial side extended from unit weights to arbitrary weights. The obstruction carries levels, not membership, because the unit-weight normalization genuinely breaks. |
| 0.4.0 | The open question answered: a dichotomy at two input places. One input place is polynomial and characterized; two is coNP-complete, already at unit weights and 0/1 capacities. |
| 0.3.0 | The draining regime characterized for unit-weight flow nets: preservation holds exactly when no set of places can be held full. Proved in both directions. |
| 0.2.0 | One region of the boundary proved instead of censused: in a net where every transition increases some place, preservation holds exactly when the net cannot fire at all. Explains why chip-firing needs a sink. |
| 0.1.0 | First publication: exact transfer to chip-firing-shaped nets, the relaxation boundary, and the failure of the natural generalization. |
