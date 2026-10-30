# Prior art

Date 2026-10-30. No match was located for capacity-blocked chip-firing from a
fixed state. Novelty is **unassessed**.

## Nearest results

- **Chip-firing reachability** (no capacities): Lilla Tóthmérész, *Rotor-routing
  reachability is easy, chip-firing reachability is hard*,
  <https://arxiv.org/abs/2102.11970>. Chip-firing reachability on strongly
  connected digraphs (no sink) has no polynomial algorithm unless the
  polynomial hierarchy collapses. The hardness there comes from recurrence and
  halting on graphs without a sink. Here ordinary firing always terminates (the
  sink is reachable), and the hardness comes from the capacity constraint
  alone.
- **Deadlock avoidance in resource allocation systems**: Mark Lawley and Spyros
  Reveliotis, *Deadlock avoidance for sequential resource allocation systems:
  hard and easy cases*,
  <https://www2.isye.gatech.edu/~spyros/publications/accept-SU-compl.pdf>.
  Safety (can every process still complete?) is NP-complete for single-unit
  sequential resource allocation systems, and polynomial under several
  capacity and routing conditions. FIXED-GOOD is the analogue for chip-firing.
  The models differ: chips are indistinguishable, a firing delivers a bundle
  to every out-neighbour at once, and the sink absorbs. The 3-PARTITION
  reduction here uses the bundle structure directly, and no reduction from the
  resource-allocation results is claimed.
- **Bounded Petri net reachability** is PSPACE-complete in general. The PSPACE
  upper bound here is the standard one.

## Not examined

Kanban and buffer-allocation scheduling literature with batch transfers; any
statement of bin packing as a deadlock-avoidance problem in manufacturing.
