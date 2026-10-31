# Revisions

The first public candidate is version 0.1.0. The preserved Q8 note documents a
qualification failure caused by hidden `PYTHONPATH` dependence and the repair
verified by Q9 and Q10.

`0.1.0-publication-qualification-repairs.md` records the public packaging
failures found and repaired before publication. None changed the theorem,
finite-search outputs, or source-bound proof envelope.

`0.2.0-checked-decoding.md`: external graph instances in a declared JSON format are decoded into the Lean parameters, with the theorem's hypotheses discharged by `decide` and a Lean-side round trip; three controls, two caught by the kernel and one by the round trip.

`0.2.1-qualification-contract.md`: the checked-decoding gate is required in
full qualification, closing the path by which a missing Lean toolchain could
be reported without failing the overall run.
