# Portable successor contract

This v0.1 is a successor of the local Cycle 17 CBMD harness. Original file
hashes are retained in provenance/LOCAL_PREDECESSOR.json; the portable file
manifest identifies this successor. Historical requests, runtime, journal,
state, mathematical receipts, and local execution roots are excluded.

All 22 predecessor test identities are retained. Their substantive controls
remain: canonicalization, tamper detection, exact invocation and idempotence,
intent before execution, uncertainty, interrupted-run custody, prohibited
environment keys, source pins, claim ceilings, and state identity.

The explicit portability changes to predecessor test fixtures are:

- The producer's dated authority ID is replaced by CBMD.LOCAL.OPERATOR.
- Two constructed interrupted-operation fixtures now append their intent to
  the ledger, matching the strengthened operation-to-ledger verification.
- HealthTests.test_health_exposes_remainder expects mathematical adverse
  coverage to be UNOBSERVED and its missing-receipt remainder. The local
  predecessor expected HEALTHY because its historical mathematical receipt
  was present. Copying that expectation without its evidence would be false.

Additional adverse tests cover disabled default execution, explicit setup,
bounded working directories, input drift, launch errors, timeout, missing
terminals, stream tampering on repeated access, absent required outputs,
unbound UCM promotion, deleted operations, and rewritten terminals.

Execution still requires an explicit local configuration. The portable template
confers no user's historical authority. Claim promotion is a policy check over
declared assessments; it is not an independent assessment of mathematical
meaning. The no-escape check is lexical and cannot establish transitive proof
closure by itself.

Scope remains INFORMATION_ONLY, with authority_effect NONE. UGK, EVS, ESA,
COP, and GOORRT maps describe local design correspondences. No installed
conformance, AOK admission, publication authority, or external review is claimed.
