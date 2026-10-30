# Verification

`reference-model/verify.py` checks the exact imported member hashes, reruns both independent bounded evidence producers, removes wall-clock diagnostics before comparison, and requires both adverse unit controls to pass.

Expected result: 163,912 amplitude equalities, 10,476 row equalities, two adverse-control refusals, and `native_transport: NOT_EVALUATED`.

`independent/derive_m7.py` (revision 0.4.0-candidate) checks the four steps of the B5-M7 derivation in `argument/M7_DERIVATION.md` with code written from the definitions, imports the frozen source only for a final labelled cross-check, and requires two mutated statements to fail. It takes about 40 seconds.
