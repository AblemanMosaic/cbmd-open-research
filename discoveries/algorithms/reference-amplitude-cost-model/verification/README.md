# Verification

`reference-model/verify.py` checks the exact imported member hashes, reruns both independent bounded evidence producers, removes wall-clock diagnostics before comparison, and requires both adverse unit controls to pass.

Expected result: 163,912 amplitude equalities, 10,476 row equalities, two adverse-control refusals, and `native_transport: NOT_EVALUATED`.
