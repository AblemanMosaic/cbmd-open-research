# v0.1.0 qualification evidence

`LEAN_REPLAY_RECEIPT.json` is the path-sanitized summary of the local release-candidate replay. The private diagnostic receipt retains exact host paths and timings and is intentionally excluded from the public repository.

The replay started without project OAI build outputs, reused a pinned dependency cache, rechecked every dependency revision and tracked-file state, compiled all nine targets and the audit module, and executed the logical-dependency ceiling. The public CI workflow independently repeats the replay on GitHub infrastructure using the same committed inputs.

This is project self-verification. It is not specialist review, source-specific novelty assessment, or a total cost/speed theorem. The release archive hash and Git commit are carried in the detached release receipt generated after the source commit is frozen.
