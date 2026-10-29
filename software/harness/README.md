# CBMD portable harness v0.1

This is the portable control plane used to record and check research operations
in Constraint-Bound Mathematical Discovery. Python 3.12 or newer and the standard
library are sufficient for the harness. Lean/Lake and Git are optional external
tools required only for Lean planning and execution.

From the repository root:

~~~text
python tools/verify_harness.py
python software/harness/cbmd.py orient
python software/harness/cbmd.py verify
python software/harness/cbmd.py court
python software/harness/cbmd.py health
~~~

The verify command checks contracts, the journal, intent/terminal bindings,
operation identities, and captured stream hashes. The court command also runs
every required test, with zero skips permitted. These are self-checks of the
instrument.

A fresh checkout correctly reports health DEGRADED: its UCM native proof
adapter remains GAP, mathematical adverse evidence is UNOBSERVED, and no local
process observations have been recorded. Historical producer results are not
imported into a reader's workspace. Passing the control tests does not change
those observations.

## Run the complete process-custody example

The shipped template has an empty execution-root list. Execution starts only
after an operator explicitly configures a fresh local workspace. Run the
following from the repository root; the dot names this checkout as the bounded
project directory:

~~~text
python software/harness/cbmd.py init-workspace --path .cbmd-work --execution-root .
python software/harness/cbmd.py --workspace .cbmd-work plan-python --script software/harness/examples/probe.py --cwd . --out .cbmd-work/requests/probe.json
python software/harness/cbmd.py --workspace .cbmd-work run .cbmd-work/requests/probe.json
python software/harness/cbmd.py --workspace .cbmd-work verify
python software/harness/cbmd.py --workspace .cbmd-work court
python software/harness/cbmd.py --workspace .cbmd-work health
~~~

The example prints an integer and attaches no research claim. The initializer
refuses a nonempty destination, a filesystem root, or the operator's home
directory. Repeating an unchanged completed request returns its verified
terminal without rerunning it. An intent without a terminal is UNCERTAIN and
cannot be rerun under the same operation ID.

Add .cbmd-work/ to your local ignore file, or choose a workspace outside the
checkout. Local requests and receipts contain the exact absolute paths needed
to identify the invocation; review them before sharing. This source package
contains no personal-machine roots, historical runtime, or inherited authority.

## Lean planning

With the exact lean-toolchain, lakefile.lean, and lake-manifest.json already
present in a project:

~~~text
python software/harness/cbmd.py --workspace .cbmd-work plan-lean --project proofs/native --module OAI.Algorithms.SubexponentialSAT.SqrtLog.CoordinateOrbitBCM1 --out .cbmd-work/requests/lean.json
python software/harness/cbmd.py --workspace .cbmd-work run .cbmd-work/requests/lean.json
python software/harness/cbmd.py scan-lean proofs/native/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CoordinateOrbitBCM1.lean
~~~

The example selects a bundled module. Use tools/replay_lean.py for the complete
proof replay and proofs/native/SOURCE_MANIFEST.json for its source boundary.
The planner locates the
pinned Elan toolchain under ELAN_HOME or the operator's normal Elan directory.
Git is resolved through CBMD_GIT_EXE or PATH. The request pins the executable,
target source, local import closure, Lake configuration, and available provenance
files. Dependency content and fetched compiler artifacts require the separate
Lean replay boundary supplied by the research project.

The scan-lean command is a conservative lexical check for sorry, admit, and
axiom. It does not inspect compiled proof dependencies, establish consistency,
or replace Lean compilation and source correspondence review. The promote
command checks supplied assessments against method and claim-ceiling policy;
callers must independently justify those assessment fields and evidence roots.
The unbound UCM proof adapter refuses promotion.

## Operational scope

The runner records an intent and journal event before Popen with shell=False,
then captures stdout, stderr, exit code, timeout/interruption, declared output
hashes, and one terminal event. Launch failures are captured as failed
terminals. Recovery records an unobserved result that is ineligible for a
mathematical claim. Verification binds each operation to its journal events
and detects deleted operation directories and rewritten terminals.

This is a single-writer research tool. It is not an operating-system sandbox:
the selected process retains the local operator's permissions, environment,
and network access. Execution roots constrain the declared working directory;
they do not confine arbitrary program effects or prove that every resource
read by a process was declared. Use only reviewed scripts, and use external
isolation when required. A process timeout kills the direct child; this v0.1
does not claim recursive process-tree containment or multi-writer locking.

The role maps are local design correspondences for UGK, EVS, ESA, and GOORRT.
No installed UGK conformance, AOK admission, independent verification, automatic
publication, novelty, or mathematical truth follows from a passing harness
check. There are no commit, push, release, or reviewer-contact commands.

The predecessor hashes and explicit portable test successor are recorded in
[provenance](provenance/LOCAL_PREDECESSOR.json) and the
[successor contract](PORTABLE_SUCCESSOR.md). The project-produced proofs and
mathematical verifiers are separate artifacts in the parent research repository.
