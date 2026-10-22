# TimeVaryingPushPull

Supplementary formalization snapshot, captured 2026-10-22.

Frozen Phase2F Track-B completion checkpoint c162e39. The split proof files are byte-identical to the completion certificate. Phase3 extraction is still running in a separate live workspace; no intermediate extraction edits are included. Source corrections and extra hypotheses remain visible in the formal declarations. Phase4 integration is not complete.

[Lean entry](Algorithms/Unverified/TimeVaryingPushPull.lean) · [Structured source](source/TimeVaryingPushPull.json) · [Release provenance](release_record.json)

The complete imported local source closure and pinned dependencies are preserved.
Compilation and kernel dependency inspection do not establish source correspondence
or discharge explicit theorem hypotheses. Original paper PDFs and model transcripts
are not included. This development is separate from the paper’s fixed benchmark.

From the repository root:

```bash
./proofloom proofs --algorithm TimeVaryingPushPull
```

The original Algorithms library uses `maxHeartbeats = 1000000`. Both the
packaged Lake configuration and direct-source verifier preserve this option.
The initial publication check with Lean’s default 200000 heartbeats timed out
in Part003/Part005; no proof statement or proof term was changed.
