# SDCS

Supplementary formalization snapshot, captured 2026-10-22.

Phase3 and Phase4 completed with library and algorithm builds passing. The algorithm retains disclosed source corrections and explicit hypotheses; both expected bounds of Theorem 8.11 are included. The Phase2F certificate predates extraction and does not directly certify the post-extraction bytes; this release independently recompiles and inspects the packaged post-Phase4 closure.

[Lean entry](Algorithms/Unverified/SDCS.lean) · [Structured source](source/SDCS.json) · [Release provenance](release_record.json)

The complete imported local source closure and pinned dependencies are preserved.
Compilation and kernel dependency inspection do not establish source correspondence
or discharge explicit theorem hypotheses. Original paper PDFs and model transcripts
are not included. This development is separate from the paper’s fixed benchmark.

From the repository root:

```bash
./proofloom proofs --algorithm SDCS
```
