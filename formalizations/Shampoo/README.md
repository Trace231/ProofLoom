# Shampoo

Supplementary formalization snapshot, captured 2026-10-22.

Phase3 and Phase4 completed with library and algorithm builds passing. The development includes the matrix, tensor and diagonal regret endpoints with their explicit comparator and regularity hypotheses and disclosed source corrections. The Phase2F certificate predates extraction and does not directly certify the post-extraction bytes; this release independently recompiles and inspects the packaged post-Phase4 closure.

[Lean entry](Algorithms/Unverified/Shampoo.lean) · [Structured source](source/Shampoo.json) · [Release provenance](release_record.json)

The complete imported local source closure and pinned dependencies are preserved.
Compilation and kernel dependency inspection do not establish source correspondence
or discharge explicit theorem hypotheses. Original paper PDFs and model transcripts
are not included. This development is separate from the paper’s fixed benchmark.

From the repository root:

```bash
./proofloom proofs --algorithm Shampoo
```
