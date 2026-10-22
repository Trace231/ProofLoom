# Muon

Supplementary formalization snapshot, captured 2026-10-22.

Phase2F accepted Track B at iteration 103. The formalization contains an original-generated-run counterexample to the Appendix B.4 directional-small-J otherwise branch under its printed schedules. The corrected branch adds explicit realized cross control; directional and cross control together are equivalent to the Jstar bound used by the proof. The corrected generated-average and uniform-output complexity conclusions are proved. This is a disclosed sufficient repair, not a proof of the unchanged source claim or of globally minimal assumptions. Phase3/Phase4 extraction has not been performed.

[Lean entry](Algorithms/Unverified/Muon.lean) · [Structured source](source/Muon.json) · [Release provenance](release_record.json)

The complete imported local source closure and pinned dependencies are preserved.
Compilation and kernel dependency inspection do not establish source correspondence
or discharge explicit theorem hypotheses. Original paper PDFs and model transcripts
are not included. This development is separate from the paper’s fixed benchmark.

From the repository root:

```bash
./proofloom proofs --algorithm Muon
```
