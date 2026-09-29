# Contributing to ProofLoom

Maintained by **Melon Group · PKU CMLR**. Start with a focused issue or pull request
that describes the source result or documentation change.

## Formalization changes

Preserve explicit hypotheses and document every statement change. Do not replace
project-local library copies with another version without rebuilding the affected
closure. Update file inventories and regenerate compilation and theorem-dependency
reports with `scripts/verify_formalizations.py`; inherited results cannot certify
changed proofs. Explain any remaining source-target obligations in the project
notes and `docs/TRUST.md`.

Use `python3 -m unittest discover -s scripts -p 'test_*.py'` to check the verifier's
dependency-graph handling. New algorithm projects need a pinned toolchain, Lake
lock, complete local import closure, structured source specification, and catalog
entry.

Keep credentials, model-run transcripts, dependency caches, evaluation datasets,
and paper PDFs out of source contributions. Include attribution for third-party
material and preserve its license terms.
