# Release scope

ProofLoom is maintained by **Melon Group · PKU CMLR**.

This repository distributes 32 Lean formalization projects, the canonical SOptLib library, structured source
specifications, dependency locks, and source verification tools. Structured JSON
specifications stay with their Lean developments so the formal statements can be
traced to their mathematical inputs.

Selected paper figures and reported results appear in the README and
[paper notes](PAPER.md).

Each Lean project includes its exact local library closure. Project-local library
versions are retained alongside the canonical library.

Verification reports record the checked source hashes, pinned dependencies, and
check provenance. [TRUST.md](TRUST.md) describes the formal statements, explicit
assumptions, and source-target coverage.

Original project contributions are released under the [MIT License](../LICENSE).
Third-party sources and dependencies retain their own terms and attribution; see
[third-party notices](../THIRD_PARTY_NOTICES.md).
