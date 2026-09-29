# SOptLib

The latest coherent canonical SOptLib snapshot captured for this release contains
**43 library modules**, its `SOptLib.lean` umbrella, and the release-only `All.lean`
entry that imports every module. Source hashes, capture time, and pinned Lean /
Mathlib versions are in [manifest.json](manifest.json).

```bash
# From the package root; dependencies are installed automatically on first use
./proofloom soptlib
```

All 45 local Lean files compile; the checked-environment inspection covers 2,874
library theorem declarations. See [VERIFICATION.json](VERIFICATION.json).
Compilation does not mean that every library theorem is axiom-free: the existing
`Axioms/BaillonHaddad.lean` retains three explicit mathematical axioms. Their
consumers are recorded in the report. The new `Analysis/OpenCocoercivity.lean`,
`Analysis/BregmanFromCocoercivity.lean`, and `Analysis/ConvexSmoothExtension.lean`
provide proved alternatives under explicit hypotheses; see [trust scope](../docs/TRUST.md).

Three versions serve different purposes:

| Location | Purpose |
|---|---|
| `soptlib/` | Latest complete coherent library snapshot, including the new analytical proofs |
| `engine/SOptLib/` | Original pipeline project's library, preserved to reproduce its behavior |
| `formalizations/<id>/SOptLib/` | Exact imported library versions needed by each frozen algorithm |

These module namespaces overlap but some definitions differ. Replacing every
copy with the newest one would change proof dependencies. This release keeps
those versions explicit; it does not merge incompatible modules or promote
unfinished `Staging` definitions into the canonical library.
