# Getting started

Use Linux, Git, and Python 3.11+ for the supported setup path. Lean is pinned to
4.29.0; every project includes its dependency lock. Allow roughly 15 GB of free
space for dependencies and builds. Large developments can require substantial
memory and time; these are original project estimates, not new measurements.

## Inspect the checkout offline

```bash
./proofloom --help
./proofloom check
```

These commands need only Python and do not install dependencies or call a model.

## Check Lean sources

```bash
./proofloom proofs --algorithm StochasticMirrorDescent
./proofloom soptlib
```

First use installs the pinned Lean toolchain and Mathlib dependencies. The setup script installs Elan
under the user's normal Elan directory if absent; dependencies and build outputs
are stored under `.deps/` and `.build/` in this checkout.

`./proofloom proofs` checks all 32 projects. Use `--jobs`, `--threads`, and
`--memory-mb` to adjust verifier resource limits; run
`python3 scripts/verify_formalizations.py --help` for current defaults and options.
Reports under `.build/` describe your local run. Read [trust scope](TRUST.md)
before interpreting a successful build as a complete proof of a source result.
