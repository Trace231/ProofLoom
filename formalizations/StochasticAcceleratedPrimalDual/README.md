# SAPD release version

This development uses the source closure identified by the published manifest.
It supersedes the
earlier exact-build selection in this package. The selected entry contains
15,952 physical lines; its SHA-256 is
`f98d69a5e8405342fbfeeaddd011b61a50c0cb430c5c70624a20535541c4e57a`.
The source JSON, Lean/Mathlib locks, and all 25 local dependency modules are
unchanged from the previous package selection.

## Proved endpoint and remaining scope

The source now contains the public theorem
`StochasticAcceleratedPrimalDualSetup.theorem_4_8_expected_gap_fixedDomain_mixedCenter_corrected`.
It proves a corrected expected-gap inequality over the completed fixed-domain
Algorithm 4.3 output, with an explicit gradient-mismatch budget through
`Q0WithPrimalBudget`.

Its premises include fixed-domain completion, gradient Lipschitz continuity and
measurability, same-sample iterate/oracle independence (`hdeltaXA_indep`), and a
martingale mean condition (`hmart`). These premises remain explicit corrected
model conditions. The theorem does not derive them all from the original paper
assumptions or prove the original unmodified `Q0` endpoint of Theorem 4.8(a).

The old private `Prop`-valued Theorem 4.8 claim shapes were removed in this
revision. The corrected high-probability endpoint is still unfinished: the
source explicitly identifies the remaining probability proof, denominator-safe
Assumption 9 semantics, event measurability, Lemma 4.1 instantiation, and corrected
Q0/Q1 accounting. This is not a completion certificate for Theorem 4.8(a)/(b).

## Verification

```bash
./proofloom proofs --algorithm StochasticAcceleratedPrimalDual
```

The updated 26-module closure compiled against Lean 4.29.0 and Mathlib
`8a178386ffc0f5fef0b77738bb5449d50efeea95`. Dependency inspection checked 785
algorithm theorem declarations, including private/generated declarations, and
found no `sorryAx` or custom axiom dependency in them. The new public endpoint
was additionally checked with Lean's `#print axioms`; it uses only `propext`,
`Classical.choice`, and `Quot.sound`. Explicit theorem hypotheses are separate
from these kernel axiom dependencies.

See the [source manifest](../manifest.json) and [verification report](../VERIFICATION.json).
