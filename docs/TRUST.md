# Formalization scope and explicit assumptions

This report describes the released sources. Compilation, dependency
inspection, and coverage of source targets are separate facts.
A source error should be represented by a corrected statement with visible new
conditions or an explicit conditional boundary. It cannot justify describing an
assumed proposition as a proved theorem.

Among the 32 developments with successful retained dependency inspections, no public algorithm theorem depends on
`sorryAx` or a custom mathematical axiom. SAM's private expected-error tests and
compiler-generated `native_decide` assumptions are still disclosed below. This
dependency result does not establish source-target completeness or discharge
explicit theorem hypotheses.

## Current mathematical corrections

Four developments state explicit analytical premises as part of their formal
statements. These premises are not inferred from the original restricted-domain
hypotheses:

| Development | Explicit correction |
|---|---|
| RGE | Each component admits a convex smooth extension agreeing on the original carrier, preserving the original primal norm and dual seminorm; the zero-smoothness case is treated separately |
| VRAGD | Each component has a convex smooth extension with the required component smoothness bound |
| RAPP | The convex regularized subproblem has a convex smooth extension with the required regularized smoothness bound; this does not assert that the original nonconvex component is convex |
| VRMD | The component gradient image is convex on the relative interior; open-domain cocoercivity and the one-sided Bregman bridge are proved, then extended to the boundary |

`SOptLib.Analysis.ConvexSmoothExtension` proves the one-sided Bregman inequality
from its extension premise; the inequality is not inserted as a structure field.
`SOptLib.Analysis.OpenCocoercivity` and `SOptLib.Analysis.BregmanFromCocoercivity`
provide the proved analytical route for VRMD.

The corrections respond to the source-domain issue recorded around Lan's Lemma
5.8: an inverse-gradient point used in that argument need not lie in the original
feasible set. The formal developments expose the additional assumptions
needed for their chosen repair. They should be described as corrected source
results, not unmodified statements with automatically discharged extra premises.

## Library assumptions

The canonical SOptLib snapshot contains three explicitly declared axioms in
`SOptLib/Axioms/BaillonHaddad.lean`:

- `perez_aros_vilches_open_convex_inner_cocoercivity`
- `carrier_baillon_haddad_of_support_upper_gradient_semantics_lipschitz`
- `carrier_baillon_haddad_of_separating_seminorm_affine_support`

The first states an open-domain inner-product cocoercivity result. The other two
state stronger one-sided Bregman boundaries on a carrier. They are distinct
assumptions, and the latter two should not be relabeled as the same theorem.
The full-library inventory records axiom consumers and distinguishes imported
declarations from axioms actually used by a given algorithm theorem.
See [full-library dependencies](../soptlib/VERIFICATION.json) and
[per-development dependencies](../formalizations/VERIFICATION.json).

A count of `axiom` keywords in algorithm entry files does not count imported
assumptions. Conversely, importing a file containing an axiom does not mean every
theorem depends on that axiom. The reports inspect the compiled dependency graph.

## Standard foundations, generated assumptions, and proof holes

The standard Lean foundations are `propext`, `Classical.choice`, and `Quot.sound`.
`sorryAx` is an unfinished proof dependency. `native_decide` generates
compiler-trust assumptions for some finite metadata checks; these are listed
separately from handwritten mathematical axioms.

SAM retains two private expected-error tests under `#guard_msgs` whose theorem
terms depend on `sorryAx`, despite having no literal `sorry` in their source.
No public SAM theorem depends on those tests. The source is preserved and the
dependency inspection reports this distinction. SAPD's `opaque` proposition
names a source-boundary predicate; a syntactic opaque declaration is not itself
a certificate that every claimed endpoint has a proof.

## SAPD and unfinished source targets

SAPD retains Phase 2F revision `7b950c6`. Its public
`theorem_4_8_expected_gap_fixedDomain_mixedCenter_corrected` proves a corrected
fixed-domain expected-gap result with an explicit mismatch budget and additional
premises, including same-sample independence and a martingale mean condition.
The theorem's kernel dependencies are the standard three foundations. That does
not discharge its explicit premises or prove the original unmodified Theorem 4.8.
The corrected high-probability endpoint remains unfinished. See the [SAPD version note](../formalizations/StochasticAcceleratedPrimalDual/README.md).

Verification status and source-hole inventories are recorded per development in
[the verification report](../formalizations/VERIFICATION.json). Lion uses the
verified source closure identified in its manifest. Source-token counts alone
are insufficient.

## Reproduce the checks

```bash
./proofloom proofs
./proofloom soptlib
```

The verifier checks file hashes, compiles local imports from packaged sources,
and traverses declaration/type/proof edges in Lean's checked environment,
including private and generated theorems. Compact packaged reports are bound
to their source hashes. Local diagnostics are written only under ignored `.build/`.
Compilation and dependency inspection do not replace the original Phase 2F
source-faithfulness and corrected-source acceptance checks.

