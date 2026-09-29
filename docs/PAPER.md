# Research notes

This companion to the [README](../README.md) summarizes *ProofLoom:
Proof-Obligation-Driven Theory Construction for Autoformalizing Research-Level
Stochastic Optimization*. Figures, reported results, and examples follow the
supplied manuscript's `main_iclr_submission.tex`. They describe that research
snapshot; the released code has its own source-bound verification records.

## Worked example: SAM's Gaussian KL bridge

SAM's generalization proof needs a KL calculation for a Gaussian posterior
$Q=\mathcal{N}(w,\sigma^2 I_d)$ and prior $P_j=\mathcal{N}(0,v_j I_d)$, with
$\sigma>0$ and $v_j>0$:

$$
\operatorname{KL}(Q\Vert P_j)
=\frac{1}{2}\left(
\frac{d\sigma^2+\lVert w\rVert^2}{v_j}
-d+d\log\frac{v_j}{\sigma^2}\right).
$$

The available KL theorem uses Euclidean coordinates. The algorithm development
represents Gaussian laws as affine pushforwards on a finite-dimensional
inner-product space. Applying the theorem therefore requires proving that the
two representations describe the same measures.

The original bridge allowed an arbitrary measurable structure. It did not supply
the `BorelSpace E` and `SecondCountableTopology E` structure needed to establish a
measurable equivalence through an orthonormal coordinate map. Planner identified
this as a modeling obstruction. Reconstruction made the source's Euclidean
measurable structure explicit, then built the missing transport argument:

1. Identify the affine Gaussian pushforward by its mean and covariance.
2. Prove `coordinateGaussianLaw_map` to identify the laws under the coordinate map.
3. Prove `coordinateGaussianKLTransport` using invariance of KL under measurable
   equivalence.
4. Apply the Gaussian KL formula and preservation of the squared norm.

The resulting calculation supplies the selected-Gaussian prior-grid proof. The
identity is proved rather than added as an assumption. This closes the local KL
obligation; the radius bound and event comparisons are separate proof steps.

[Read the SAM Lean source](../formalizations/SAM/Algorithms/Unverified/SAM.lean)
and its [mathematical specification](../formalizations/SAM/source/SAM.json).
The release's [trust report](TRUST.md) separately discloses private expected-error
tests and the public theorem dependency boundary.

## Evaluation reported in the paper

The benchmark comprises ten FOML tasks and five research-paper tasks. Seven systems
receive a cumulative 48-hour generation budget per task, including resumed runs.
All five research-paper tasks use the same SOptLib snapshot, containing only the
FOML results and construction records; it is held fixed during their evaluation.

Human evaluation uses a 1–7 rubric established by two Lean experts, blind ratings,
and expert adjudication of disagreements. G-Eval and FidelityEval each use a
0–100 scale with four model judges. Scores are means within each task group,
not proof-success percentages. The human means are shown in the [README](../README.md#results).

<details>
<summary><b>FOML: all model-based scores</b></summary>

| System | G-Eval GPT | Gemini | DeepSeek | Claude | FidelityEval GPT | Gemini | DeepSeek | Claude |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Raw Codex | 36.5 | 36.7 | 37.6 | 39.9 | 31.4 | 28.4 | 34.3 | 29.5 |
| Raw Codex (Goals) | 35.3 | 36.2 | 36.2 | 41.3 | 30.9 | 29.4 | 35.7 | 29.0 |
| OpenGauss | 43.8 | 48.1 | 47.6 | 48.1 | 43.1 | 35.9 | 44.9 | 36.7 |
| LeanMarathon | 72.9 | 74.3 | 75.9 | 72.4 | 72.1 | 64.6 | 77.0 | 69.3 |
| Trellis | 63.1 | 67.2 | 66.5 | 65.6 | 67.0 | 64.9 | 64.8 | 60.9 |
| Archon | 61.4 | 66.0 | 65.2 | 67.7 | 72.8 | 64.6 | 71.9 | 66.8 |
| **ProofLoom** | **92.0** | **87.9** | **88.6** | **89.4** | **87.8** | **93.3** | **90.1** | **85.8** |

</details>

<details>
<summary><b>Research papers: all model-based scores</b></summary>

| System | G-Eval GPT | Gemini | DeepSeek | Claude | FidelityEval GPT | Gemini | DeepSeek | Claude |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Raw Codex | 36.3 | 39.0 | 34.6 | 40.8 | 35.3 | 37.2 | 35.0 | 26.2 |
| Raw Codex (Goals) | 47.9 | 47.6 | 44.8 | 48.0 | 44.7 | 46.2 | 45.4 | 36.6 |
| OpenGauss | 54.7 | 52.2 | 48.8 | 51.8 | 52.5 | 50.2 | 55.8 | 43.6 |
| LeanMarathon | 65.5 | 66.8 | 68.8 | 63.8 | 66.9 | 63.4 | 68.8 | 60.6 |
| Trellis | 64.7 | 76.2 | 66.0 | 67.8 | 67.5 | 71.6 | 69.6 | 65.2 |
| Archon | 72.7 | 69.2 | 67.6 | 70.8 | 77.1 | 75.0 | 79.2 | 72.4 |
| **ProofLoom** | **89.9** | **84.6** | **80.8** | **90.6** | **81.5** | **89.6** | **83.8** | **86.6** |

</details>

The manuscript names the judges as GPT 5.6-sol, Gemini 3.8 Flash, DeepSeek V4 Pro,
and Claude Opus 5. These labels are transcribed from the supplied paper.

### Mechanism ablation

The paper reviews 43 obstruction cases across three configurations (129 runs).
The counts below combine its 29 model/interface mismatches and 14 cases involving
false or underspecified claims.

| Configuration | Crossing | Partial | Incorrect |
| :--- | ---: | ---: | ---: |
| Without Judge | 29 | 8 | 6 |
| Without Planner–Audit | 29 | 13 | 1 |
| Full ProofLoom | 33 | 9 | 1 |

**Crossing** means a correct diagnosis and a source-faithful repair direction.
**Partial** means the diagnosis or repair direction remains unresolved.
**Incorrect** means an erroneous replacement or unsupported change to the
source-facing mathematical statement. These are human-adjudicated repair labels,
not counts of completed convergence proofs.

## Source findings and release scope

The [construction atlas](assets/paper-artifact-atlas.pdf) visualizes algorithm code
and reused SOptLib support across the paper's 33 developments. Counts exclude
blank and comment-only lines, with library support deduplicated per development.
The September 28 design retains the archived statistics, last updated on
September 25. [Figure data](assets/paper-artifact-atlas-data.json) records the
counting rules, snapshot scope, and square-root scales.

The paper's audit reports 28 independent discrepancies affecting 22 of its 33
developments: 25 original-source issues and three issues in author-revised
versions. The SAM scale mismatch and restricted-domain smoothness issue in the
[README](../README.md#what-formalization-reveals) are selected examples.

Its corpus census contains 33 construction snapshots, including one unreleased
development. This repository releases **32 developments** and a separately frozen
canonical SOptLib snapshot. Paper-level line and declaration counts should not be
used as measurements of this checkout.

There are also differences in endpoint versions. For example, the paper's
evaluation describes SAPD's full expected-gap and tail claims as targets; the
released revision includes a corrected fixed-domain expected-gap theorem with
explicit extra premises. Its high-probability endpoint remains unfinished.
See the [SAPD version note](../formalizations/StochasticAcceleratedPrimalDual/README.md).

Semantic review relies on model judgments and can miss changes to assumptions or
conclusions. Research-level construction can take hours, and the reported
evaluation is confined to stochastic optimization. The [trust report](TRUST.md)
and [verification records](../formalizations/VERIFICATION.md) describe what the
released sources establish, including custom library axioms and added hypotheses.

## Source map

The presentation follows these parts of `main_iclr_submission.tex`:

| Material | Manuscript section or label |
| :--- | :--- |
| Construction order and conditional-expectation example | §2; `fig:construction-order` |
| System overview | §2.2; `fig:pipeline` |
| Signature contracts and Planner–Audit | §3 |
| SOptLib layers and learning | §4; `tab:layers` |
| Seven-system results | §5.1–5.2; `tab:main-results` |
| Ablation | §5.3; `tab:mechanism-ablation` |
| SAM and restricted-domain findings | §5.4; `app:source-findings` |
| SAM Gaussian KL construction | `app:sam-construction` |
| Snapshot and endpoint scope | `app:corpus-census`; `app:source-endpoints` |

The construction-order and system-overview diagrams correspond to the manuscript's
`Figure1_construction_order.pdf` and `Figure1_aporune_refined.pdf`. Figure code is
schematic.
