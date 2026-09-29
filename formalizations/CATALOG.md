# Algorithm catalog

Each of the 32 directories is an independent Lean project. Original file names,
import graphs, and project-specific library versions are preserved.

Run `./proofloom proofs --algorithm ID` from the package root. The complete source inventory is in [manifest.json](manifest.json). Verification results are in [VERIFICATION.json](VERIFICATION.json); see [trust boundaries](../docs/TRUST.md).

| ID | Algorithm lines¹ | Source | Entry |
|---|---:|---|---|
| `AMSGrad` | 9,247 | Reddi, Kale, and Kumar, ICLR 2018, On the Convergence of Adam and Beyond (Algorithm 2 and Theorem 4) | [Lean](AMSGrad/Algorithms/Unverified/AMSGrad.lean) · [source](AMSGrad/source/AMSGrad.json) |
| `HeavyBallSecondRiddle` | 15,825 | Research notes and evidence bundle (HB-A (Theorem A); Theorems B--C; D1--D11) | [Lean](HeavyBallSecondRiddle/Algorithms/Unverified/HeavyBallSecondRiddle.lean) · [source](HeavyBallSecondRiddle/source/HeavyBallSecondRiddle.json) |
| `Lion` | 6,253 | Wei Jiang and Lijun Zhang, Convergence Analysis of the Lion Optimizer in Centralized and Distributed Settings, arXiv:2508.12327v1 (2025), Algorithm 1 (v1), Lemma 1, Theorem 1 | [Lean](Lion/Algorithms/Unverified/Lion.lean) · [source](Lion/source/Lion.json) |
| `MARS` | 10,098 | Yuan, Liu, Wu, Zhou, and Gu, ICML 2025, PMLR 267:73553-73587 (Theorems B.5, B.6, Lemma 3.4) | [Lean](MARS/Algorithms/Unverified/MARS.lean) · [source](MARS/source/MARS.json) |
| `NonconvexStochasticAcceleratedGD` | 6,424 | Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020 (Algorithm 6.4 and Theorem 6.12) | [Lean](NonconvexStochasticAcceleratedGD/Algorithms/Unverified/NonconvexStochasticAcceleratedGD.lean) · [source](NonconvexStochasticAcceleratedGD/source/NonconvexStochasticAcceleratedGD.json) |
| `NonconvexStochasticBlockMirrorDescent` | 3,605 | Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, Section 6.3 (Theorem 6.9) | [Lean](NonconvexStochasticBlockMirrorDescent/Algorithms/Unverified/NonconvexStochasticBlockMirrorDescent.lean) · [source](NonconvexStochasticBlockMirrorDescent/source/NonconvexStochasticBlockMirrorDescent.json) |
| `NonconvexStochasticFirstOrder` | 4,348 | Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020 (Theorem 6.2) | [Lean](NonconvexStochasticFirstOrder/Algorithms/Unverified/NonconvexStochasticFirstOrder.lean) · [source](NonconvexStochasticFirstOrder/source/NonconvexStochasticFirstOrder.json) |
| `NonconvexStochasticMirrorDescent` | 12,072 | Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020 (Theorem 6.7) | [Lean](NonconvexStochasticMirrorDescent/Algorithms/Unverified/NonconvexStochasticMirrorDescent.lean) · [source](NonconvexStochasticMirrorDescent/source/NonconvexStochasticMirrorDescent.json) |
| `NonconvexVarianceReducedMirrorDescent` | 4,480 | Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, Section 6.5.1, Algorithm 6.6, Theorem 6.14, Corollary 6.20 | [Lean](NonconvexVarianceReducedMirrorDescent/Algorithms/Unverified/NonconvexVarianceReducedMirrorDescent.lean) · [source](NonconvexVarianceReducedMirrorDescent/source/NonconvexVarianceReducedMirrorDescent.json) |
| `PAGE` | 7,022 | Li, Bao, Zhang, Richtarik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization, ICML 2021 (Theorem 1) | [Lean](PAGE/Algorithms/Unverified/PAGE.lean) · [source](PAGE/source/PAGE.json) |
| `PullWithMemoryDGD` | 4,191 | Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, arXiv:2512.24483v1 (Theorem 2) | [Lean](PullWithMemoryDGD/Algorithms/Unverified/PullWithMemoryDGD.lean) · [source](PullWithMemoryDGD/source/PullWithMemoryDGD.json) |
| `RSGF` | 8,055 | G. Lan, First-Order and Stochastic Optimization Methods for Machine Learning, Springer 2020, Section 6.1.2.1 (Theorem 6.3) | [Lean](RSGF/Algorithms/Unverified/StochasticZerothOrder.lean) · [source](RSGF/source/StochasticZerothOrder.json) |
| `RandomGradientExtrapolation` | 13,654 | Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020 (Algorithm 5.4, Theorem 5.4) | [Lean](RandomGradientExtrapolation/Algorithms/Unverified/RandomGradientExtrapolation.lean) · [source](RandomGradientExtrapolation/source/RandomGradientExtrapolation.json) |
| `RandomPrimalDualGradient` | 17,002 | Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, Section 5.1, Theorem 5.1 | [Lean](RandomPrimalDualGradient/Algorithms/Unverified/RandomPrimalDualGradient.lean) · [source](RandomPrimalDualGradient/source/RandomPrimalDualGradient.json) |
| `RandomizedAcceleratedProximalPoint` | 18,507 | Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020 (Theorem 6.16) | [Lean](RandomizedAcceleratedProximalPoint/Algorithms/Unverified/RandomizedAcceleratedProximalPoint.lean) · [source](RandomizedAcceleratedProximalPoint/source/RandomizedAcceleratedProximalPoint.json) |
| `SAM` | 14,835 | Foret, Kleiner, Mobahi, Neyshabur, Sharpness-Aware Minimization for Efficiently Improving Generalization (ICLR 2021), Appendix Theorem 2 | [Lean](SAM/Algorithms/Unverified/SAM.lean) · [source](SAM/source/SAM.json) |
| `SPIDER` | 22,447 | Fang, Li, Lin, Zhang, Spider: Near-Optimal Non-Convex Optimization via Stochastic Path Integrated Differential Estimator, arXiv:1807.01695v2 (Theorem 1) | [Lean](SPIDER/Algorithms/Unverified/SPIDER.lean) · [source](SPIDER/source/SPIDER.json) |
| `StochasticAcceleratedGradientDescent` | 12,448 | Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020 (Theorem 4.4) | [Lean](StochasticAcceleratedGradientDescent/Algorithms/Unverified/StochasticAcceleratedGradientDescent.lean) · [source](StochasticAcceleratedGradientDescent/source/StochasticAcceleratedGradientDescent.json) |
| `StochasticAcceleratedMirrorProx` | 8,604 | Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020 (Theorem 4.10) | [Lean](StochasticAcceleratedMirrorProx/Algorithms/Unverified/StochasticAcceleratedMirrorProx.lean) · [source](StochasticAcceleratedMirrorProx/source/StochasticAcceleratedMirrorProx.json) |
| `StochasticAcceleratedPrimalDual` | 15,952 | Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, Section 4.4.2, Algorithm 4.3, Theorem 4.8, Corollary 4.3 | [Lean](StochasticAcceleratedPrimalDual/Algorithms/Unverified/StochasticAcceleratedPrimalDual.lean) · [source](StochasticAcceleratedPrimalDual/source/StochasticAcceleratedPrimalDual.json) |
| `StochasticBlockMirrorDescent` | 5,046 | Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020 (Theorem 4.12) | [Lean](StochasticBlockMirrorDescent/Algorithms/Unverified/StochasticBlockMirrorDescent.lean) · [source](StochasticBlockMirrorDescent/source/StochasticBlockMirrorDescent.json) |
| `StochasticConditionalGradientSliding` | 6,192 | Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020 (Algorithm 7.8, Theorem 7.11) | [Lean](StochasticConditionalGradientSliding/Algorithms/Unverified/StochasticConditionalGradientSliding.lean) · [source](StochasticConditionalGradientSliding/source/StochasticConditionalGradientSliding.json) |
| `StochasticConvexConcaveSaddlePoint` | 9,284 | Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020 (Proposition 4.10) | [Lean](StochasticConvexConcaveSaddlePoint/Algorithms/Unverified/StochasticConvexConcaveSaddlePoint.lean) · [source](StochasticConvexConcaveSaddlePoint/source/StochasticConvexConcaveSaddlePoint.json) |
| `StochasticGradientSliding` | 62,249 | Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020 (Corollary 8.3) | [Lean](StochasticGradientSliding/Algorithms/Unverified/StochasticGradientSliding.lean) · [source](StochasticGradientSliding/source/StochasticGradientSliding.json) |
| `StochasticMirrorDescent` | 4,311 | Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020 (Theorem 4.1) | [Lean](StochasticMirrorDescent/Algorithms/Unverified/StochasticMirrorDescent.lean) · [source](StochasticMirrorDescent/source/StochasticMirrorDescent.json) |
| `StochasticNonconvexCGSliding` | 6,774 | Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020 (Section 7.5.2, Theorem 7.18, Corollary 7.13) | [Lean](StochasticNonconvexCGSliding/Algorithms/Unverified/StochasticNonconvexCGSliding.lean) · [source](StochasticNonconvexCGSliding/source/StochasticNonconvexCGSliding.json) |
| `StochasticNonconvexConditionalGradient` | 25,223 | Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020 (Algorithm 7.13, Theorem 7.17, and Corollary 7.12) | [Lean](StochasticNonconvexConditionalGradient/Algorithms/Unverified/StochasticNonconvexConditionalGradient.lean) · [source](StochasticNonconvexConditionalGradient/source/StochasticNonconvexConditionalGradient.json) |
| `StochasticRecursiveMomentum` | 17,513 | Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, arXiv:1905.10018v3 (Theorem 1) | [Lean](StochasticRecursiveMomentum/Algorithms/Unverified/StochasticRecursiveMomentum.lean) · [source](StochasticRecursiveMomentum/source/StochasticRecursiveMomentum.json) |
| `StochasticZerothOrder` | 12,524 | Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020 (Theorem 6.4) | [Lean](StochasticZerothOrder/Algorithms/Unverified/StochasticZerothOrder.lean) · [source](StochasticZerothOrder/source/StochasticZerothOrder.json) |
| `VarianceReducedAcceleratedGradientDescent` | 30,989 | Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020 (Theorem 5.9) | [Lean](VarianceReducedAcceleratedGradientDescent/Algorithms/Unverified/VarianceReducedAcceleratedGradientDescent.lean) · [source](VarianceReducedAcceleratedGradientDescent/source/VarianceReducedAcceleratedGradientDescent.json) |
| `VarianceReducedMirrorDescent` | 13,081 | Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020 (Corollary 5.8) | [Lean](VarianceReducedMirrorDescent/Algorithms/Unverified/VarianceReducedMirrorDescent.lean) · [source](VarianceReducedMirrorDescent/source/VarianceReducedMirrorDescent.json) |
| `RCDGD` | 6,373 | Anonymous research note RCDGD-1 (Theorem 4.2) | [Lean](RCDGD/Algorithms/Unverified/RCDGD.lean) · [source](RCDGD/source/RCDGD.json) |

¹ Physical source lines, including comments and imports, summed over algorithm modules; imported analytical/library modules are not counted as algorithm lines. These counts describe this package, not the earlier paper census.

## Source versions and mathematical scope

All 32 closures have retained successful compilation records bound to their source
hashes. Compilation does not prove source-target completeness.

RGE, RAPP, VRAGD, and VRMD expose additional analytical hypotheses. SAPD's corrected
high-probability endpoint remains unfinished. Lion uses the verified source closure
identified in its manifest. See
[trust boundaries](../docs/TRUST.md) and [verification](VERIFICATION.md).

RSGF and StochasticZerothOrder have distinct source closures despite similarly
named entries. Library copies are intentionally separate; the complete canonical
snapshot lives in [SOptLib](../soptlib/README.md).

The RCDGD input cites a research note whose author identity is absent from the
supplied source. Its citation is preserved rather than attributed speculatively.
