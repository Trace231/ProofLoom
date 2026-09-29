# Formalization verification records

All 32 released local source closures have retained successful compilation and
checked-environment dependency-inspection records from the supplied archive.
Each record identifies the verified source hashes, pinned dependencies, and
check provenance.

Source-target coverage remains distinct. SAPD has an unfinished high-probability
endpoint; four analyses have explicit corrected hypotheses. See
[TRUST.md](../docs/TRUST.md).

| Development | Retained verification | Algorithm theorem declarations¹ | Public uses sorryAx | Any algorithm uses sorryAx | Public custom mathematical axiom names² |
|---|---|---:|---|---|---:|
| AMSGrad | passed | 366 | no | no | 0 |
| HeavyBallSecondRiddle | passed | 745 | no | no | 0 |
| Lion | passed | 332 | no | no | 0 |
| MARS | passed | 277 | no | no | 0 |
| NonconvexStochasticAcceleratedGD | passed | 261 | no | no | 0 |
| NonconvexStochasticBlockMirrorDescent | passed | 253 | no | no | 0 |
| NonconvexStochasticFirstOrder | passed | 275 | no | no | 0 |
| NonconvexStochasticMirrorDescent | passed | 694 | no | no | 0 |
| NonconvexVarianceReducedMirrorDescent | passed | 240 | no | no | 0 |
| PAGE | passed | 270 | no | no | 0 |
| PullWithMemoryDGD | passed | 269 | no | no | 0 |
| RSGF | passed | 256 | no | no | 0 |
| RandomGradientExtrapolation | passed | 569 | no | no | 0 |
| RandomPrimalDualGradient | passed | 569 | no | no | 0 |
| RandomizedAcceleratedProximalPoint | passed | 579 | no | no | 0 |
| SAM | passed | 562 | no | yes | 0 |
| SPIDER | passed | 371 | no | no | 0 |
| StochasticAcceleratedGradientDescent | passed | 474 | no | no | 0 |
| StochasticAcceleratedMirrorProx | passed | 343 | no | no | 0 |
| StochasticAcceleratedPrimalDual | passed | 785 | no | no | 0 |
| StochasticBlockMirrorDescent | passed | 255 | no | no | 0 |
| StochasticConditionalGradientSliding | passed | 344 | no | no | 0 |
| StochasticConvexConcaveSaddlePoint | passed | 420 | no | no | 0 |
| StochasticGradientSliding | passed | 1735 | no | no | 0 |
| StochasticMirrorDescent | passed | 358 | no | no | 0 |
| StochasticNonconvexCGSliding | passed | 277 | no | no | 0 |
| StochasticNonconvexConditionalGradient | passed | 1249 | no | no | 0 |
| StochasticRecursiveMomentum | passed | 664 | no | no | 0 |
| StochasticZerothOrder | passed | 457 | no | no | 0 |
| VarianceReducedAcceleratedGradientDescent | passed | 983 | no | no | 0 |
| VarianceReducedMirrorDescent | passed | 479 | no | no | 0 |
| RCDGD | passed | 397 | no | no | 0 |

¹ Includes private and generated theorems; not a count of distinct source theorems.

² Excludes standard foundations and compiler-generated `native_decide` assumptions.
The [JSON report](VERIFICATION.json) records source-hole locations and handwritten declarations; dependency results
are provided for checked developments. A dash denotes an unavailable result.

