import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Tactic

-- Generalization plan (G0):
-- concept/name: almost-everywhere measurability from a probability pushforward law; orig was `aemeasurable_of_map_eq_probability_law`
-- generality used: arbitrary measurable spaces `Ω` and `A`, source measure `P`, random variable `Y`, and target measure `μ` carrying only `[IsProbabilityMeasure μ]`; no topology, finite-dimensionality, independence, integrability, or optimization assumptions are used.
-- portable call pattern: any stochastic algorithm can derive a random variable's `AEMeasurable` property before applying map, integral, marginal, or independence APIs when its pushforward equals a named probability law; the source measure, map, and law change while the conclusion stays the same.
-- counterargument checked: Mathlib has the converse-shaped `AEMeasurable.of_map_ne_zero`, but it requires a separate nonzero proof; the probability-law specialization composes the map-zero contradiction with the law's unit mass and is a reusable Glue proof step rather than paper traceability or a caller-side expression.
-- coverage search: searched `aemeasurable map equals probability measure`, `map not aemeasurable probability`, and the exact statement across SOptLib, Staging, and Mathlib; the closest hits were `AEMeasurable.of_map_ne_zero` and unrelated map-law lemmas, so no full duplicate was found.
-- minimal hypotheses: measurable spaces and a probability-measure instance for `μ` are sufficient; the source measure need not be finite or a probability measure.

/-- A random variable whose pushforward equals a probability measure is almost everywhere measurable.

Layer: Glue | Gap: Level 0 (pushforward probability law to a.e. measurability)
Proof: argue by contradiction; a non-a.e.-measurable map pushes every source measure to zero, while the assumed probability law has total mass one, yielding an impossibility.
Source: Mathlib measure pushforward API (`Measure.map_of_not_aemeasurable`) and probability-measure total-mass facts
Used in: stochastic algorithm proofs that first establish a generated sample or branch map's named probability law and then need its a.e. measurability for map, integral, marginal, or independence transport
Book citation: book/research/PAGE.json#/algorithm_spec
Origin algorithm: Li, Bao, Zhang, and Richtárik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
theorem aemeasurable_of_map_eq_probability_measure
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    {P : MeasureTheory.Measure Ω} {Y : Ω → A} {μ : MeasureTheory.Measure A}
    [MeasureTheory.IsProbabilityMeasure μ]
    (hmap : MeasureTheory.Measure.map Y P = μ) :
    AEMeasurable Y P := by
  by_contra hnot
  have hzero : MeasureTheory.Measure.map Y P = 0 := by
    simpa using (MeasureTheory.Measure.map_of_not_aemeasurable hnot)
  have hμ_zero : μ Set.univ = (0 : ENNReal) := by
    rw [← hmap, hzero]
    simp
  have hμ_one : μ Set.univ = (1 : ENNReal) := by
    simp
  rw [hμ_one] at hμ_zero
  norm_num at hμ_zero
