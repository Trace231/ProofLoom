import SOptLib.Glue.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: finite product stopping tail probability bounded by a constant power; orig was optimization_min_tail_bound_of_one_run_markov
-- generality used: finite index and stopping types, an arbitrary measurable sample space, a PMF product law, an arbitrary s-finite sample measure, and pointwise fiber-product and one-coordinate ENNReal tail bounds
-- portable call pattern: independent multi-start and repeated-run proofs instantiate the same stopping-vector law and one-run tail estimate while changing the stopping PMF, sample law, event family, and constant
-- counterargument checked: not paper-local because the statement removes gradients, objectives, and RSGD data; not a duplicate because SOptLib has the equality to a product but not the uniform-bound-to-constant-power consequence
-- coverage search: queried "finite product probability all events bounded by power of one event bound", "PMF pi measure intersection events product probabilities", and "all coordinate tail probability product one coordinate bound constant power"; top relevant hits were pi_stopping_tail_probability_eq_product_of_nonStrict and pi_stopping_tail_probability_eq_product, which provide only the product equality
-- minimal hypotheses: the proof uses exactly finite types, the product stopping-law identity, the fiber factorization, s-finiteness for the product-measure expansion, and coordinate bounds; no optimization, convexity, finite-dimensional, or probability-measure assumptions are needed

/-- A finite product stopping law and uniform one-coordinate tail bound give a
constant-power all-coordinate tail bound.

If the stopping-vector PMF factors coordinatewise, each fixed-vector tail fiber
factors as a product of coordinate fibers, and every one-coordinate weighted
fiber mass is at most `c`, then the joint stopping/sample probability of the
all-coordinate event is at most `c ^ Fintype.card ι`.

Layer: Glue | Gap: Level 1 (finite product stopping-vector tail inequality)
Proof: reuse the finite product stopping-tail factorization theorem, then bound the resulting finite product coordinatewise by `c` and rewrite the constant product as a power.
Source: Mathlib probability mass functions, product measures, ENNReal finite products, and SOptLib finite stopping-tail factorization
Used in: repeated randomized stochastic-gradient optimization runs, where a one-run Markov stopping tail estimate is lifted to the all-runs minimum tail event
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, two-phase randomized stochastic gradient method -/
theorem pi_stopping_all_tail_le_const_pow_of_one_tail_bound
    {ι α Ω : Type*} [Fintype ι] [Fintype α]
    [MeasurableSpace (ι → α)] [MeasurableSingletonClass (ι → α)]
    [MeasurableSpace Ω]
    (p : PMF α) (q : PMF (ι → α)) (μ : Measure Ω) [SFinite μ]
    (A : (ι → α) → Set Ω) (B : ι → α → Set Ω) (c : ENNReal)
    (hq : ∀ R : ι → α, q R = ∏ i : ι, p (R i))
    (hfiber : ∀ R : ι → α, μ (A R) = ∏ i : ι, μ (B i (R i)))
    (hone : ∀ i : ι, (∑ a : α, p a * μ (B i a)) ≤ c) :
    (q.toMeasure.prod μ) {x : (ι → α) × Ω | x.2 ∈ A x.1} ≤
      c ^ Fintype.card ι := by
  classical
  let Pone : ι → ENNReal := fun i => ∑ a : α, p a * μ (B i a)
  have hprod_eq :
      (q.toMeasure.prod μ) {x : (ι → α) × Ω | x.2 ∈ A x.1} =
        ∏ i : ι, Pone i := by
    exact
      pi_stopping_tail_probability_eq_product_of_nonStrict
        (p := p) (q := q) (μ := μ)
        (Pall := (q.toMeasure.prod μ)
          {x : (ι → α) × Ω | x.2 ∈ A x.1})
        (Pone := Pone) (A := A) (B := B) rfl hq hfiber
        (by intro i; rfl)
  calc
    (q.toMeasure.prod μ) {x : (ι → α) × Ω | x.2 ∈ A x.1}
        = ∏ i : ι, Pone i := hprod_eq
    _ ≤ ∏ _i : ι, c := by
        exact Finset.prod_le_prod
          (by intro i _hi; exact bot_le)
          (by intro i _hi; exact hone i)
    _ = c ^ Fintype.card ι := by
        rw [Finset.prod_const, Finset.card_univ]
