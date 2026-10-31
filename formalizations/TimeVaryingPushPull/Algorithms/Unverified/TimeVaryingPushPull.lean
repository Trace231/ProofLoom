import Algorithms.Unverified.TimeVaryingPushPull.Part003

-- Aggregator for `Algorithms.Unverified.TimeVaryingPushPull`. Source declarations live under `TimeVaryingPushPull/`.

namespace Algorithms.Unverified.TimeVaryingPushPull

open MeasureTheory

/-- A selected family of generated Push--Pull problems, indexed so that `n`
corresponds exactly to the positive node count `n + 1`, together with the
scalar identifications used in Corollary 8.2. -/
def GeneratedCorollaryFamily
    (neff L Delta sigma transient : ℕ → ℝ)
    (setup : (n : ℕ) → Setup (Fin (n + 1)) ℝ) : Prop :=
  ∀ n : ℕ,
    neff n = (setup n).effectiveNodeCount ∧
      L n = (setup n).L ∧
        Delta n = (setup n).Delta ∧
          sigma n = (setup n).sigma ∧
            transient n = (setup n).theoremSevenOneTransientCoefficient

/-- Generated-process upper property used by the stochastic branch of
Corollary 8.2.  Unlike the scalar leading-term predicate, this statement
quantifies the source probability space and oracle law and bounds the actual
stationarity average of the generated constant-stepsize trajectory. -/
def GeneratedStochasticUpperProperty
    (neff L Delta sigma transient : ℕ → ℝ)
    (setup : (n : ℕ) → Setup (Fin (n + 1)) ℝ) : Prop :=
  GeneratedCorollaryFamily neff L Delta sigma transient setup ∧
    ∀ (n : ℕ) (Omega : Type*) [MeasurableSpace Omega]
      (mu : Measure Omega) [IsProbabilityMeasure mu]
      (oracle : Setup.OracleNoiseProcess Omega (Fin (n + 1)) ℝ),
      (setup n).StochasticOracleAssumptions mu oracle →
        ∀ horizon : ℕ, 1 ≤ horizon →
          ∃ alpha : ℝ,
            0 < alpha ∧ alpha ≤ (setup n).alphaMax ∧
              ((setup n).withStepsize alpha).stationarityAverage
                  mu oracle horizon ≤
                8 * sigma n *
                    Real.sqrt (L n * Delta n /
                      (neff n * (horizon : ℝ))) +
                  transient n / (horizon : ℝ)

/-- Theorem 7.1 supplies the generated upper property for every selected
source family. -/
theorem generatedStochasticUpperProperty_of_family
    {neff L Delta sigma transient : ℕ → ℝ}
    {setup : (n : ℕ) → Setup (Fin (n + 1)) ℝ}
    (hfamily : GeneratedCorollaryFamily neff L Delta sigma transient setup) :
    GeneratedStochasticUpperProperty neff L Delta sigma transient setup := by
  refine ⟨hfamily, ?_⟩
  intro n Omega _ mu _ oracle horacle horizon hhorizon
  rcases (setup n).horizonStepsize_pos_le_alphaMax horizon hhorizon with
    ⟨halpha_pos, halpha_le⟩
  refine ⟨(setup n).horizonStepsize horizon, halpha_pos, halpha_le, ?_⟩
  have hupper :=
    (setup n).horizon_stepsize_leading_and_transient_bounds
      mu oracle horizon hhorizon horacle
  rcases hfamily n with ⟨hneff, hL, hDelta, hsigma, htransient⟩
  simpa [Setup.stationarityAverage, hneff, hL, hDelta, hsigma, htransient]
    using hupper

/-- The source-mandated homogeneous quadratic test is run on the same network
as the corresponding upper-bound instance.  Besides the primitive schedules,
the network-derived gain data and every scalar used in Corollary 8.2 are
identified explicitly. -/
def GeneratedSameNetworkQuadraticRealization
    (setup quad : (n : ℕ) → Setup (Fin (n + 1)) ℝ) : Prop :=
  ∀ n : ℕ,
    (quad n).R = (setup n).R ∧
      (quad n).C = (setup n).C ∧
        (quad n).period = (setup n).period ∧
          (Finset.expect Finset.univ (fun r : Fin (quad n).period => Setup.rowSum ((quad n).influence r.1))) = (Finset.expect Finset.univ (fun r : Fin (setup n).period => Setup.rowSum ((setup n).influence r.1))) ∧
            (quad n).influenceSecondMoment =
                (setup n).influenceSecondMoment ∧
              (quad n).effectiveNodeCount =
                  (setup n).effectiveNodeCount ∧
                (quad n).L = (setup n).L ∧
                  (quad n).Delta = (setup n).Delta ∧
                    (quad n).sigma = (setup n).sigma

/-- Primitive data for the source-mandated quadratic tests at every
positive-noise index.  The same probability space may carry the whole family,
while each tested member has its own generated Setup and exact-noise oracle on
the upper instance's network.  The public criterion below separately requires
that these indices form an eventual tail. -/
def GeneratedQuadraticLowerFamily
    (neff L Delta sigma : ℕ → ℝ)
    (setup : (n : ℕ) → Setup (Fin (n + 1)) ℝ)
    (quad : (n : ℕ) → Setup (Fin (n + 1)) ℝ)
    {Omega : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (oracle : (n : ℕ) → Setup.OracleNoiseProcess Omega (Fin (n + 1)) ℝ) : Prop :=
  GeneratedSameNetworkQuadraticRealization setup quad ∧
    ∀ n : ℕ,
      0 < sigma n →
        neff n = (quad n).effectiveNodeCount ∧
        L n = (quad n).L ∧
          Delta n = (quad n).Delta ∧
            sigma n = (quad n).sigma ∧
              Setup.HomogeneousQuadraticComponents (Node := Fin (n + 1))
                (quad n) (L n) ∧
                (quad n).ExactVarianceIidAdditiveNoise mu (oracle n)

/-- Pointwise generated lower certification on the positive-noise indices.
Its asymptotic horizon is the argument of each residual and is deliberately
independent of the family index and of any selected schedule `T n`. -/
def GeneratedMatchingQuadraticLowerCertification
    (neff L Delta sigma : ℕ → ℝ)
    (setup : (n : ℕ) → Setup (Fin (n + 1)) ℝ)
    (quad : (n : ℕ) → Setup (Fin (n + 1)) ℝ)
    {Omega : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (oracle : (n : ℕ) → Setup.OracleNoiseProcess Omega (Fin (n + 1)) ℝ) : Prop :=
  GeneratedQuadraticLowerFamily neff L Delta sigma setup quad mu oracle ∧
    ∀ n : ℕ, 0 < sigma n →
      ∃ residual : ℕ → ℝ, Setup.LittleOInvSqrt residual ∧
        ∀ horizon : ℕ,
          (quad n).infConstantStepsizeStationarity mu (oracle n) horizon =
            sigma n * Real.sqrt
              (2 * L n * Delta n / (neff n * (horizon : ℝ))) +
              residual horizon

/-- The matching lower theorem derives, rather than assumes, every member's
generated infimum expansion. -/
theorem generatedMatchingQuadraticLowerCertification_of_family
    {neff L Delta sigma : ℕ → ℝ}
    {setup : (n : ℕ) → Setup (Fin (n + 1)) ℝ}
    {quad : (n : ℕ) → Setup (Fin (n + 1)) ℝ}
    {Omega : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (oracle : (n : ℕ) → Setup.OracleNoiseProcess Omega (Fin (n + 1)) ℝ)
    (hfamily :
      GeneratedQuadraticLowerFamily neff L Delta sigma setup quad mu oracle) :
    GeneratedMatchingQuadraticLowerCertification
      neff L Delta sigma setup quad mu oracle := by
  refine ⟨hfamily, ?_⟩
  intro n hsigmaPos
  rcases hfamily.2 n hsigmaPos with
    ⟨hneff, hL, hDelta, hsigma, hquad, hnoise⟩
  rcases Setup.MatchingQuadraticLowerBound
      (quad n) (L n) mu (oracle n) hquad hnoise with
    ⟨residual, hresidual, hexpansion⟩
  refine ⟨residual, hresidual, ?_⟩
  intro horizon
  rw [hexpansion horizon]
  unfold Setup.matchingQuadraticLeadingTerm
  rw [← hneff, ← hDelta, ← hsigma]

/-- The uniformly bounded `T⁻¹` transient is lower order than the
`((n+1)T)⁻¹ᐟ²` stochastic scale.  This squared, denominator-free formulation
is equivalent to saying that the squared ratio tends to zero, and avoids any
extra positivity assumption on the transient itself. -/
def GeneratedTransientLowerOrder
    (transient : ℕ → ℝ) (T : ℕ → ℕ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
    |transient n| ^ 2 * ((n + 1 : ℕ) : ℝ) ≤ epsilon * (T n : ℝ)

/-- Centralized-SGD-order upper clause on the generated arithmetic-average
stationarity itself.  All probability spaces and source-law oracles are
quantified, and the stepsize generates the trajectory being measured. -/
def GeneratedCentralizedStochasticUpperProperty
    (neff L Delta sigma transient : ℕ → ℝ) (T : ℕ → ℕ)
    (setup : (n : ℕ) → Setup (Fin (n + 1)) ℝ) : Prop :=
  GeneratedCorollaryFamily neff L Delta sigma transient setup ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ (Omega : Type*) [MeasurableSpace Omega]
        (mu : Measure Omega) [IsProbabilityMeasure mu]
        (oracle : Setup.OracleNoiseProcess Omega (Fin (n + 1)) ℝ),
        (setup n).StochasticOracleAssumptions mu oracle →
          ∃ alpha : ℝ,
            0 < alpha ∧ alpha ≤ (setup n).alphaMax ∧
              ((setup n).withStepsize alpha).stationarityAverage
                  mu oracle (T n) ≤
                C * sigma n * Real.sqrt
                    (L n * Delta n /
                      (((n + 1 : ℕ) : ℝ) * (T n : ℝ))) +
                  transient n / (T n : ℝ)

/-- Centralized-SGD-order performance of the actual generated quadratic
stationarity infimum.  There is one comparison constant for the family, while
the eventual horizon threshold may depend on the member.  Thus the horizon in
the matching expansion is independent of the selected schedule `T n`. -/
def GeneratedQuadraticCentralizedLowerProperty
    (neff L Delta sigma : ℕ → ℝ)
    (setup : (n : ℕ) → Setup (Fin (n + 1)) ℝ)
    (quad : (n : ℕ) → Setup (Fin (n + 1)) ℝ)
    {Omega : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (oracle : (n : ℕ) → Setup.OracleNoiseProcess Omega (Fin (n + 1)) ℝ) : Prop :=
  GeneratedQuadraticLowerFamily neff L Delta sigma setup quad mu oracle ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∃ horizon0 : ℕ, 1 ≤ horizon0 ∧ ∀ horizon : ℕ, horizon0 ≤ horizon →
        (quad n).infConstantStepsizeStationarity mu (oracle n) horizon ≤
          C * (sigma n * Real.sqrt
            (2 * L n * Delta n / ((n + 1 : ℕ) : ℝ))) *
              (Real.sqrt (horizon : ℝ))⁻¹

/-- Generated stochastic complexity assertion for Corollary 8.2.  Its upper
component is about the stationarity average of the generated arithmetic-average
trajectory.  Its necessary component is certified on actual generated
homogeneous-quadratic trajectories through their constant-stepsize stationarity
infima and per-instance little-o residuals. -/
def GeneratedStochasticNfoldComplexity
    (neff L Delta sigma transient : ℕ → ℝ) (T : ℕ → ℕ)
    (setup : (n : ℕ) → Setup (Fin (n + 1)) ℝ)
    (quad : (n : ℕ) → Setup (Fin (n + 1)) ℝ)
    {Omega : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (oracle : (n : ℕ) → Setup.OracleNoiseProcess Omega (Fin (n + 1)) ℝ) : Prop :=
  GeneratedCentralizedStochasticUpperProperty.{0}
      neff L Delta sigma transient T setup ∧
    GeneratedTransientLowerOrder transient T ∧
      GeneratedQuadraticCentralizedLowerProperty
        neff L Delta sigma setup quad mu oracle

theorem generatedTransientLowerOrder_of_uniformBound
    {L Delta sigma transient : ℕ → ℝ} {T : ℕ → ℕ}
    (hbounded : Setup.UniformlyBoundedCorollaryFamily L Delta sigma transient)
    (hT : Setup.TimeOverNodeDiverges T) :
    GeneratedTransientLowerOrder transient T := by
  rcases hbounded with ⟨C, hC, hbounded⟩
  intro epsilon hepsilon
  have hM : 0 ≤ C ^ 2 / epsilon :=
    div_nonneg (sq_nonneg C) hepsilon.le
  rcases hT (C ^ 2 / epsilon) hM with ⟨N0, hlarge⟩
  refine ⟨N0, ?_⟩
  intro n hn
  have habs : |transient n| ≤ C := (hbounded n).2.2.2.2.2.2
  have hsquare : |transient n| ^ 2 ≤ C ^ 2 := by
    nlinarith [abs_nonneg (transient n)]
  have hnpos : 0 ≤ (((n + 1 : ℕ) : ℝ)) := by positivity
  calc
    |transient n| ^ 2 * ((n + 1 : ℕ) : ℝ) ≤
        C ^ 2 * ((n + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hsquare hnpos
    _ = epsilon * ((C ^ 2 / epsilon) * ((n + 1 : ℕ) : ℝ)) := by
      field_simp [ne_of_gt hepsilon]
    _ ≤ epsilon * (T n : ℝ) :=
      mul_le_mul_of_nonneg_left (hlarge n hn) hepsilon.le

/-- At zero noise, Theorem 7.1 gives the generated centralized-form upper
stationarity clause without any effective-node scaling hypothesis: its
stochastic term vanishes and only the explicit transient remains.  This is an
original-object obstruction to cancelling `sigma` in the necessity argument,
but it is not by itself a counterexample to the source corollary because it
does not construct a family whose effective-node count fails to be
`Theta(n)`. -/
theorem generatedCentralizedStochasticUpperProperty_of_zeroNoise
    {neff L Delta sigma transient : ℕ → ℝ} {T : ℕ → ℕ}
    {setup : (n : ℕ) → Setup (Fin (n + 1)) ℝ}
    (hfamily : GeneratedCorollaryFamily neff L Delta sigma transient setup)
    (hzero : ∀ n : ℕ, sigma n = 0)
    (hT : Setup.TimeOverNodeDiverges T) :
    GeneratedCentralizedStochasticUpperProperty
      neff L Delta sigma transient T setup := by
  have hupper :
      GeneratedStochasticUpperProperty neff L Delta sigma transient setup :=
    generatedStochasticUpperProperty_of_family hfamily
  rcases hT 1 (by norm_num) with ⟨N0, hlarge⟩
  refine ⟨hfamily, 0, le_rfl, N0, ?_⟩
  intro n hn Omega _ mu _ oracle horacle
  have hTpos : (0 : ℝ) < (T n : ℝ) := by
    have hnOne : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    exact lt_of_lt_of_le hnOne (by simpa using hlarge n hn)
  have hTnat : 1 ≤ T n := by exact_mod_cast hTpos
  rcases hupper.2 n Omega mu oracle horacle (T n) hTnat with
    ⟨alpha, halphaPos, halphaMax, hstationarity⟩
  refine ⟨alpha, halphaPos, halphaMax, ?_⟩
  simpa [hzero n] using hstationarity

/- The zero-noise audit needs an original growing family, rather than a
scalar cancellation example.  The following period-two network is the first
primitive part of that construction.  At the even phase the push matrix has
one distinguished node, at the odd phase it is uniform, and the pull matrix
is uniform in both phases.  All entries remain positive, so this is an
admissible paper network for every positive node count. -/
private noncomputable def zeroNoiseUniformWeight (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ))⁻¹

private noncomputable def zeroNoiseSkewWeight
    (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  (1 / 2 : ℝ) * (if i = 0 then 1 else 0) +
    (1 / 2 : ℝ) * zeroNoiseUniformWeight n

private noncomputable def zeroNoiseCounterexamplePush
    (n t : ℕ) : NodeMatrix (Fin (n + 1)) :=
  fun _ j =>
    if t % 2 = 0 then zeroNoiseSkewWeight n j
    else zeroNoiseUniformWeight n

private noncomputable def zeroNoiseCounterexamplePull
    (n _t : ℕ) : NodeMatrix (Fin (n + 1)) :=
  fun _ _ => zeroNoiseUniformWeight n

private theorem zeroNoiseUniformWeight_pos (n : ℕ) :
    0 < zeroNoiseUniformWeight n := by
  unfold zeroNoiseUniformWeight
  positivity

private theorem zeroNoiseSkewWeight_pos
    (n : ℕ) (i : Fin (n + 1)) :
    0 < zeroNoiseSkewWeight n i := by
  unfold zeroNoiseSkewWeight
  have hu := zeroNoiseUniformWeight_pos n
  split_ifs <;> positivity

private theorem zeroNoiseUniformWeight_sum (n : ℕ) :
    ∑ _i : Fin (n + 1), zeroNoiseUniformWeight n = 1 := by
  unfold zeroNoiseUniformWeight
  simp
  exact mul_inv_cancel₀ (by positivity)

private theorem zeroNoiseSkewWeight_sum (n : ℕ) :
    ∑ i : Fin (n + 1), zeroNoiseSkewWeight n i = 1 := by
  classical
  unfold zeroNoiseSkewWeight
  rw [Finset.sum_add_distrib]
  simp
  unfold zeroNoiseUniformWeight
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  field_simp [ne_of_gt hn]
  norm_num
  ring

private theorem zeroNoiseCounterexamplePush_periodic (n t : ℕ) :
    zeroNoiseCounterexamplePush n (t + 2) =
      zeroNoiseCounterexamplePush n t := by
  have hmod : (t + 2) % 2 = t % 2 := by omega
  funext i j
  simp [zeroNoiseCounterexamplePush, hmod]

private theorem zeroNoiseCounterexample_network_specs (n : ℕ) :
    (∀ t : ℕ,
      RowStochastic (Node := Fin (n + 1))
        (zeroNoiseCounterexamplePush n t)) ∧
    (∀ t : ℕ,
      ColumnStochastic (Node := Fin (n + 1))
        (zeroNoiseCounterexamplePull n t)) ∧
    (∀ t : ℕ,
      PositiveDiagonal (Node := Fin (n + 1))
        (zeroNoiseCounterexamplePush n t)) ∧
    (∀ t : ℕ,
      PositiveDiagonal (Node := Fin (n + 1))
        (zeroNoiseCounterexamplePull n t)) ∧
    (∀ t : ℕ,
      PositiveEntriesLowerBounded (Node := Fin (n + 1))
        ((1 / 2 : ℝ) * zeroNoiseUniformWeight n)
        (zeroNoiseCounterexamplePush n t)) ∧
    (∀ t : ℕ,
      PositiveEntriesLowerBounded (Node := Fin (n + 1))
        ((1 / 2 : ℝ) * zeroNoiseUniformWeight n)
        (zeroNoiseCounterexamplePull n t)) ∧
    (∀ t : ℕ,
      StronglyConnectedPositiveGraph (Node := Fin (n + 1))
        (zeroNoiseCounterexamplePush n t)) ∧
    (∀ t : ℕ,
      StronglyConnectedPositiveGraph (Node := Fin (n + 1))
        (zeroNoiseCounterexamplePull n t)) := by
  classical
  have hu := zeroNoiseUniformWeight_pos n
  constructor
  · intro t
    constructor
    · intro i j
      unfold zeroNoiseCounterexamplePush
      split_ifs
      · exact (zeroNoiseSkewWeight_pos n j).le
      · exact hu.le
    · intro i
      unfold zeroNoiseCounterexamplePush
      split_ifs
      · exact zeroNoiseSkewWeight_sum n
      · exact zeroNoiseUniformWeight_sum n
  constructor
  · intro t
    constructor
    · intro i j
      exact hu.le
    · intro j
      exact zeroNoiseUniformWeight_sum n
  constructor
  · intro t i
    unfold zeroNoiseCounterexamplePush
    split_ifs
    · exact zeroNoiseSkewWeight_pos n i
    · exact hu
  constructor
  · intro t i
    exact hu
  constructor
  · intro t i j _hij
    unfold zeroNoiseCounterexamplePush
    split_ifs
    · unfold zeroNoiseSkewWeight
      split_ifs <;> nlinarith
    · nlinarith
  constructor
  · intro t i j _hij
    unfold zeroNoiseCounterexamplePull
    nlinarith
  constructor
  · intro t i j
    exact Relation.ReflTransGen.single (by
      unfold zeroNoiseCounterexamplePush
      split_ifs
      · exact zeroNoiseSkewWeight_pos n j
      · exact hu)
  · intro t i j
    exact Relation.ReflTransGen.single (by
      unfold zeroNoiseCounterexamplePull
      exact hu)

/- A genuine generated zero-noise problem on the network above.  All
component objectives are the same quadratic, so the objective and its gap do
not change when the node count grows.  A later scaling step will shrink this
gap to control the explicit Theorem 7.1 transient without changing the
network or its effective-node count. -/
private noncomputable def zeroNoiseCounterexampleBaseSetup (n : ℕ) :
    Setup (Fin (n + 1)) ℝ where
  componentObjective := fun _ x => x ^ 2 / 2
  x0 := 1
  L := 1
  L_pos := by norm_num
  component_lsmooth := by
    intro i
    constructor
    · fun_prop
    · intro x y
      have hgradient (z : ℝ) :
          gradient (fun w : ℝ => w ^ 2 / 2) z = z := by
        have h :=
          hasGradientAt_const_mul_norm_sub_sq_centered (E := ℝ) 1 0 z
        simpa [Real.norm_eq_abs, sq_abs, sub_zero, smul_eq_mul,
          div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          h.gradient
      rw [hgradient x, hgradient y]
      simp
  objective_bddBelow := by
    refine ⟨0, ?_⟩
    rintro y ⟨x, rfl⟩
    simp [finiteAverageObjectiveOf, SOptLib.finiteUniformAverage]
    positivity
  Delta_pos := by
    have hobjective :
        finiteAverageObjectiveOf (Node := Fin (n + 1)) (E := ℝ)
            (fun _ x => x ^ 2 / 2) = fun x : ℝ => x ^ 2 / 2 := by
      funext x
      simp [finiteAverageObjectiveOf, SOptLib.finiteUniformAverage]
      field_simp
    have hinf :
        SOptLib.objectiveInfimumValue (Set.univ : Set ℝ)
            (fun x : ℝ => x ^ 2 / 2) = 0 := by
      unfold SOptLib.objectiveInfimumValue
      apply (show IsLeast ((fun x : ℝ => x ^ 2 / 2) '' Set.univ) 0 by
        constructor
        · exact ⟨0, Set.mem_univ 0, by norm_num⟩
        · rintro y ⟨x, _hx, rfl⟩
          positivity).csInf_eq
    rw [hobjective, hinf]
    norm_num
  sigma := 0
  sigma_nonneg := by norm_num
  alpha := 1
  period := 2
  period_pos := by norm_num
  minPositiveWeight := (1 / 2 : ℝ) * zeroNoiseUniformWeight n
  minPositiveWeight_pos := by
    exact mul_pos (by norm_num) (zeroNoiseUniformWeight_pos n)
  R := zeroNoiseCounterexamplePush n
  C := zeroNoiseCounterexamplePull n
  R_periodic := zeroNoiseCounterexamplePush_periodic n
  C_periodic := by intros; rfl
  R_rowStochastic := (zeroNoiseCounterexample_network_specs n).1
  C_columnStochastic := (zeroNoiseCounterexample_network_specs n).2.1
  R_positiveDiagonal := (zeroNoiseCounterexample_network_specs n).2.2.1
  C_positiveDiagonal := (zeroNoiseCounterexample_network_specs n).2.2.2.1
  R_positiveEntriesLowerBounded :=
    (zeroNoiseCounterexample_network_specs n).2.2.2.2.1
  C_positiveEntriesLowerBounded :=
    (zeroNoiseCounterexample_network_specs n).2.2.2.2.2.1
  R_stronglyConnected :=
    (zeroNoiseCounterexample_network_specs n).2.2.2.2.2.2.1
  C_stronglyConnected :=
    (zeroNoiseCounterexample_network_specs n).2.2.2.2.2.2.2

private theorem zeroNoiseCounterexampleBaseSetup_scalar_data (n : ℕ) :
    (zeroNoiseCounterexampleBaseSetup n).L = 1 ∧
      (zeroNoiseCounterexampleBaseSetup n).Delta = 1 / 2 ∧
        (zeroNoiseCounterexampleBaseSetup n).sigma = 0 := by
  constructor
  · rfl
  constructor
  · have hobjective :
        (zeroNoiseCounterexampleBaseSetup n).objective =
          fun x : ℝ => x ^ 2 / 2 := by
      funext x
      unfold Setup.objective finiteAverageObjectiveOf
      simp [zeroNoiseCounterexampleBaseSetup,
        SOptLib.finiteUniformAverage]
      field_simp
    have hinf :
        (zeroNoiseCounterexampleBaseSetup n).objectiveInfimum = 0 := by
      unfold Setup.objectiveInfimum SOptLib.objectiveInfimumValue
      rw [hobjective]
      apply (show IsLeast ((fun x : ℝ => x ^ 2 / 2) '' Set.univ) 0 by
        constructor
        · exact ⟨0, Set.mem_univ 0, by norm_num⟩
        · rintro y ⟨x, _hx, rfl⟩
          positivity).csInf_eq
    unfold Setup.Delta
    rw [hobjective, hinf]
    simp [zeroNoiseCounterexampleBaseSetup]
  · simp [zeroNoiseCounterexampleBaseSetup]

/- Rescale only the common initial point.  The scale is chosen from the exact
transient of the unit-initialized problem; it is strictly positive and leaves
all network objects unchanged. -/
private noncomputable def zeroNoiseCounterexampleScale (n : ℕ) : ℝ :=
  (1 + |(zeroNoiseCounterexampleBaseSetup n).theoremSevenOneTransientCoefficient|)⁻¹

private theorem zeroNoiseCounterexampleScale_pos (n : ℕ) :
    0 < zeroNoiseCounterexampleScale n := by
  unfold zeroNoiseCounterexampleScale
  positivity

private noncomputable def zeroNoiseCounterexampleSetup (n : ℕ) :
    Setup (Fin (n + 1)) ℝ :=
  { zeroNoiseCounterexampleBaseSetup n with
    x0 := zeroNoiseCounterexampleScale n
    Delta_pos := by
      have hscale := zeroNoiseCounterexampleScale_pos n
      have hobjective :
          finiteAverageObjectiveOf (Node := Fin (n + 1)) (E := ℝ)
              (fun _ x => x ^ 2 / 2) = fun x : ℝ => x ^ 2 / 2 := by
        funext x
        simp [finiteAverageObjectiveOf, SOptLib.finiteUniformAverage]
        field_simp
      have hinf :
          SOptLib.objectiveInfimumValue (Set.univ : Set ℝ)
              (fun x : ℝ => x ^ 2 / 2) = 0 := by
        unfold SOptLib.objectiveInfimumValue
        apply (show IsLeast ((fun x : ℝ => x ^ 2 / 2) '' Set.univ) 0 by
          constructor
          · exact ⟨0, Set.mem_univ 0, by norm_num⟩
          · rintro y ⟨x, _hx, rfl⟩
            positivity).csInf_eq
      change 0 <
        finiteAverageObjectiveOf (Node := Fin (n + 1)) (E := ℝ)
            (fun _ x => x ^ 2 / 2) (zeroNoiseCounterexampleScale n) -
          SOptLib.objectiveInfimumValue (Set.univ : Set ℝ)
            (finiteAverageObjectiveOf (Node := Fin (n + 1)) (E := ℝ)
              (fun _ x => x ^ 2 / 2))
      rw [hobjective, hinf]
      simpa using
        (div_pos (sq_pos_of_pos hscale) (by norm_num : (0 : ℝ) < 2)) }

private theorem zeroNoiseCounterexampleSetup_scalar_data (n : ℕ) :
    (zeroNoiseCounterexampleSetup n).L = 1 ∧
      (zeroNoiseCounterexampleSetup n).Delta =
          zeroNoiseCounterexampleScale n ^ 2 / 2 ∧
        (zeroNoiseCounterexampleSetup n).sigma = 0 := by
  constructor
  · rfl
  constructor
  · have hobjective :
        (zeroNoiseCounterexampleSetup n).objective =
          fun x : ℝ => x ^ 2 / 2 := by
      funext x
      unfold Setup.objective finiteAverageObjectiveOf
      simp [zeroNoiseCounterexampleSetup,
        zeroNoiseCounterexampleBaseSetup,
        SOptLib.finiteUniformAverage]
      field_simp
    have hinf :
        (zeroNoiseCounterexampleSetup n).objectiveInfimum = 0 := by
      unfold Setup.objectiveInfimum SOptLib.objectiveInfimumValue
      rw [hobjective]
      apply (show IsLeast ((fun x : ℝ => x ^ 2 / 2) '' Set.univ) 0 by
        constructor
        · exact ⟨0, Set.mem_univ 0, by norm_num⟩
        · rintro y ⟨x, _hx, rfl⟩
          positivity).csInf_eq
    unfold Setup.Delta
    rw [hobjective, hinf]
    simp [zeroNoiseCounterexampleSetup]
  · simp [zeroNoiseCounterexampleSetup,
      zeroNoiseCounterexampleBaseSetup]

private noncomputable def zeroNoiseCounterexamplePhaseWeight
    (n t : ℕ) : RowVector (Fin (n + 1)) :=
  fun i =>
    if t % 2 = 0 then zeroNoiseSkewWeight n i
    else zeroNoiseUniformWeight n

private theorem zeroNoiseCounterexamplePhaseWeight_sum (n t : ℕ) :
    Setup.rowSum (Node := Fin (n + 1))
      (zeroNoiseCounterexamplePhaseWeight n t) = 1 := by
  unfold Setup.rowSum zeroNoiseCounterexamplePhaseWeight
  split_ifs
  · exact zeroNoiseSkewWeight_sum n
  · exact zeroNoiseUniformWeight_sum n

private theorem zeroNoiseCounterexamplePhaseWeight_pos
    (n t : ℕ) (i : Fin (n + 1)) :
    0 < zeroNoiseCounterexamplePhaseWeight n t i := by
  unfold zeroNoiseCounterexamplePhaseWeight
  split_ifs
  · exact zeroNoiseSkewWeight_pos n i
  · exact zeroNoiseUniformWeight_pos n

private theorem zeroNoiseCounterexamplePhaseWeight_periodic (n t : ℕ) :
    zeroNoiseCounterexamplePhaseWeight n (t + 2) =
      zeroNoiseCounterexamplePhaseWeight n t := by
  have hmod : (t + 2) % 2 = t % 2 := by omega
  funext i
  simp [zeroNoiseCounterexamplePhaseWeight, hmod]

private theorem zeroNoiseCounterexampleBaseSetup_perron (n : ℕ) :
    (∀ t : ℕ,
      (zeroNoiseCounterexampleBaseSetup n).perronLeft t =
        zeroNoiseCounterexamplePhaseWeight n t) ∧
    (∀ t : ℕ,
      (zeroNoiseCounterexampleBaseSetup n).perronRight t =
        fun _ => zeroNoiseUniformWeight n) := by
  classical
  let setup := zeroNoiseCounterexampleBaseSetup n
  let candidate :
      (ℕ → RowVector (Fin (n + 1))) ×
        (ℕ → RowVector (Fin (n + 1))) :=
    (zeroNoiseCounterexamplePhaseWeight n,
      fun _ _ => zeroNoiseUniformWeight n)
  have hequations : setup.PerronSequencesEquations candidate := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t j
      unfold Setup.rowMulMatrix
      change
        (∑ i : Fin (n + 1),
          zeroNoiseCounterexamplePhaseWeight n (t + 1) i *
            zeroNoiseCounterexamplePhaseWeight n t j) =
          zeroNoiseCounterexamplePhaseWeight n t j
      rw [← Finset.sum_mul]
      rw [show (∑ i : Fin (n + 1),
          zeroNoiseCounterexamplePhaseWeight n (t + 1) i) = 1 by
        simpa [Setup.rowSum] using
          zeroNoiseCounterexamplePhaseWeight_sum n (t + 1)]
      simp
    · exact zeroNoiseCounterexamplePhaseWeight_sum n
    · intro t i
      unfold Setup.matrixMulVector
      change
        (∑ _j : Fin (n + 1),
          zeroNoiseUniformWeight n * zeroNoiseUniformWeight n) =
          zeroNoiseUniformWeight n
      rw [← Finset.mul_sum]
      rw [zeroNoiseUniformWeight_sum n]
      simp
    · intro t
      exact zeroNoiseUniformWeight_sum n
  have hpositivePeriodic :
      setup.PerronSequencesPositivePeriodic candidate := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact zeroNoiseCounterexamplePhaseWeight_pos n
    · intro t i
      exact zeroNoiseUniformWeight_pos n
    · intro t
      exact zeroNoiseCounterexamplePhaseWeight_periodic n t
    · intro t
      rfl
  have hcandidate : candidate = setup.perronSequences :=
    setup.perronSequences_unique candidate hequations hpositivePeriodic
  constructor
  · intro t
    have hleft := congrArg (fun sequences => sequences.1 t) hcandidate
    simpa [candidate, setup, Setup.perronLeft] using hleft.symm
  · intro t
    have hright := congrArg (fun sequences => sequences.2 t) hcandidate
    simpa [candidate, setup, Setup.perronRight] using hright.symm

private theorem zeroNoiseCounterexampleSetup_perronRight (n t : ℕ) :
    (zeroNoiseCounterexampleSetup n).perronRight t =
      fun _ => zeroNoiseUniformWeight n := by
  let scaled := zeroNoiseCounterexampleSetup n
  let base := zeroNoiseCounterexampleBaseSetup n
  have hperron : scaled.perronSequences = base.perronSequences := by
    apply base.perronSequences_unique scaled.perronSequences
    · simpa [scaled, base, zeroNoiseCounterexampleSetup,
        Setup.PerronSequencesEquations] using scaled.perronSequences_spec.1
    · simpa [scaled, base, zeroNoiseCounterexampleSetup,
        Setup.PerronSequencesPositivePeriodic] using
          scaled.perronSequences_spec.2.1
  have hright : scaled.perronRight t = base.perronRight t := by
    unfold Setup.perronRight
    exact congrArg (fun seqs => seqs.2 t) hperron
  rw [hright, (zeroNoiseCounterexampleBaseSetup_perron n).2 t]

private theorem zeroNoiseCounterexampleSetup_initialGradientHeterogeneity_zero
    (n : ℕ) :
    (zeroNoiseCounterexampleSetup n).initialGradientHeterogeneity = 0 := by
  have hgradient (z : ℝ) :
      gradient (fun w : ℝ => w ^ 2 / 2) z = z := by
    have h := hasGradientAt_const_mul_norm_sub_sq_centered (E := ℝ) 1 0 z
    simpa [Real.norm_eq_abs, sq_abs, sub_zero, smul_eq_mul,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h.gradient
  unfold Setup.initialGradientHeterogeneity
    FiniteNetwork.initialGradientHeterogeneity
    SOptLib.dependentProductNormSq FiniteNetwork.perronResidual
    Setup.gradientTable Setup.componentGradient Setup.initialPrimal
  rw [zeroNoiseCounterexampleSetup_perronRight n 0]
  have hsum :
      (∑ _j : Fin (n + 1), (zeroNoiseCounterexampleSetup n).x0) =
        ((n + 1 : ℕ) : ℝ) * (zeroNoiseCounterexampleSetup n).x0 := by
    simp
  simp_rw [show (zeroNoiseCounterexampleSetup n).componentObjective =
      fun (_ : Fin (n + 1)) (x : ℝ) => x ^ 2 / 2 by rfl]
  simp_rw [hgradient]
  have huniform :
      zeroNoiseUniformWeight n * ((n + 1 : ℕ) : ℝ) = 1 := by
    unfold zeroNoiseUniformWeight
    exact inv_mul_cancel₀ (by positivity)
  have hcenter :
      (zeroNoiseCounterexampleSetup n).x0 -
          zeroNoiseUniformWeight n *
            (((n + 1 : ℕ) : ℝ) *
              (zeroNoiseCounterexampleSetup n).x0) = 0 := by
    rw [← mul_assoc, huniform]
    simp
  simp_rw [hsum, smul_eq_mul, hcenter]
  simp

private theorem zeroNoiseCounterexampleBaseSetup_initialGradientHeterogeneity_zero
    (n : ℕ) :
    (zeroNoiseCounterexampleBaseSetup n).initialGradientHeterogeneity = 0 := by
  have hgradient (z : ℝ) :
      gradient (fun w : ℝ => w ^ 2 / 2) z = z := by
    have h := hasGradientAt_const_mul_norm_sub_sq_centered (E := ℝ) 1 0 z
    simpa [Real.norm_eq_abs, sq_abs, sub_zero, smul_eq_mul,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h.gradient
  unfold Setup.initialGradientHeterogeneity
    FiniteNetwork.initialGradientHeterogeneity
    SOptLib.dependentProductNormSq FiniteNetwork.perronResidual
    Setup.gradientTable Setup.componentGradient Setup.initialPrimal
  rw [(zeroNoiseCounterexampleBaseSetup_perron n).2 0]
  have hsum :
      (∑ _j : Fin (n + 1), (zeroNoiseCounterexampleBaseSetup n).x0) =
        ((n + 1 : ℕ) : ℝ) *
          (zeroNoiseCounterexampleBaseSetup n).x0 := by
    simp
  simp_rw [show (zeroNoiseCounterexampleBaseSetup n).componentObjective =
      fun (_ : Fin (n + 1)) (x : ℝ) => x ^ 2 / 2 by rfl]
  simp_rw [hgradient]
  have huniform :
      zeroNoiseUniformWeight n * ((n + 1 : ℕ) : ℝ) = 1 := by
    unfold zeroNoiseUniformWeight
    exact inv_mul_cancel₀ (by positivity)
  have hcenter :
      (zeroNoiseCounterexampleBaseSetup n).x0 -
          zeroNoiseUniformWeight n *
            (((n + 1 : ℕ) : ℝ) *
              (zeroNoiseCounterexampleBaseSetup n).x0) = 0 := by
    rw [← mul_assoc, huniform]
    simp
  simp_rw [hsum, smul_eq_mul, hcenter]
  simp

private theorem zeroNoiseCounterexampleSetup_transient_network_data (n : ℕ) :
    (zeroNoiseCounterexampleSetup n).alphaMax =
        (zeroNoiseCounterexampleBaseSetup n).alphaMax ∧
      (zeroNoiseCounterexampleSetup n).theoremSevenOnePreRateA =
        (zeroNoiseCounterexampleBaseSetup n).theoremSevenOnePreRateA ∧
      (zeroNoiseCounterexampleSetup n).theoremSevenOnePreRateD =
        (zeroNoiseCounterexampleBaseSetup n).theoremSevenOnePreRateD ∧
      (zeroNoiseCounterexampleSetup n).blockGain =
        (zeroNoiseCounterexampleBaseSetup n).blockGain ∧
      (Finset.expect Finset.univ (fun r : Fin (zeroNoiseCounterexampleSetup n).period => Setup.rowSum ((zeroNoiseCounterexampleSetup n).influence r.1))) =
        (Finset.expect Finset.univ (fun r : Fin (zeroNoiseCounterexampleBaseSetup n).period => Setup.rowSum ((zeroNoiseCounterexampleBaseSetup n).influence r.1))) ∧
      (zeroNoiseCounterexampleSetup n).influenceSecondMoment =
        (zeroNoiseCounterexampleBaseSetup n).influenceSecondMoment := by
  let scaled := zeroNoiseCounterexampleSetup n
  let base := zeroNoiseCounterexampleBaseSetup n
  have hperiod : scaled.period = base.period := rfl
  have hL : scaled.L = base.L := rfl
  have hperron : scaled.perronSequences = base.perronSequences := by
    apply base.perronSequences_unique scaled.perronSequences
    · simpa [scaled, base, zeroNoiseCounterexampleSetup,
        Setup.PerronSequencesEquations] using scaled.perronSequences_spec.1
    · simpa [scaled, base, zeroNoiseCounterexampleSetup,
        Setup.PerronSequencesPositivePeriodic] using
          scaled.perronSequences_spec.2.1
  have hleft (t : ℕ) : scaled.perronLeft t = base.perronLeft t := by
    unfold Setup.perronLeft
    exact congrArg (fun seqs => seqs.1 t) hperron
  have hright (t : ℕ) : scaled.perronRight t = base.perronRight t := by
    unfold Setup.perronRight
    exact congrArg (fun seqs => seqs.2 t) hperron
  have hpullLift (t j : ℕ) :
      scaled.pullLiftProduct t j = base.pullLiftProduct t j := by
    induction j with
    | zero => rfl
    | succ j ih =>
        simp only [Setup.pullLiftProduct]
        rw [ih]
        rfl
  have hcorrectedSeries (t j : ℕ)
      (W : ZeroSumState (Fin (n + 1)) ℝ) :
      scaled.correctedLiftSeriesTerm t j W =
        base.correctedLiftSeriesTerm t j W := by
    rw [scaled.correctedLiftSeriesTerm_eq_weightedState,
      base.correctedLiftSeriesTerm_eq_weightedState, hleft, hpullLift]
  have hcorrected (t : ℕ) (W : ZeroSumState (Fin (n + 1)) ℝ) :
      scaled.correctedLift t W = base.correctedLift t W := by
    unfold Setup.correctedLift
    apply tsum_congr
    intro j
    exact hcorrectedSeries t j W
  have hcorrectedNorm :
      scaled.correctedLiftNormZero = base.correctedLiftNormZero := by
    unfold Setup.correctedLiftNormZero Setup.correctedLiftOperatorNorm
    congr 1
  have hpullWindow (r j : ℕ) :
      scaled.pullWindowProduct r j = base.pullWindowProduct r j := by
    induction j with
    | zero => rfl
    | succ j ih =>
        simp only [Setup.pullWindowProduct]
        rw [ih]
        rfl
  have hC : scaled.C = base.C := by rfl
  have hinfluenceSeries (r j : ℕ) :
      scaled.influenceSeriesTerm r j = base.influenceSeriesTerm r j := by
    classical
    unfold Setup.influenceSeriesTerm
    simp only [FiniteNetwork.periodicInfluenceSeriesTerm_def, hleft, hC]
  have hinfluence (r : ℕ) : scaled.influence r = base.influence r := by
    unfold Setup.influence
    rw [hleft]
    congr 1
  have hinfluenceGain : (Finset.expect Finset.univ (fun r : Fin scaled.period => Setup.rowSum (scaled.influence r.1))) = (Finset.expect Finset.univ (fun r : Fin base.period => Setup.rowSum (base.influence r.1))) := by
    rw [hperiod]
    simp_rw [hinfluence] <;> rfl
  have hinfluenceSecondMoment :
      scaled.influenceSecondMoment = base.influenceSecondMoment := by
    unfold Setup.influenceSecondMoment
    rw [hperiod]
    congr 1
  have hblockGain : scaled.blockGain = base.blockGain := by
    unfold Setup.blockGain
    rw [hperiod]
    congr 1
  have hcontractionDelta :
      scaled.contractionDelta = base.contractionDelta := by rfl
  have hcontractionRate :
      scaled.contractionRate = base.contractionRate := by
    unfold Setup.contractionRate
    rw [hcontractionDelta]
  have hcolumnContraction :
      scaled.columnContractionConstant = base.columnContractionConstant := by
    unfold Setup.columnContractionConstant
    rw [hcontractionDelta]
  have hrowContraction :
      scaled.rowContractionConstant = base.rowContractionConstant := by
    unfold Setup.rowContractionConstant
    rw [hcontractionDelta]
  have hpullDeviation :
      scaled.pullDeviationNormMax = base.pullDeviationNormMax := by rfl
  have hpushDeviation :
      scaled.pushDeviationNormMax = base.pushDeviationNormMax := by rfl
  have hresidualMatrix (t : ℕ) :
      scaled.perronResidualMatrix t = base.perronResidualMatrix t := by
    unfold Setup.perronResidualMatrix
    rw [hright]
  have hresidualMax :
      scaled.perronResidualNormMax = base.perronResidualNormMax := by
    unfold Setup.perronResidualNormMax Setup.periodMax
    congr 1
  have hrightMax :
      scaled.perronRightNormMax = base.perronRightNormMax := by
    unfold Setup.perronRightNormMax Setup.periodMax
    congr 1
  have hprojectedRightMax :
      scaled.projectedPerronRightNormMax =
        base.projectedPerronRightNormMax := by
    unfold Setup.projectedPerronRightNormMax Setup.periodMax
    congr 1
  have hhybrid :
      scaled.hybridWeightDeviationNorm = base.hybridWeightDeviationNorm := by
    unfold Setup.hybridWeightDeviationNorm
    rw [hleft]
  have hthetaInitial :
      scaled.thetaInitialConstant = base.thetaInitialConstant := by
    unfold Setup.thetaInitialConstant
    rw [hcolumnContraction, hcontractionRate]
  have hthetaDisplacement :
      scaled.thetaDisplacementConstant = base.thetaDisplacementConstant := by
    unfold Setup.thetaDisplacementConstant
    rw [hcolumnContraction, hresidualMax, hcontractionRate]
  have hjointNoise :
      scaled.jointNoiseResidualConstant = base.jointNoiseResidualConstant := by
    unfold Setup.jointNoiseResidualConstant
    rw [hcolumnContraction, hpullDeviation, hcontractionRate]
  have hsectionSixGradientResponseFormula :
      scaled.sectionSixGradientResponseFormula =
        base.sectionSixGradientResponseFormula := by
    unfold Setup.sectionSixGradientResponseFormula
    rw [hrowContraction, hcontractionRate]
  have hprojectedTrackerGradient :
      scaled.projectedTrackerGradientCoefficient =
        base.projectedTrackerGradientCoefficient := by
    unfold Setup.projectedTrackerGradientCoefficient
    rw [hprojectedRightMax, hperiod]
  have hprojectedTrackerDisplacement :
      scaled.projectedTrackerDisplacementCoefficient =
        base.projectedTrackerDisplacementCoefficient := by
    unfold Setup.projectedTrackerDisplacementCoefficient
    rw [hthetaDisplacement, hprojectedRightMax, hperiod]
  have hprojectedTrackerConsensus :
      scaled.projectedTrackerConsensusCoefficient =
        base.projectedTrackerConsensusCoefficient := by
    unfold Setup.projectedTrackerConsensusCoefficient
    rw [hprojectedRightMax]
  have hprojectedTrackerNoise :
      scaled.projectedTrackerNoiseCoefficient =
        base.projectedTrackerNoiseCoefficient := by
    unfold Setup.projectedTrackerNoiseCoefficient
    rw [hjointNoise]
  have hunprojectedTrackerGradient :
      scaled.unprojectedTrackerGradientCoefficient =
        base.unprojectedTrackerGradientCoefficient := by
    unfold Setup.unprojectedTrackerGradientCoefficient
    rw [hrightMax, hperiod]
  have hunprojectedTrackerDisplacement :
      scaled.unprojectedTrackerDisplacementCoefficient =
        base.unprojectedTrackerDisplacementCoefficient := by
    unfold Setup.unprojectedTrackerDisplacementCoefficient
    rw [hthetaDisplacement, hrightMax, hperiod]
  have hunprojectedTrackerConsensus :
      scaled.unprojectedTrackerConsensusCoefficient =
        base.unprojectedTrackerConsensusCoefficient := by
    unfold Setup.unprojectedTrackerConsensusCoefficient
    rw [hrightMax]
  have hunprojectedTrackerNoise :
      scaled.unprojectedTrackerNoiseCoefficient =
        base.unprojectedTrackerNoiseCoefficient := by
    unfold Setup.unprojectedTrackerNoiseCoefficient
    rw [hjointNoise]
  have hsectionSixLambdaQFormula :
      scaled.sectionSixLambdaQFormula = base.sectionSixLambdaQFormula := by
    unfold Setup.sectionSixLambdaQFormula
    rw [hpushDeviation, hunprojectedTrackerConsensus]
  have hsectionSixStabilityConstants :
      scaled.sectionSixStabilityConstants =
        base.sectionSixStabilityConstants := by
    funext r
    unfold Setup.sectionSixStabilityConstants
    split_ifs <;>
      simp only [hsectionSixLambdaQFormula, hsectionSixGradientResponseFormula,
        hprojectedTrackerConsensus, hunprojectedTrackerDisplacement,
        hprojectedTrackerDisplacement]
  have halphaStable : scaled.alphaStable = base.alphaStable := by
    unfold Setup.alphaStable
    rw [hsectionSixStabilityConstants]
    rfl
  have hsectionSixLambdaQ :
      scaled.sectionSixLambdaQ = base.sectionSixLambdaQ := by
    exact hsectionSixLambdaQFormula
  have hsectionSixGradientResponse :
      scaled.sectionSixGradientResponse = base.sectionSixGradientResponse := by
    exact hsectionSixGradientResponseFormula
  have hfinalDisplacementGradient :
      scaled.finalDisplacementGradientConstant =
        base.finalDisplacementGradientConstant := by
    unfold Setup.finalDisplacementGradientConstant
    rw [hsectionSixLambdaQ, hsectionSixGradientResponse,
      hprojectedTrackerGradient, hunprojectedTrackerGradient]
  have hfinalDisplacementNoise :
      scaled.finalDisplacementNoiseConstant =
        base.finalDisplacementNoiseConstant := by
    unfold Setup.finalDisplacementNoiseConstant
    rw [hsectionSixLambdaQ, hsectionSixGradientResponse,
      hprojectedTrackerNoise, hunprojectedTrackerNoise]
  have hfinalConsensusGradient :
      scaled.finalConsensusGradientConstant =
        base.finalConsensusGradientConstant := by
    unfold Setup.finalConsensusGradientConstant
    rw [hsectionSixGradientResponse, hprojectedTrackerGradient,
      hprojectedTrackerDisplacement, hfinalDisplacementGradient]
  have hfinalConsensusNoise :
      scaled.finalConsensusNoiseConstant =
        base.finalConsensusNoiseConstant := by
    unfold Setup.finalConsensusNoiseConstant
    rw [hsectionSixGradientResponse, hprojectedTrackerNoise,
      hprojectedTrackerDisplacement, hfinalDisplacementNoise]
  have hrhoInitial : scaled.rhoInitialConstant = base.rhoInitialConstant := by
    unfold Setup.rhoInitialConstant
    rw [hcorrectedNorm, hcolumnContraction, hcontractionRate]
  have hrhoDisplacement :
      scaled.rhoDisplacementConstant = base.rhoDisplacementConstant := by
    unfold Setup.rhoDisplacementConstant
    rw [hcorrectedNorm, hcolumnContraction, hresidualMax,
      hcontractionRate, hresidualMatrix, hperiod]
  have hphaseConsensus :
      scaled.phaseConsensusCoefficient = base.phaseConsensusCoefficient := by
    unfold Setup.phaseConsensusCoefficient
    rw [hinfluenceGain, hperiod]
  have hcentered (r : ℕ) :
      scaled.centeredInfluence r = base.centeredInfluence r := by
    unfold Setup.centeredInfluence
    rw [hinfluence, hinfluenceGain]
  have hpartial (r : ℕ) :
      scaled.influencePartialSum r = base.influencePartialSum r := by
    unfold Setup.influencePartialSum
    apply Finset.sum_congr rfl
    intro j _hj
    exact hcentered j
  have habel :
      scaled.influenceAbelConstant = base.influenceAbelConstant := by
    unfold Setup.influenceAbelConstant
    apply Finset.sum_congr rfl
    intro r _hr
    rw [hpartial]
  have hphaseDisplacement :
      scaled.phaseDisplacementCoefficient =
        base.phaseDisplacementCoefficient := by
    unfold Setup.phaseDisplacementCoefficient
    rw [hinfluenceGain, habel, hperiod]
  have hstateFeedbackConsensus :
      scaled.stateFeedbackConsensusCoefficient =
        base.stateFeedbackConsensusCoefficient := by
    unfold Setup.stateFeedbackConsensusCoefficient
    rw [hblockGain, hhybrid, hphaseConsensus]
  have hstateFeedbackDisplacement :
      scaled.stateFeedbackDisplacementCoefficient =
        base.stateFeedbackDisplacementCoefficient := by
    unfold Setup.stateFeedbackDisplacementCoefficient
    rw [hphaseDisplacement, hrhoDisplacement]
  have hstationaryFeedback :
      scaled.stationaryFeedbackConstant = base.stationaryFeedbackConstant := by
    unfold Setup.stationaryFeedbackConstant
    rw [hstateFeedbackConsensus, hfinalConsensusGradient,
      hstateFeedbackDisplacement, hfinalDisplacementGradient, hblockGain]
  have hrandomFeedback :
      scaled.randomFeedbackConstant = base.randomFeedbackConstant := by
    unfold Setup.randomFeedbackConstant
    rw [hstateFeedbackConsensus, hfinalConsensusNoise,
      hstateFeedbackDisplacement, hfinalDisplacementNoise, hperiod]
  have hnoiseTrackerFilter :
      scaled.noiseTrackerFilterConstant = base.noiseTrackerFilterConstant := by
    unfold Setup.noiseTrackerFilterConstant
    rw [hcorrectedNorm, hcolumnContraction, hpullDeviation,
      hcontractionRate]
  change scaled.alphaMax = base.alphaMax ∧
    scaled.theoremSevenOnePreRateA = base.theoremSevenOnePreRateA ∧
    scaled.theoremSevenOnePreRateD = base.theoremSevenOnePreRateD ∧
    scaled.blockGain = base.blockGain ∧
    (Finset.expect Finset.univ (fun r : Fin scaled.period => Setup.rowSum (scaled.influence r.1))) = (Finset.expect Finset.univ (fun r : Fin base.period => Setup.rowSum (base.influence r.1))) ∧
    scaled.influenceSecondMoment = base.influenceSecondMoment
  refine ⟨?_, ?_, ?_, hblockGain, hinfluenceGain,
    hinfluenceSecondMoment⟩
  · unfold Setup.alphaMax
    rw [halphaStable, hblockGain, hinfluenceSecondMoment,
      hnoiseTrackerFilter, hrandomFeedback, hstationaryFeedback, hperiod, hL]
  · unfold Setup.theoremSevenOnePreRateA
    rw [hL, hperiod, hfinalDisplacementGradient]
  · unfold Setup.theoremSevenOnePreRateD
    rw [hL, hperiod, hfinalDisplacementNoise]

private theorem zeroNoiseCounterexampleSetup_transient_eq (n : ℕ) :
    (zeroNoiseCounterexampleSetup n).theoremSevenOneTransientCoefficient =
      zeroNoiseCounterexampleScale n ^ 2 *
        (zeroNoiseCounterexampleBaseSetup n).theoremSevenOneTransientCoefficient := by
  rcases zeroNoiseCounterexampleSetup_transient_network_data n with
    ⟨halpha, hpreA, hpreD, hblock, hgain, hsecond⟩
  rcases zeroNoiseCounterexampleSetup_scalar_data n with
    ⟨hL, hDelta, hsigma⟩
  rcases zeroNoiseCounterexampleBaseSetup_scalar_data n with
    ⟨hLbase, hDeltaBase, hsigmaBase⟩
  have hperiod : (zeroNoiseCounterexampleSetup n).period =
      (zeroNoiseCounterexampleBaseSetup n).period := rfl
  rw [Setup.theoremSevenOneTransientCoefficient,
    Setup.theoremSevenOneTransientCoefficient]
  rw [halpha, hpreA, hpreD, hblock, hgain, hsecond,
    hL, hLbase, hDelta, hDeltaBase, hsigma, hsigmaBase, hperiod,
    zeroNoiseCounterexampleSetup_initialGradientHeterogeneity_zero,
    zeroNoiseCounterexampleBaseSetup_initialGradientHeterogeneity_zero]
  ring

private theorem zeroNoiseCounterexamplePull_mul_self (n : ℕ) :
    Setup.matrixMul (Node := Fin (n + 1))
        (zeroNoiseCounterexamplePull n 0)
        (zeroNoiseCounterexamplePull n 0) =
      zeroNoiseCounterexamplePull n 0 := by
  classical
  funext i j
  unfold Setup.matrixMul zeroNoiseCounterexamplePull
  rw [← Finset.mul_sum]
  rw [zeroNoiseUniformWeight_sum n]
  simp

private theorem zeroNoiseCounterexample_pullWindowProduct_succ
    (n r j : ℕ) :
    (zeroNoiseCounterexampleBaseSetup n).pullWindowProduct r (j + 1) =
      zeroNoiseCounterexamplePull n 0 := by
  induction j with
  | zero =>
      simp [Setup.pullWindowProduct, zeroNoiseCounterexampleBaseSetup,
        Setup.matrixMul_identity_right]
      funext i k
      rfl
  | succ j ih =>
      simp only [Setup.pullWindowProduct]
      change
        Setup.matrixMul (Node := Fin (n + 1))
            (zeroNoiseCounterexamplePull n 0)
            ((zeroNoiseCounterexampleBaseSetup n).pullWindowProduct r (j + 1)) =
          zeroNoiseCounterexamplePull n 0
      rw [ih]
      exact zeroNoiseCounterexamplePull_mul_self n

private theorem zeroNoisePhaseWeight_mul_pull_sub_identity
    (n t : ℕ) :
    Setup.rowMulMatrix (Node := Fin (n + 1))
        (zeroNoiseCounterexamplePhaseWeight n t)
        (Setup.matrixSub (Node := Fin (n + 1))
          (zeroNoiseCounterexamplePull n 0)
          (Setup.identityMatrix (Node := Fin (n + 1)))) =
      fun i => zeroNoiseUniformWeight n -
        zeroNoiseCounterexamplePhaseWeight n t i := by
  classical
  funext i
  unfold Setup.rowMulMatrix Setup.matrixSub Setup.identityMatrix
    zeroNoiseCounterexamplePull
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [show (∑ j : Fin (n + 1),
      zeroNoiseCounterexamplePhaseWeight n t j) = 1 by
    simpa [Setup.rowSum] using
      zeroNoiseCounterexamplePhaseWeight_sum n t]
  simp

private theorem zeroNoisePull_mul_sub_identity (n : ℕ) :
    Setup.matrixMul (Node := Fin (n + 1))
        (zeroNoiseCounterexamplePull n 0)
        (Setup.matrixSub (Node := Fin (n + 1))
          (zeroNoiseCounterexamplePull n 0)
          (Setup.identityMatrix (Node := Fin (n + 1)))) =
      fun _ _ => 0 := by
  classical
  funext i j
  unfold Setup.matrixMul Setup.matrixSub Setup.identityMatrix
    zeroNoiseCounterexamplePull
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [zeroNoiseUniformWeight_sum n]
  simp

private theorem zeroNoiseCounterexample_influenceSeriesTerm_zero
    (n r j : ℕ) :
    (zeroNoiseCounterexampleBaseSetup n).influenceSeriesTerm r (j + 1) =
      fun _ => 0 := by
  classical
  funext i
  rw [Setup.influenceSeriesTerm_apply_as_weighted_column]
  rw [← (zeroNoiseCounterexampleBaseSetup n).pullWindowProduct_eq_pullLiftProduct_succ]
  rw [zeroNoiseCounterexample_pullWindowProduct_succ n r j]
  rw [← Setup.weightedState_rowMulMatrix]
  simp only [Setup.weightedState, smul_eq_mul]
  rw [show (zeroNoiseCounterexampleBaseSetup n).C r =
      zeroNoiseCounterexamplePull n 0 by rfl]
  change
    Setup.rowMulMatrix (Node := Fin (n + 1))
        (Setup.rowMulMatrix (Node := Fin (n + 1))
          ((zeroNoiseCounterexampleBaseSetup n).perronLeft
            (r + (j + 1) + 2))
          (zeroNoiseCounterexamplePull n 0))
        (Setup.matrixSub (Node := Fin (n + 1))
          (zeroNoiseCounterexamplePull n 0)
          (Setup.identityMatrix (Node := Fin (n + 1)))) i = 0
  rw [Setup.rowMulMatrix_matrixMul]
  rw [zeroNoisePull_mul_sub_identity n]
  simp [Setup.rowMulMatrix]

private theorem zeroNoiseCounterexample_influence (n r : ℕ) :
    (zeroNoiseCounterexampleBaseSetup n).influence r =
      fun i =>
        zeroNoiseCounterexamplePhaseWeight n (r + 1) i +
          zeroNoiseUniformWeight n -
            zeroNoiseCounterexamplePhaseWeight n (r + 2) i := by
  classical
  unfold Setup.influence
  rw [(zeroNoiseCounterexampleBaseSetup_perron n).1 (r + 1)]
  have htail :
      (∑' j : ℕ,
        (zeroNoiseCounterexampleBaseSetup n).influenceSeriesTerm r j) =
      (zeroNoiseCounterexampleBaseSetup n).influenceSeriesTerm r 0 := by
    apply tsum_eq_single 0
    intro j hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    exact zeroNoiseCounterexample_influenceSeriesTerm_zero n r k
  rw [htail]
  funext i
  simp only [Pi.add_apply]
  rw [Setup.influenceSeriesTerm_apply_as_weighted_column]
  simp only [Setup.pullLiftProduct]
  rw [Setup.leftMul_identity]
  rw [(zeroNoiseCounterexampleBaseSetup_perron n).1 (r + 2)]
  change
    zeroNoiseCounterexamplePhaseWeight n (r + 1) i +
        Setup.rowMulMatrix (Node := Fin (n + 1))
          (zeroNoiseCounterexamplePhaseWeight n (r + 2))
          (Setup.matrixSub (Node := Fin (n + 1))
            (zeroNoiseCounterexamplePull n 0)
            (Setup.identityMatrix (Node := Fin (n + 1)))) i = _
  rw [zeroNoisePhaseWeight_mul_pull_sub_identity n (r + 2)]
  simp
  ring

private theorem zeroNoiseCounterexample_influence_rowSum (n r : ℕ) :
    Setup.rowSum (Node := Fin (n + 1))
      ((zeroNoiseCounterexampleBaseSetup n).influence r) = 1 := by
  classical
  rw [zeroNoiseCounterexample_influence n r]
  unfold Setup.rowSum
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hphase1 := zeroNoiseCounterexamplePhaseWeight_sum n (r + 1)
  have hphase2 := zeroNoiseCounterexamplePhaseWeight_sum n (r + 2)
  have huniform := zeroNoiseUniformWeight_sum n
  unfold Setup.rowSum at hphase1 hphase2
  rw [hphase1, hphase2, huniform]
  norm_num

private theorem zeroNoiseCounterexample_influenceGain (n : ℕ) :
    (Finset.expect Finset.univ (fun r : Fin (zeroNoiseCounterexampleBaseSetup n).period => Setup.rowSum ((zeroNoiseCounterexampleBaseSetup n).influence r.1))) = 1 := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin]
  change
    (∑ r : Fin 2,
        Setup.rowSum (Node := Fin (n + 1))
          ((zeroNoiseCounterexampleBaseSetup n).influence r.1)) / 2 = 1
  simp [zeroNoiseCounterexample_influence_rowSum]

private theorem zeroNoiseCounterexample_influence_one (n : ℕ) :
    (zeroNoiseCounterexampleBaseSetup n).influence 1 =
      zeroNoiseSkewWeight n := by
  rw [zeroNoiseCounterexample_influence n 1]
  funext i
  simp [zeroNoiseCounterexamplePhaseWeight]

private theorem zeroNoiseCounterexample_influenceSecondMoment_lower (n : ℕ) :
    (1 / 8 : ℝ) ≤
      (zeroNoiseCounterexampleBaseSetup n).influenceSecondMoment := by
  classical
  have hsingle :
      (zeroNoiseSkewWeight n (0 : Fin (n + 1))) ^ 2 ≤
        Setup.rowNormSq (Node := Fin (n + 1))
          ((zeroNoiseCounterexampleBaseSetup n).influence 1) := by
    rw [zeroNoiseCounterexample_influence_one n]
    unfold Setup.rowNormSq
    exact Finset.single_le_sum
      (fun i _ => sq_nonneg (zeroNoiseSkewWeight n i))
      (Finset.mem_univ (0 : Fin (n + 1)))
  have hskew :
      (1 / 2 : ℝ) ≤ zeroNoiseSkewWeight n (0 : Fin (n + 1)) := by
    unfold zeroNoiseSkewWeight
    simp
    exact (zeroNoiseUniformWeight_pos n).le
  have hskewSq :
      (1 / 4 : ℝ) ≤ (zeroNoiseSkewWeight n (0 : Fin (n + 1))) ^ 2 := by
    nlinarith [zeroNoiseSkewWeight_pos n (0 : Fin (n + 1))]
  unfold Setup.influenceSecondMoment
  change
    ((2 : ℝ)⁻¹) *
      (∑ r : Fin 2,
        Setup.rowNormSq (Node := Fin (n + 1))
          ((zeroNoiseCounterexampleBaseSetup n).influence r.1)) >= 1 / 8
  simp only [Fin.sum_univ_two]
  have hzero :
      0 ≤ Setup.rowNormSq (Node := Fin (n + 1))
        ((zeroNoiseCounterexampleBaseSetup n).influence 0) := by
    unfold Setup.rowNormSq
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  norm_num at *
  nlinarith

private theorem zeroNoiseCounterexample_effectiveNodeCount_le_eight (n : ℕ) :
    (zeroNoiseCounterexampleBaseSetup n).effectiveNodeCount ≤ 8 := by
  have hqpos :=
    (zeroNoiseCounterexampleBaseSetup n).influenceSecondMoment_pos
  unfold Setup.effectiveNodeCount
  rw [zeroNoiseCounterexample_influenceGain n]
  rw [div_le_iff₀ hqpos]
  have hq := zeroNoiseCounterexample_influenceSecondMoment_lower n
  nlinarith

private theorem zeroNoiseCounterexampleSetup_influence_data (n : ℕ) :
    (Finset.expect Finset.univ (fun r : Fin (zeroNoiseCounterexampleSetup n).period => Setup.rowSum ((zeroNoiseCounterexampleSetup n).influence r.1))) =
        (Finset.expect Finset.univ (fun r : Fin (zeroNoiseCounterexampleBaseSetup n).period => Setup.rowSum ((zeroNoiseCounterexampleBaseSetup n).influence r.1))) ∧
      (zeroNoiseCounterexampleSetup n).influenceSecondMoment =
        (zeroNoiseCounterexampleBaseSetup n).influenceSecondMoment := by
  let scaled := zeroNoiseCounterexampleSetup n
  let base := zeroNoiseCounterexampleBaseSetup n
  have hperron : scaled.perronSequences = base.perronSequences := by
    apply base.perronSequences_unique scaled.perronSequences
    · simpa [scaled, base, zeroNoiseCounterexampleSetup,
        Setup.PerronSequencesEquations] using scaled.perronSequences_spec.1
    · simpa [scaled, base, zeroNoiseCounterexampleSetup,
        Setup.PerronSequencesPositivePeriodic] using
          scaled.perronSequences_spec.2.1
  have hleft (t : ℕ) : scaled.perronLeft t = base.perronLeft t := by
    unfold Setup.perronLeft
    exact congrArg (fun seqs => seqs.1 t) hperron
  have hpull (r j : ℕ) :
      scaled.pullWindowProduct r j = base.pullWindowProduct r j := by
    induction j with
    | zero => rfl
    | succ j ih =>
        simp only [Setup.pullWindowProduct]
        rw [ih]
        rfl
  have hC : scaled.C = base.C := by rfl
  have hseries (r j : ℕ) :
      scaled.influenceSeriesTerm r j = base.influenceSeriesTerm r j := by
    classical
    unfold Setup.influenceSeriesTerm
    simp only [FiniteNetwork.periodicInfluenceSeriesTerm_def, hleft, hC]
  have hinfluence (r : ℕ) : scaled.influence r = base.influence r := by
    unfold Setup.influence
    rw [hleft]
    congr 1
  constructor
  · congr 1
  · unfold Setup.influenceSecondMoment
    change
      ((2 : ℝ)⁻¹) *
          (∑ r : Fin 2, Setup.rowNormSq (scaled.influence r.1)) =
        ((2 : ℝ)⁻¹) *
          (∑ r : Fin 2, Setup.rowNormSq (base.influence r.1))
    congr 1

private theorem zeroNoiseCounterexampleSetup_effectiveNodeCount_eq (n : ℕ) :
    (zeroNoiseCounterexampleSetup n).effectiveNodeCount =
      (zeroNoiseCounterexampleBaseSetup n).effectiveNodeCount := by
  unfold Setup.effectiveNodeCount
  rw [(zeroNoiseCounterexampleSetup_influence_data n).1,
    (zeroNoiseCounterexampleSetup_influence_data n).2]

private theorem zeroNoiseCounterexample_effectiveNodeCount_not_theta :
    ¬ Setup.EffectiveNodeCountThetaN
      (fun n => (zeroNoiseCounterexampleBaseSetup n).effectiveNodeCount) := by
  intro htheta
  rcases htheta with ⟨c, C, N0, hc, _hcC, htheta⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max (N0 : ℝ) (8 / c))
  have hnNReal : (N0 : ℝ) < (n : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hn
  have hnN : N0 ≤ n := by
    exact_mod_cast (le_of_lt hnNReal)
  have hratio : 8 / c < (n : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hn
  have hlarge : 8 < (n : ℝ) * c :=
    (div_lt_iff₀ hc).mp hratio
  have hlarge' : 8 < c * ((n + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hlower := (htheta n hnN).1
  have hupper := zeroNoiseCounterexample_effectiveNodeCount_le_eight n
  linarith

private theorem zeroNoiseCounterexampleSetup_effectiveNodeCount_not_theta :
    ¬ Setup.EffectiveNodeCountThetaN
      (fun n => (zeroNoiseCounterexampleSetup n).effectiveNodeCount) := by
  simpa only [zeroNoiseCounterexampleSetup_effectiveNodeCount_eq] using
    zeroNoiseCounterexample_effectiveNodeCount_not_theta

/- The zero-noise obstruction is nonvacuous at the source oracle level.  A
one-point probability space carries the identically-zero measurable process;
the event-integral formulation of the paper law then holds for every strict
past sigma-algebra. -/
private noncomputable def zeroNoiseCounterexampleOracle (n : ℕ) :
    Setup.OracleNoiseProcess Unit (Fin (n + 1)) ℝ where
  noise := fun _ _ _ => 0
  noise_measurable := by
    intro t
    fun_prop

private noncomputable def unitEventProbability (event : Set Unit) :
    Unit → ℝ := by
  classical
  exact fun _ => if () ∈ event then 1 else 0

private theorem unitConditionalProbabilityVersion
    (calF : MeasurableSpace Unit) (event : Set Unit) :
    @Setup.PaperConditionalProbabilityVersion Unit PUnit.instMeasurableSpace
      (@Measure.dirac Unit PUnit.instMeasurableSpace ()) inferInstance calF
      event (unitEventProbability event) := by
  classical
  constructor
  · fun_prop
  constructor
  · filter_upwards [] with omega
    by_cases hevent : () ∈ event <;>
      simp [unitEventProbability, hevent]
  · intro A hA
    by_cases hevent : () ∈ event
    · have hset : A ∩ event = A := by
        ext omega
        rcases omega with ⟨⟩
        simp [hevent]
      simp [unitEventProbability, hevent, hset]
    · have hset : A ∩ event = ∅ := by
        ext omega
        rcases omega with ⟨⟩
        simp [hevent]
      simp [unitEventProbability, hevent, hset]

private theorem zeroNoiseCounterexampleOracle_sourceLaw (n : ℕ) :
    (zeroNoiseCounterexampleSetup n).StochasticOracleAssumptions
      (Measure.dirac ()) (zeroNoiseCounterexampleOracle n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t i
    constructor
    · simp [zeroNoiseCounterexampleOracle]
    · intro A hA
      simp [zeroNoiseCounterexampleOracle]
  · intro t i
    constructor
    · simp [zeroNoiseCounterexampleOracle]
    · intro A hA
      simp [zeroNoiseCounterexampleOracle,
        zeroNoiseCounterexampleSetup, zeroNoiseCounterexampleBaseSetup]
  · intro t events hevents
    let condProb : Fin (n + 1) → Unit → ℝ := fun i =>
      unitEventProbability {omega : Unit |
        (zeroNoiseCounterexampleOracle n).noise omega t i ∈ events i}
    refine ⟨condProb, ?_, ?_⟩
    · intro i
      simpa [condProb] using
        unitConditionalProbabilityVersion
          ((zeroNoiseCounterexampleOracle n).strictPastMeasurableSpace t)
          {omega : Unit |
            (zeroNoiseCounterexampleOracle n).noise omega t i ∈ events i}
    · let cylinder : Set Unit := {omega : Unit | ∀ i : Fin (n + 1),
        (zeroNoiseCounterexampleOracle n).noise omega t i ∈ events i}
      have hfun :
          (fun omega : Unit => ∏ i : Fin (n + 1), condProb i omega) =
            unitEventProbability cylinder := by
        funext omega
        rcases omega with ⟨⟩
        classical
        by_cases hall : ∀ i : Fin (n + 1), (0 : ℝ) ∈ events i
        · simp [condProb, cylinder, unitEventProbability,
            zeroNoiseCounterexampleOracle, hall]
        · push Not at hall
          rcases hall with ⟨i, hi⟩
          have hnall : ¬ ∀ j : Fin (n + 1), (0 : ℝ) ∈ events j :=
            fun h => hi (h i)
          rw [show (∏ j : Fin (n + 1), condProb j ()) = 0 by
            apply Finset.prod_eq_zero (Finset.mem_univ i)
            simp [condProb, unitEventProbability,
              zeroNoiseCounterexampleOracle, hi]]
          simp [cylinder, unitEventProbability,
            zeroNoiseCounterexampleOracle, hnall]
      rw [hfun]
      exact unitConditionalProbabilityVersion
        ((zeroNoiseCounterexampleOracle n).strictPastMeasurableSpace t)
        cylinder

private def zeroNoiseCounterexampleHorizon (n : ℕ) : ℕ :=
  (n + 1) ^ 2

private theorem zeroNoiseCounterexampleHorizon_diverges :
    Setup.TimeOverNodeDiverges zeroNoiseCounterexampleHorizon := by
  intro M hM
  obtain ⟨N0, hN0⟩ := exists_nat_ge M
  refine ⟨N0, ?_⟩
  intro n hn
  have hMn : M ≤ ((n + 1 : ℕ) : ℝ) := by
    exact hN0.trans (by exact_mod_cast (hn.trans (Nat.le_add_right n 1)))
  have hnnonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hMn hnnonneg
  simpa [zeroNoiseCounterexampleHorizon, pow_two] using hmul

private theorem zeroNoiseCounterexampleScale_le_one (n : ℕ) :
    zeroNoiseCounterexampleScale n ≤ 1 := by
  unfold zeroNoiseCounterexampleScale
  rw [inv_le_one₀]
  · exact le_add_of_nonneg_right (abs_nonneg _)
  · positivity

private theorem zeroNoiseCounterexample_transient_abs_le_one (n : ℕ) :
    |(zeroNoiseCounterexampleSetup n).theoremSevenOneTransientCoefficient| ≤
      1 := by
  let b :=
    (zeroNoiseCounterexampleBaseSetup n).theoremSevenOneTransientCoefficient
  let s := zeroNoiseCounterexampleScale n
  have hspos : 0 < s := zeroNoiseCounterexampleScale_pos n
  have hsle : s ≤ 1 := zeroNoiseCounterexampleScale_le_one n
  have habs : 0 ≤ |b| := abs_nonneg b
  have hnormalize : s * (1 + |b|) = 1 := by
    dsimp [s, b]
    unfold zeroNoiseCounterexampleScale
    exact inv_mul_cancel₀ (by positivity)
  have hsa : s * |b| ≤ 1 := by
    nlinarith
  have hsq : s ^ 2 ≤ s := by
    nlinarith
  have hscaled : s ^ 2 * |b| ≤ 1 :=
    (mul_le_mul_of_nonneg_right hsq habs).trans hsa
  rw [zeroNoiseCounterexampleSetup_transient_eq, abs_mul, abs_pow,
    abs_of_pos hspos]
  exact hscaled

private theorem zeroNoiseCounterexample_problem_scalars_bounded :
    ∀ n : ℕ,
      0 ≤ (zeroNoiseCounterexampleSetup n).L ∧
        (zeroNoiseCounterexampleSetup n).L ≤ 1 ∧
        0 ≤ (zeroNoiseCounterexampleSetup n).Delta ∧
        (zeroNoiseCounterexampleSetup n).Delta ≤ 1 ∧
        0 ≤ (zeroNoiseCounterexampleSetup n).sigma ∧
        (zeroNoiseCounterexampleSetup n).sigma ≤ 1 := by
  intro n
  rcases zeroNoiseCounterexampleSetup_scalar_data n with
    ⟨hL, hDelta, hsigma⟩
  have hscalePos := zeroNoiseCounterexampleScale_pos n
  have hscaleLe := zeroNoiseCounterexampleScale_le_one n
  rw [hL, hDelta, hsigma]
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · positivity
  constructor
  · nlinarith
  constructor <;> norm_num

private theorem zeroNoiseCounterexample_uniformly_bounded :
    Setup.UniformlyBoundedCorollaryFamily
      (fun n => (zeroNoiseCounterexampleSetup n).L)
      (fun n => (zeroNoiseCounterexampleSetup n).Delta)
      (fun n => (zeroNoiseCounterexampleSetup n).sigma)
      (fun n =>
        (zeroNoiseCounterexampleSetup n).theoremSevenOneTransientCoefficient) := by
  refine ⟨1, by norm_num, ?_⟩
  intro n
  rcases zeroNoiseCounterexample_problem_scalars_bounded n with
    ⟨hL0, hL1, hDelta0, hDelta1, hsigma0, hsigma1⟩
  exact ⟨hL0, hL1, hDelta0, hDelta1, hsigma0, hsigma1,
    zeroNoiseCounterexample_transient_abs_le_one n⟩

private theorem zeroNoiseCounterexample_generated_family :
    GeneratedCorollaryFamily
      (fun n => (zeroNoiseCounterexampleSetup n).effectiveNodeCount)
      (fun n => (zeroNoiseCounterexampleSetup n).L)
      (fun n => (zeroNoiseCounterexampleSetup n).Delta)
      (fun n => (zeroNoiseCounterexampleSetup n).sigma)
      (fun n =>
        (zeroNoiseCounterexampleSetup n).theoremSevenOneTransientCoefficient)
      zeroNoiseCounterexampleSetup := by
  intro n
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/- This packages the original generated zero-noise family counterexample,
including the exact transient coefficient required by the source family
hypotheses. -/
private theorem zeroNoiseGeneratedNecessityObstruction :
    GeneratedCentralizedStochasticUpperProperty
      (fun n => (zeroNoiseCounterexampleSetup n).effectiveNodeCount)
      (fun n => (zeroNoiseCounterexampleSetup n).L)
      (fun n => (zeroNoiseCounterexampleSetup n).Delta)
      (fun n => (zeroNoiseCounterexampleSetup n).sigma)
      (fun n =>
        (zeroNoiseCounterexampleSetup n).theoremSevenOneTransientCoefficient)
      zeroNoiseCounterexampleHorizon zeroNoiseCounterexampleSetup ∧
    Setup.UniformlyBoundedCorollaryFamily
      (fun n => (zeroNoiseCounterexampleSetup n).L)
      (fun n => (zeroNoiseCounterexampleSetup n).Delta)
      (fun n => (zeroNoiseCounterexampleSetup n).sigma)
      (fun n =>
        (zeroNoiseCounterexampleSetup n).theoremSevenOneTransientCoefficient) ∧
    Setup.TimeOverNodeDiverges zeroNoiseCounterexampleHorizon ∧
    (∀ n : ℕ,
      (zeroNoiseCounterexampleSetup n).StochasticOracleAssumptions
        (Measure.dirac ()) (zeroNoiseCounterexampleOracle n)) ∧
    (∀ n : ℕ, (zeroNoiseCounterexampleSetup n).sigma = 0) ∧
    (∀ n : ℕ,
      0 ≤ (zeroNoiseCounterexampleSetup n).L ∧
        (zeroNoiseCounterexampleSetup n).L ≤ 1 ∧
        0 ≤ (zeroNoiseCounterexampleSetup n).Delta ∧
        (zeroNoiseCounterexampleSetup n).Delta ≤ 1 ∧
        0 ≤ (zeroNoiseCounterexampleSetup n).sigma ∧
        (zeroNoiseCounterexampleSetup n).sigma ≤ 1) ∧
    ¬ Setup.EffectiveNodeCountThetaN
      (fun n => (zeroNoiseCounterexampleSetup n).effectiveNodeCount) := by
  refine ⟨?_, zeroNoiseCounterexample_uniformly_bounded,
    zeroNoiseCounterexampleHorizon_diverges,
    zeroNoiseCounterexampleOracle_sourceLaw,
    fun n => (zeroNoiseCounterexampleSetup_scalar_data n).2.2,
    zeroNoiseCounterexample_problem_scalars_bounded,
    zeroNoiseCounterexampleSetup_effectiveNodeCount_not_theta⟩
  apply generatedCentralizedStochasticUpperProperty_of_zeroNoise
    zeroNoiseCounterexample_generated_family
  · intro n
    exact (zeroNoiseCounterexampleSetup_scalar_data n).2.2
  · exact zeroNoiseCounterexampleHorizon_diverges

/-- A square-root rate can be factored into its horizon-independent
coefficient and the `horizon⁻¹ᐟ²` scale. -/
theorem sqrt_div_mul_eq_sqrt_div_mul_inv_sqrt
    {A e : ℝ} {horizon : ℕ}
    (hA : 0 ≤ A) (he : 0 < e) (hhorizon : 1 ≤ horizon) :
    Real.sqrt (A / (e * (horizon : ℝ))) =
      Real.sqrt (A / e) * (Real.sqrt (horizon : ℝ))⁻¹ := by
  have hhorizonPos : (0 : ℝ) < (horizon : ℝ) := by positivity
  calc
    Real.sqrt (A / (e * (horizon : ℝ))) =
        Real.sqrt ((A / e) / (horizon : ℝ)) := by
      congr 1
      field_simp [ne_of_gt he, ne_of_gt hhorizonPos]
    _ = Real.sqrt (A / e) / Real.sqrt (horizon : ℝ) :=
      Real.sqrt_div (div_nonneg hA he.le) _
    _ = Real.sqrt (A / e) * (Real.sqrt (horizon : ℝ))⁻¹ := by
      rw [div_eq_mul_inv]

/-- Corrected generated stochastic branch of Corollary 8.2.  The explicit
eventual-positive premise is necessary by the full-hypothesis generated
zero-noise counterexample above.  On that eventual tail, the exact-noise
family supplies primitive, nonvacuous lower-test data on the same networks as
the upper instances.  The lower performance horizon remains independent of
the selected schedule `T`. -/
theorem GeneratedTrueNfoldSpeedupCriterion
    {neff L Delta sigma transient : ℕ → ℝ} {T : ℕ → ℕ}
    {setup : (n : ℕ) → Setup (Fin (n + 1)) ℝ}
    {quad : (n : ℕ) → Setup (Fin (n + 1)) ℝ}
    {Omega : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (oracle : (n : ℕ) → Setup.OracleNoiseProcess Omega (Fin (n + 1)) ℝ)
    (hfamily : GeneratedCorollaryFamily neff L Delta sigma transient setup)
    (hquad :
      GeneratedQuadraticLowerFamily neff L Delta sigma setup quad mu oracle)
    (hpositive : Setup.EventuallyPositiveSigmaFamily sigma)
    (hbounded : Setup.UniformlyBoundedCorollaryFamily L Delta sigma transient)
    (hT : Setup.TimeOverNodeDiverges T) :
    GeneratedStochasticNfoldComplexity
        neff L Delta sigma transient T setup quad mu oracle ↔
      Setup.EffectiveNodeCountThetaN neff := by
  have hupper :
      GeneratedStochasticUpperProperty neff L Delta sigma transient setup :=
    generatedStochasticUpperProperty_of_family hfamily
  have hlower :
      GeneratedMatchingQuadraticLowerCertification
        neff L Delta sigma setup quad mu oracle :=
    generatedMatchingQuadraticLowerCertification_of_family mu oracle hquad
  have htransient : GeneratedTransientLowerOrder transient T :=
    generatedTransientLowerOrder_of_uniformBound hbounded hT
  rcases hpositive with ⟨Nsigma, hsigmaPositive⟩
  rcases hT 1 (by norm_num) with ⟨NT, hTlarge⟩
  have hTpos : ∀ n : ℕ, NT ≤ n → 0 < (T n : ℝ) := by
    intro n hn
    have hnT := hTlarge n hn
    have hnOne : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    exact lt_of_lt_of_le hnOne (by simpa using hnT)
  constructor
  · intro hcomplexity
    rcases hcomplexity with ⟨_hgeneratedUpper, _htransientLower,
      hgeneratedLowerFamily, C, hC, NC, hgeneratedLower⟩
    let c : ℝ := ((C + 1) ^ 2 + 1)⁻¹
    have hdenom : 0 < (C + 1) ^ 2 + 1 := by positivity
    have hc : 0 < c := inv_pos.mpr hdenom
    have hcOne : c ≤ (1 : ℝ) := by
      dsimp [c]
      rw [inv_le_one₀ hdenom]
      nlinarith [sq_nonneg (C + 1)]
    refine ⟨c, 1, max NC Nsigma, hc, hcOne, ?_⟩
    intro n hn
    have hnC : NC ≤ n := le_trans (le_max_left _ _) hn
    have hnSigma : Nsigma ≤ n := le_trans (le_max_right _ _) hn
    have hsigmaPos : 0 < sigma n := hsigmaPositive n hnSigma
    rcases hgeneratedLowerFamily.2 n hsigmaPos with
      ⟨hneffQuad, _hLQuad, hDeltaQuad, hsigmaQuad, hhomogeneous, hnoise⟩
    rcases hgeneratedLower n hnC with
      ⟨horizon0, hhorizon0, hperformance⟩
    rcases hlower.2 n hsigmaPos with ⟨residual, hresidual, hexpansion⟩
    have hLpos : 0 < L n := hhomogeneous.1
    have hDeltaPos : 0 < Delta n := by
      rw [hDeltaQuad]
      exact (quad n).Delta_positive
    have hneffPos : 0 < neff n := by
      rw [hneffQuad]
      exact (quad n).effectiveNodeCount_pos_and_le_nodeCount.1
    have hneffUpper : neff n ≤ ((n + 1 : ℕ) : ℝ) := by
      rw [hneffQuad]
      simpa [nodeCount] using
        (quad n).AverageGainEffectiveNodes.2.2.2.2.2.2.1
    have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    let centralCoefficient : ℝ :=
      sigma n * Real.sqrt
        (2 * L n * Delta n / ((n + 1 : ℕ) : ℝ))
    have hcentralCoefficientPos : 0 < centralCoefficient := by
      dsimp [centralCoefficient]
      exact mul_pos hsigmaPos (Real.sqrt_pos.2
        (div_pos
          (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hLpos) hDeltaPos)
          hm))
    have hsmall := hresidual.def hcentralCoefficientPos
    rcases Filter.eventually_atTop.1 hsmall with ⟨horizonResidual, hsmall⟩
    let horizon : ℕ := max horizon0 horizonResidual
    have hhorizon0le : horizon0 ≤ horizon := le_max_left _ _
    have hhorizonResidualle : horizonResidual ≤ horizon := le_max_right _ _
    have hhorizon : 1 ≤ horizon := le_trans hhorizon0 hhorizon0le
    have hhorizonPos : (0 : ℝ) < (horizon : ℝ) := by positivity
    have hinvSqrtNonneg :
        0 ≤ (Real.sqrt (horizon : ℝ))⁻¹ := by positivity
    have hresidualNorm := hsmall horizon hhorizonResidualle
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hinvSqrtNonneg] at hresidualNorm
    have hresidualLower :
        -(centralCoefficient * (Real.sqrt (horizon : ℝ))⁻¹) ≤
          residual horizon := by
      linarith [neg_abs_le (residual horizon)]
    have hperformanceAt := hperformance horizon hhorizon0le
    rw [hexpansion horizon] at hperformanceAt
    have hleadingFactor :
        Real.sqrt
            (2 * L n * Delta n / (neff n * (horizon : ℝ))) =
          Real.sqrt (2 * L n * Delta n / neff n) *
            (Real.sqrt (horizon : ℝ))⁻¹ :=
      sqrt_div_mul_eq_sqrt_div_mul_inv_sqrt
        (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hLpos)
          hDeltaPos).le hneffPos hhorizon
    have hcentralFactor :
        Real.sqrt
            (2 * L n * Delta n /
              (((n + 1 : ℕ) : ℝ) * (horizon : ℝ))) =
          Real.sqrt
              (2 * L n * Delta n / ((n + 1 : ℕ) : ℝ)) *
            (Real.sqrt (horizon : ℝ))⁻¹ :=
      sqrt_div_mul_eq_sqrt_div_mul_inv_sqrt
        (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hLpos)
          hDeltaPos).le hm hhorizon
    have hcompare :
        sigma n * Real.sqrt
            (2 * L n * Delta n / (neff n * (horizon : ℝ))) ≤
          (C + 1) * sigma n * Real.sqrt
            (2 * L n * Delta n /
              (((n + 1 : ℕ) : ℝ) * (horizon : ℝ))) := by
      rw [hleadingFactor, hcentralFactor]
      dsimp [centralCoefficient] at hresidualLower hperformanceAt
      nlinarith
    have hlinear : ((n + 1 : ℕ) : ℝ) ≤ (C + 1) ^ 2 * neff n :=
      Setup.leading_sqrt_ratio_effective_node_forward
        (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hLpos) hDeltaPos)
        hneffPos hm hhorizonPos hsigmaPos (by linarith) hcompare
    have hlowerLinear : c * ((n + 1 : ℕ) : ℝ) ≤ neff n := by
      dsimp [c]
      rw [inv_mul_le_iff₀ hdenom]
      nlinarith [mul_pos hdenom hneffPos]
    exact ⟨hlowerLinear, by simpa using hneffUpper⟩
  · intro htheta
    rcases htheta with ⟨c, Ctheta, Ntheta, hc, _hcCtheta, htheta⟩
    refine ⟨?_, htransient, ?_⟩
    · refine ⟨hfamily, 8 * Real.sqrt (c⁻¹),
        mul_nonneg (by norm_num) (Real.sqrt_nonneg _), max Ntheta NT, ?_⟩
      intro n hn Omega _ mu' _ oracle' horacle'
      have hnTheta : Ntheta ≤ n := le_trans (le_max_left _ _) hn
      have hnT : NT ≤ n := le_trans (le_max_right _ _) hn
      have hTnat : 1 ≤ T n := by exact_mod_cast hTpos n hnT
      rcases hupper.2 n Omega mu' oracle' horacle' (T n) hTnat with
        ⟨alpha, halphaPos, halphaMax, hstationarity⟩
      rcases hfamily n with ⟨hneff, hL, hDelta, hsigma, _htransient⟩
      have hsigmaNonneg : 0 ≤ sigma n := by
        rw [hsigma]
        exact (setup n).sigma_nonneg
      have hLpos : 0 < L n := by simpa [hL] using (setup n).L_pos
      have hDeltaPos : 0 < Delta n := by
        simpa [hDelta] using (setup n).Delta_positive
      have hneffPos : 0 < neff n := by
        simpa [hneff] using (setup n).effectiveNodeCount_pos_and_le_nodeCount.1
      have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hleading := Setup.leading_sqrt_ratio_effective_node_reverse
        (mul_pos hLpos hDeltaPos) hneffPos hm (hTpos n hnT)
        hsigmaNonneg hc (htheta n hnTheta).1
      refine ⟨alpha, halphaPos, halphaMax, hstationarity.trans ?_⟩
      simpa [mul_assoc] using
        (add_le_add_right
          (mul_le_mul_of_nonneg_left hleading (by norm_num : (0 : ℝ) ≤ 8))
          (transient n / (T n : ℝ)))
    · refine ⟨hquad, Real.sqrt (c⁻¹) + 1, by positivity,
        max Ntheta Nsigma, ?_⟩
      intro n hn
      have hnTheta : Ntheta ≤ n := le_trans (le_max_left _ _) hn
      have hnSigma : Nsigma ≤ n := le_trans (le_max_right _ _) hn
      have hsigmaPos : 0 < sigma n := hsigmaPositive n hnSigma
      rcases hlower.2 n hsigmaPos with ⟨residual, hresidual, hexpansion⟩
      rcases hquad.2 n hsigmaPos with
        ⟨hneffQuad, _hLQuad, hDeltaQuad, hsigmaQuad, hhomogeneous, hnoise⟩
      have hLpos : 0 < L n := hhomogeneous.1
      have hDeltaPos : 0 < Delta n := by
        rw [hDeltaQuad]
        exact (quad n).Delta_positive
      have hneffPos : 0 < neff n := by
        rw [hneffQuad]
        exact (quad n).effectiveNodeCount_pos_and_le_nodeCount.1
      have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      let centralCoefficient : ℝ :=
        sigma n * Real.sqrt
          (2 * L n * Delta n / ((n + 1 : ℕ) : ℝ))
      have hcentralCoefficientPos : 0 < centralCoefficient := by
        dsimp [centralCoefficient]
        exact mul_pos hsigmaPos (Real.sqrt_pos.2
          (div_pos
            (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hLpos) hDeltaPos)
            hm))
      have hsmall := hresidual.def hcentralCoefficientPos
      rcases Filter.eventually_atTop.1 hsmall with ⟨horizonResidual, hsmall⟩
      refine ⟨max 1 horizonResidual, le_max_left _ _, ?_⟩
      intro horizon hhorizonMax
      have hhorizon : 1 ≤ horizon :=
        le_trans (le_max_left _ _) hhorizonMax
      have hhorizonResidual : horizonResidual ≤ horizon :=
        le_trans (le_max_right _ _) hhorizonMax
      have hhorizonPos : (0 : ℝ) < (horizon : ℝ) := by positivity
      have hinvSqrtNonneg :
          0 ≤ (Real.sqrt (horizon : ℝ))⁻¹ := by positivity
      have hresidualNorm := hsmall horizon hhorizonResidual
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hinvSqrtNonneg] at hresidualNorm
      have hresidualUpper :
          residual horizon ≤
            centralCoefficient * (Real.sqrt (horizon : ℝ))⁻¹ :=
        le_trans (le_abs_self _) hresidualNorm
      have hleading := Setup.leading_sqrt_ratio_effective_node_reverse
        (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hLpos) hDeltaPos)
        hneffPos hm hhorizonPos hsigmaPos.le hc (htheta n hnTheta).1
      have hcentralFactor :
          Real.sqrt
              (2 * L n * Delta n /
                (((n + 1 : ℕ) : ℝ) * (horizon : ℝ))) =
            Real.sqrt
                (2 * L n * Delta n / ((n + 1 : ℕ) : ℝ)) *
              (Real.sqrt (horizon : ℝ))⁻¹ :=
        sqrt_div_mul_eq_sqrt_div_mul_inv_sqrt
          (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hLpos)
            hDeltaPos).le hm hhorizon
      rw [hexpansion horizon]
      rw [hcentralFactor] at hleading
      dsimp [centralCoefficient] at hresidualUpper ⊢
      nlinarith

/-- Generated zero-noise conclusion of Corollary 8.2.  It quantifies every
source-law oracle and bounds the stationarity average of the generated run,
not merely the scalar transient quotient. -/
def GeneratedDeterministicProperty
    (transient : ℕ → ℝ)
    (setup : (n : ℕ) → Setup (Fin (n + 1)) ℝ) : Prop :=
  (∀ n : ℕ,
      (setup n).sigma = 0 ∧
        transient n = (setup n).theoremSevenOneTransientCoefficient) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (Omega : Type*)
      [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
      (oracle : Setup.OracleNoiseProcess Omega (Fin (n + 1)) ℝ),
      (setup n).StochasticOracleAssumptions mu oracle →
        ∀ horizon : ℕ, 1 ≤ horizon →
          ((setup n).withStepsize ((setup n).horizonStepsize horizon)).stationarityAverage
              mu oracle horizon ≤ C / (horizon : ℝ)

/-- The generated deterministic branch follows directly from Theorem 7.1,
using one uniform bound on the explicit family transient. -/
theorem GeneratedDeterministicCorollaryBranch
    {transient : ℕ → ℝ}
    {setup : (n : ℕ) → Setup (Fin (n + 1)) ℝ}
    (hzero : ∀ n : ℕ, (setup n).sigma = 0)
    (htransient : ∀ n : ℕ,
      transient n = (setup n).theoremSevenOneTransientCoefficient)
    (hbounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, transient n ≤ C) :
    GeneratedDeterministicProperty transient setup := by
  refine ⟨fun n => ⟨hzero n, htransient n⟩, ?_⟩
  rcases hbounded with ⟨C, hC, hCle⟩
  refine ⟨C, hC, ?_⟩
  intro n Omega _ mu _ oracle horacle horizon hhorizon
  have hupper :=
    (setup n).horizon_stepsize_leading_and_transient_bounds
      mu oracle horizon hhorizon horacle
  have hhorizon_pos : (0 : ℝ) < horizon := by positivity
  have htransient_le :
      (setup n).theoremSevenOneTransientCoefficient / (horizon : ℝ) ≤
        C / (horizon : ℝ) := by
    exact (div_le_div_iff_of_pos_right hhorizon_pos).2
      (by simpa [htransient n] using hCle n)
  have hgenerated :
      ((setup n).withStepsize ((setup n).horizonStepsize horizon)).stationarityAverage
          mu oracle horizon ≤
        (setup n).theoremSevenOneTransientCoefficient / (horizon : ℝ) := by
    simpa [Setup.stationarityAverage, hzero n] using hupper
  exact hgenerated.trans htransient_le

end Algorithms.Unverified.TimeVaryingPushPull
