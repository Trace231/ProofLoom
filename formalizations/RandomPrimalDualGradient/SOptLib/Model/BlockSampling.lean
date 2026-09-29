import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Tactic

/-- Natural-time stream of paired oracle samples and block indices.

For sample type `S` and block-index type `I`, `blockSamplePath S I` is the
path space whose `k`th coordinate is the pair generated at iteration `k`.  It
uses the canonical Pi-function representation so Mathlib's measurable-space
and coordinate-projection APIs apply directly.

Layer: Model | Concept: Sampling
Proof: (definitional construction; Nat-indexed Pi-function over the sample/block product type)
Source: Mathlib Pi-function, natural-number index, and product type APIs
Used in: stochastic block mirror descent iid product stream for oracle samples and sampled blocks
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic block mirror descent -/
abbrev blockSamplePath (S I : Type*) : Type _ :=
  ℕ → S × I

namespace SOptLib

/-- The length-`t` sample window cut out of a Nat-indexed sample stream at an offset.

For a stochastic sample stream `sample : ℕ → Ω → S`, `sampleWindow sample offset t`
is the `Fin t`-indexed block `r ↦ sample (offset + r.val)`.  This keeps finite
sample blocks in Pi-vector form, which is the shape used by product-law and
finite-prefix determinism arguments.

Layer: Model | Concept: Sampling
Proof: (definitional construction; offset Nat-indexed stream restricted to a Fin-indexed window)
Source: Mathlib natural-number indices, Fin coordinates, and Pi-function APIs
Used in: randomized accelerated proximal-point fixed inner run finite sample blocks
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  randomized accelerated proximal-point method -/
def sampleWindow {Ω S : Type*} (sample : ℕ → Ω → S) (offset t : ℕ) : Ω → Fin t → S :=
  fun ω r => sample (offset + r.1) ω

/-- A sample window is the finite coordinate block cut out of the underlying stream.

Layer: Model | Gap: Level 0 (sample-window characterization)
Proof: by rfl after unfolding sampleWindow
Source: Mathlib natural-number indices, Fin coordinates, and Pi-function APIs
Used in: randomized accelerated proximal-point fixed inner run finite sample blocks
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  randomized accelerated proximal-point method -/
@[simp] theorem sampleWindow_def {Ω S : Type*} (sample : ℕ → Ω → S) (offset t : ℕ) :
    sampleWindow sample offset t = fun ω r => sample (offset + r.1) ω := rfl

/-- A sample window evaluates by reading the underlying stream at `offset + r.val`.

Layer: Model | Gap: Level 0 (sample-window coordinate unfolding)
Proof: by rfl after unfolding sampleWindow
Source: Mathlib natural-number indices, Fin coordinates, and Pi-function APIs
Used in: randomized accelerated proximal-point fixed inner run finite sample blocks
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  randomized accelerated proximal-point method -/
@[simp] theorem sampleWindow_apply {Ω S : Type*} (sample : ℕ → Ω → S)
    (offset t : ℕ) (ω : Ω) (r : Fin t) :
    sampleWindow sample offset t ω r = sample (offset + r.1) ω := rfl

/-- The window starting at `offset + 1` is the tail of the window starting at `offset`.

Layer: Model | Gap: Level 0 (sample-window offset successor reindexing)
Proof: extensionality and natural-number arithmetic after unfolding `sampleWindow`
Source: Mathlib natural-number indices, Fin coordinates, and Pi-function APIs
Used in: finite-prefix arguments that drop the first sample of a stochastic block
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  randomized accelerated proximal-point method -/
theorem sampleWindow_offset_succ_eq_tail {Ω S : Type*} (sample : ℕ → Ω → S)
    (offset t : ℕ) :
    (fun ω r => sampleWindow sample (offset + 1) t ω r) =
      fun ω r => sampleWindow sample offset (t + 1) ω r.succ := by
  funext ω r
  simp [sampleWindow, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

open MeasureTheory

/-- A two-index sample array is coordinatewise measurable and independent after
flattening to a 1-based Nat-indexed stream.

For mini-batch algorithms whose samples are written as `xi k j`, this predicate
packages the local coordinate measurability together with independence of the
stream `n ↦ xi ((Nat.unpair n).1 + 1) ((Nat.unpair n).2 + 1)`.

Layer: Model | Concept: Sampling
Proof: (definitional construction; conjunction of coordinate measurability and
  independence of the 1-based `Nat.unpair` flattened stream)
Source: Mathlib probability independence API for `iIndepFun` and natural-number
  pairing APIs
Used in: stochastic conditional-gradient mini-batch sample stream used to build
  prefix filtrations and fresh-sample independence bridges
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
def twoIndexSampleBasis
    {Omega Sample : Type*} [MeasurableSpace Omega] [MeasurableSpace Sample]
    (xi : Nat -> Nat -> Omega -> Sample) (mu : Measure Omega) : Prop :=
  (forall k j : Nat, Measurable (xi k j)) /\
    ProbabilityTheory.iIndepFun
      (fun (n : Nat) (omega : Omega) =>
        xi ((Nat.unpair n).1 + 1) ((Nat.unpair n).2 + 1) omega)
      mu

/-- The two-index sample-basis predicate unfolds to coordinate measurability
and independence of the 1-based flattened stream.

Layer: Model | Gap: Level 0 (two-index sample-basis definition)
Proof: by rfl after unfolding `twoIndexSampleBasis`.
Source: Mathlib probability independence API for `iIndepFun` and natural-number
  pairing APIs
Used in: stochastic conditional-gradient mini-batch sample stream used to build
  prefix filtrations and fresh-sample independence bridges
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
@[simp]
theorem twoIndexSampleBasis_iff
    {Omega Sample : Type*} [MeasurableSpace Omega] [MeasurableSpace Sample]
    (xi : Nat -> Nat -> Omega -> Sample) (mu : Measure Omega) :
    twoIndexSampleBasis xi mu <->
      (forall k j : Nat, Measurable (xi k j)) /\
        ProbabilityTheory.iIndepFun
          (fun (n : Nat) (omega : Omega) =>
            xi ((Nat.unpair n).1 + 1) ((Nat.unpair n).2 + 1) omega)
          mu := by
  rfl

/-- Coordinate projections of a two-index sample basis are measurable.

Layer: Model | Gap: Level 0 (two-index sample-basis measurability projection)
Proof: projection from `twoIndexSampleBasis`.
Source: Mathlib measurable random-variable API and conjunction projections
Used in: stochastic conditional-gradient mini-batch sample stream used to build
  prefix filtrations and fresh-sample independence bridges
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem twoIndexSampleBasis.measurable
    {Omega Sample : Type*} [MeasurableSpace Omega] [MeasurableSpace Sample]
    {xi : Nat -> Nat -> Omega -> Sample} {mu : Measure Omega}
    (hxi : twoIndexSampleBasis xi mu) (k j : Nat) :
    Measurable (xi k j) :=
  hxi.1 k j

/-- The 1-based `Nat.unpair` flattening of a two-index sample basis is
independent.

Layer: Model | Gap: Level 0 (two-index sample-basis independence projection)
Proof: projection from `twoIndexSampleBasis`.
Source: Mathlib probability independence API for `iIndepFun` and conjunction
  projections
Used in: stochastic conditional-gradient mini-batch sample stream used to build
  prefix filtrations and fresh-sample independence bridges
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem twoIndexSampleBasis.iIndepFun_flatten
    {Omega Sample : Type*} [MeasurableSpace Omega] [MeasurableSpace Sample]
    {xi : Nat -> Nat -> Omega -> Sample} {mu : Measure Omega}
    (hxi : twoIndexSampleBasis xi mu) :
    ProbabilityTheory.iIndepFun
      (fun (n : Nat) (omega : Omega) =>
        xi ((Nat.unpair n).1 + 1) ((Nat.unpair n).2 + 1) omega)
      mu :=
  hxi.2

/-- Nat-indexed stream of finite mini-batches with samples in `A`.

For batch size `b`, `miniBatchSamplePath b A` is the path space whose `k`th
coordinate is a `Fin b`-indexed mini-batch of samples from `A`.  This is the
canonical Pi-function representation used when stochastic algorithms address
samples by iteration `k` and within-batch coordinate `r`.

Layer: Model | Concept: Sampling
Proof: (definitional construction; Nat-indexed Pi-function over finite batch coordinates)
Source: Mathlib natural-number index, Fin coordinate, and Pi-function APIs
Used in: stochastic finite-sum recursive gradient-estimator mini-batch streams
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional-gradient sliding -/
abbrev miniBatchSamplePath (b : Nat) (A : Type*) : Type _ :=
  (k : Nat) -> Fin b -> A

/-- The canonical iid law on Nat-indexed finite mini-batches with marginal `mu`.

For a measurable sample space `A`, `iidMiniBatchSampleLaw b mu` is the nested
infinite product measure on `miniBatchSamplePath b A`; every coordinate
`(k, r)` has marginal `mu`, and the coordinates are jointly independent when
`mu` is a probability measure.

Layer: Model | Concept: Probability
Proof: (definitional construction; nested constant-family infinite product measure over Nat and Fin coordinates)
Source: Mathlib probability product measures and infinite product construction
Used in: stochastic finite-sum recursive gradient-estimator mini-batch source law
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional-gradient sliding -/
noncomputable def iidMiniBatchSampleLaw
    {A : Type*} [MeasurableSpace A] (b : Nat) (mu : Measure A) :
    Measure (miniBatchSamplePath b A) :=
  Measure.infinitePi (fun _ : Nat => Measure.infinitePi (fun _ : Fin b => mu))

/-- The iid mini-batch sample law is the nested infinite product over time and
within-batch coordinates.

Layer: Model | Gap: Level 0 (iid mini-batch law unfolding)
Proof: by rfl after unfolding `iidMiniBatchSampleLaw`.
Source: Mathlib probability product measures and infinite product construction
Used in: stochastic finite-sum recursive gradient-estimator mini-batch source law
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional-gradient sliding -/
@[simp]
theorem iidMiniBatchSampleLaw_def
    {A : Type*} [MeasurableSpace A] (b : Nat) (mu : Measure A) :
    iidMiniBatchSampleLaw b mu =
      Measure.infinitePi (fun _ : Nat => Measure.infinitePi (fun _ : Fin b => mu)) := rfl

/-- The iid mini-batch law of a probability marginal is a probability measure.

Layer: Model | Gap: Level 0 (iid mini-batch probability measure)
Proof: unfold `iidMiniBatchSampleLaw` and use Mathlib's probability-measure
  instance for nested infinite products.
Source: Mathlib probability product measures and `IsProbabilityMeasure` instances
Used in: stochastic finite-sum recursive gradient-estimator mini-batch source law
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional-gradient sliding -/
@[instance]
theorem iidMiniBatchSampleLaw_isProbabilityMeasure
    {A : Type*} [MeasurableSpace A] (b : Nat) (mu : Measure A) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (iidMiniBatchSampleLaw b mu) := by
  unfold iidMiniBatchSampleLaw
  infer_instance

/-- Coordinates of the iid mini-batch law are jointly independent.

Layer: Model | Gap: Level 0 (iid mini-batch coordinate independence)
Proof: unfold `iidMiniBatchSampleLaw` and apply Mathlib's uncurry independence
  theorem for nested infinite product measures.
Source: Mathlib probability independence API for infinite product measures
Used in: stochastic finite-sum recursive gradient-estimator mini-batch source law
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional-gradient sliding -/
theorem iidMiniBatchSampleLaw_iIndepFun_eval
    {A : Type*} [MeasurableSpace A] (b : Nat) (mu : Measure A) [IsProbabilityMeasure mu] :
    ProbabilityTheory.iIndepFun
      (fun (kr : Nat × Fin b) (omega : miniBatchSamplePath b A) => omega kr.1 kr.2)
      (iidMiniBatchSampleLaw b mu) := by
  unfold iidMiniBatchSampleLaw
  simpa [miniBatchSamplePath] using
    (ProbabilityTheory.iIndepFun_uncurry_infinitePi'
      (μ := fun _ : Nat => fun _ : Fin b => mu)
      (X := fun (_ : Nat) (_ : Fin b) (a : A) => a)
      (by intro k r; exact measurable_id))

/-- Every coordinate projection of the iid mini-batch law has marginal law `mu`.

Layer: Model | Gap: Level 0 (iid mini-batch coordinate marginal law)
Proof: unfold `iidMiniBatchSampleLaw`, map through the outer coordinate
  projection, then specialize `Measure.infinitePi_map_eval` to the inner
  finite-batch coordinate.
Source: Mathlib probability product measures and coordinate marginal API
Used in: stochastic finite-sum recursive gradient-estimator mini-batch source law
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional-gradient sliding -/
theorem iidMiniBatchSampleLaw_map_eval
    {A : Type*} [MeasurableSpace A] (b : Nat) (mu : Measure A) [IsProbabilityMeasure mu]
    (k : Nat) (r : Fin b) :
    Measure.map (fun omega : miniBatchSamplePath b A => omega k r)
        (iidMiniBatchSampleLaw b mu) = mu := by
  unfold iidMiniBatchSampleLaw
  change Measure.map
      ((fun batch : Fin b → A => batch r) ∘
        (fun omega : miniBatchSamplePath b A => omega k))
      (Measure.infinitePi fun _ : Nat =>
        Measure.infinitePi fun _ : Fin b => mu) = mu
  rw [← MeasureTheory.Measure.map_map]
  · have houter :
        Measure.map (fun omega : miniBatchSamplePath b A => omega k)
            (Measure.infinitePi fun _ : Nat =>
              Measure.infinitePi fun _ : Fin b => mu) =
          Measure.infinitePi (fun _ : Fin b => mu) := by
      simpa [miniBatchSamplePath] using
        (MeasureTheory.Measure.infinitePi_map_eval
          (μ := fun _ : Nat => Measure.infinitePi fun _ : Fin b => mu) k)
    rw [houter]
    simpa using
      (MeasureTheory.Measure.infinitePi_map_eval
        (μ := fun _ : Fin b => mu) r)
  · exact measurable_pi_apply r
  · fun_prop

/-- The iid mini-batch law is a probability measure with independent
coordinates and common marginal `mu`.

Layer: Model | Gap: Level 0 (iid mini-batch sample-law specification)
Proof: combine the probability-measure instance, uncurry independence theorem,
  and coordinate marginal theorem for the nested product law.
Source: Mathlib probability product measures and independence APIs
Used in: stochastic finite-sum recursive gradient-estimator mini-batch source law
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional-gradient sliding -/
theorem iidMiniBatchSampleLaw_spec
    {A : Type*} [MeasurableSpace A] (b : Nat) (mu : Measure A) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (iidMiniBatchSampleLaw b mu) ∧
      ProbabilityTheory.iIndepFun
        (fun (kr : Nat × Fin b) (omega : miniBatchSamplePath b A) => omega kr.1 kr.2)
        (iidMiniBatchSampleLaw b mu) ∧
      ∀ k : Nat, ∀ r : Fin b,
        Measure.map (fun omega : miniBatchSamplePath b A => omega k r)
          (iidMiniBatchSampleLaw b mu) = mu := by
  exact ⟨inferInstance, iidMiniBatchSampleLaw_iIndepFun_eval b mu,
    iidMiniBatchSampleLaw_map_eval b mu⟩

/-- A path law is iid across Nat-by-Fin mini-batch coordinates with marginal `mu`.

For a candidate law `P` on `miniBatchSamplePath b A`, this specification records
that `P` is a probability measure, that all coordinates `(k, r)` are jointly
independent, and that every coordinate projection has common marginal `mu`.

Layer: Model | Concept: Probability
Proof: (definitional construction; conjunction of probability, coordinate independence, and common marginal laws)
Source: Mathlib probability independence API and measure-map coordinate marginal API
Used in: stochastic finite-sum recursive gradient-estimator mini-batch source law
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional-gradient sliding -/
def miniBatchIidLawSpec
    {A : Type*} [MeasurableSpace A] (b : Nat) (mu : Measure A)
    (P : Measure (miniBatchSamplePath b A)) : Prop :=
  IsProbabilityMeasure P ∧
    ProbabilityTheory.iIndepFun
      (fun (kr : Nat × Fin b) (omega : miniBatchSamplePath b A) => omega kr.1 kr.2) P ∧
    ∀ k : Nat, ∀ r : Fin b,
      Measure.map (fun omega : miniBatchSamplePath b A => omega k r) P = mu

@[simp] theorem miniBatchIidLawSpec_def
    {A : Type*} [MeasurableSpace A] (b : Nat) (mu : Measure A)
    (P : Measure (miniBatchSamplePath b A)) :
    miniBatchIidLawSpec b mu P ↔
      IsProbabilityMeasure P ∧
        ProbabilityTheory.iIndepFun
          (fun (kr : Nat × Fin b) (omega : miniBatchSamplePath b A) => omega kr.1 kr.2) P ∧
        ∀ k : Nat, ∀ r : Fin b,
          Measure.map (fun omega : miniBatchSamplePath b A => omega k r) P = mu :=
  Iff.rfl

theorem miniBatchIidLawSpec.isProbabilityMeasure
    {A : Type*} [MeasurableSpace A] {b : Nat} {mu : Measure A}
    {P : Measure (miniBatchSamplePath b A)}
    (h : miniBatchIidLawSpec b mu P) :
    IsProbabilityMeasure P :=
  h.1

theorem miniBatchIidLawSpec.iIndepFun_eval
    {A : Type*} [MeasurableSpace A] {b : Nat} {mu : Measure A}
    {P : Measure (miniBatchSamplePath b A)}
    (h : miniBatchIidLawSpec b mu P) :
    ProbabilityTheory.iIndepFun
      (fun (kr : Nat × Fin b) (omega : miniBatchSamplePath b A) => omega kr.1 kr.2) P :=
  h.2.1

theorem miniBatchIidLawSpec.map_eval
    {A : Type*} [MeasurableSpace A] {b : Nat} {mu : Measure A}
    {P : Measure (miniBatchSamplePath b A)}
    (h : miniBatchIidLawSpec b mu P) (k : Nat) (r : Fin b) :
    Measure.map (fun omega : miniBatchSamplePath b A => omega k r) P = mu :=
  h.2.2 k r


/-- Nat-by-Nat sample path with values in `A`.

This is the canonical carrier for stochastic algorithms whose random source is
addressed first by an outer epoch and then by an inner iteration.

Layer: Model | Concept: Sampling
Proof: (definitional construction; Nat-by-Nat Pi-function over sample values)
Source: Mathlib natural-number index and Pi-function type APIs
Used in: variance-reduced accelerated gradient descent epoch and inner-loop component draws
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  variance-reduced accelerated gradient descent -/
abbrev twoIndexSamplePath (A : Type*) : Type _ :=
  Nat -> Nat -> A

/-- The canonical iid law on two Nat-indexed coordinates with marginal `mu`.

For a measurable sample space `A`, `iidTwoIndexSampleLaw mu` is the nested
infinite product measure on arrays `omega k t`, with a Nat-indexed outer
coordinate and a Nat-indexed inner coordinate.

Layer: Model | Concept: Probability
Proof: (definitional construction; nested constant-family infinite product law via `iidStreamLaw`)
Source: Mathlib probability product measures and infinite product construction
Used in: variance-reduced accelerated gradient descent epoch and inner-loop component draws
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  variance-reduced accelerated gradient descent -/
noncomputable def iidTwoIndexSampleLaw
    {A : Type*} [MeasurableSpace A] (mu : MeasureTheory.Measure A) :
    MeasureTheory.Measure (twoIndexSamplePath A) :=
  MeasureTheory.Measure.infinitePi (fun _ : Nat =>
    MeasureTheory.Measure.infinitePi (fun _ : Nat => mu))

@[simp]
theorem iidTwoIndexSampleLaw_def
    {A : Type*} [MeasurableSpace A] (mu : MeasureTheory.Measure A) :
    iidTwoIndexSampleLaw mu =
      MeasureTheory.Measure.infinitePi (fun _ : Nat =>
        MeasureTheory.Measure.infinitePi (fun _ : Nat => mu)) := rfl

/-- The iid two-index law of a probability marginal is a probability measure.

Layer: Model | Gap: Level 0 (iid two-index product-law probability measure)
Proof: unfold `iidTwoIndexSampleLaw` and use the existing probability-measure
  instance for nested iid stream laws.
Source: Mathlib probability product measures and `IsProbabilityMeasure` instances
Used in: variance-reduced accelerated gradient descent epoch and inner-loop component draws
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  variance-reduced accelerated gradient descent -/
@[instance]
theorem iidTwoIndexSampleLaw_isProbabilityMeasure
    {A : Type*} [MeasurableSpace A] (mu : MeasureTheory.Measure A)
    [MeasureTheory.IsProbabilityMeasure mu] :
    MeasureTheory.IsProbabilityMeasure (iidTwoIndexSampleLaw mu) := by
  unfold iidTwoIndexSampleLaw
  infer_instance

/-- Flattened coordinates of the iid two-index law are jointly independent.

Layer: Model | Gap: Level 0 (iid Nat-by-Nat coordinate independence)
Proof: unfold the nested stream law and apply Mathlib's uncurry independence
  theorem for nested infinite product measures.
Source: Mathlib probability independence API for infinite product measures
Used in: variance-reduced accelerated gradient descent strict-history freshness for component draws
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  variance-reduced accelerated gradient descent -/
theorem iidTwoIndexSampleLaw_iIndepFun_eval
    {A : Type*} [MeasurableSpace A] (mu : MeasureTheory.Measure A)
    [MeasureTheory.IsProbabilityMeasure mu] :
    ProbabilityTheory.iIndepFun
      (fun (q : Prod Nat Nat) (omega : twoIndexSamplePath A) => omega q.1 q.2)
      (iidTwoIndexSampleLaw mu) := by
  unfold iidTwoIndexSampleLaw
  simpa [twoIndexSamplePath] using
    (ProbabilityTheory.iIndepFun_uncurry_infinitePi'
      (μ := fun _ : Nat => fun _ : Nat => mu)
      (X := fun (_ : Nat) (_ : Nat) (a : A) => a)
      (by intro k t; exact measurable_id))

/-- Every coordinate projection of the iid two-index law has marginal law `mu`.

Layer: Model | Gap: Level 0 (iid Nat-by-Nat coordinate marginal law)
Proof: map through the outer coordinate projection, then specialize the
  one-index iid stream marginal theorem to the inner coordinate.
Source: Mathlib probability product measures and coordinate marginal API
Used in: variance-reduced accelerated gradient descent one-draw component-law transport
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  variance-reduced accelerated gradient descent -/
theorem iidTwoIndexSampleLaw_map_eval
    {A : Type*} [MeasurableSpace A] (mu : MeasureTheory.Measure A)
    [MeasureTheory.IsProbabilityMeasure mu] (k t : Nat) :
    MeasureTheory.Measure.map (fun omega : twoIndexSamplePath A => omega k t)
        (iidTwoIndexSampleLaw mu) = mu := by
  unfold iidTwoIndexSampleLaw
  change MeasureTheory.Measure.map
      ((fun stream : Nat -> A => stream t) ∘
        (fun omega : twoIndexSamplePath A => omega k))
      (MeasureTheory.Measure.infinitePi fun _ : Nat =>
        MeasureTheory.Measure.infinitePi fun _ : Nat => mu) = mu
  rw [← MeasureTheory.Measure.map_map]
  · have houter :
        MeasureTheory.Measure.map (fun omega : twoIndexSamplePath A => omega k)
            (MeasureTheory.Measure.infinitePi fun _ : Nat =>
              MeasureTheory.Measure.infinitePi fun _ : Nat => mu) =
          MeasureTheory.Measure.infinitePi (fun _ : Nat => mu) := by
      simpa [twoIndexSamplePath] using
        (MeasureTheory.Measure.infinitePi_map_eval
          (μ := fun _ : Nat => MeasureTheory.Measure.infinitePi fun _ : Nat => mu) k)
    rw [houter]
    simpa using
      (MeasureTheory.Measure.infinitePi_map_eval
        (μ := fun _ : Nat => mu) t)
  · exact measurable_pi_apply t
  · fun_prop

/-- A fixed outer coordinate of the iid two-index law is an iid inner stream.

Layer: Model | Gap: Level 0 (fixed-epoch iid inner-stream independence)
Proof: precompose flattened two-index coordinate independence with the
  injective map `t |-> (k, t)`.
Source: Mathlib probability `iIndepFun.precomp` and product-coordinate APIs
Used in: variance-reduced accelerated gradient descent fixed-epoch fresh component draws
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  variance-reduced accelerated gradient descent -/
theorem iidTwoIndexSampleLaw_fixed_left_iIndepFun_eval
    {A : Type*} [MeasurableSpace A] (mu : MeasureTheory.Measure A)
    [MeasureTheory.IsProbabilityMeasure mu] (k : Nat) :
    ProbabilityTheory.iIndepFun
      (fun (t : Nat) (omega : twoIndexSamplePath A) => omega k t)
      (iidTwoIndexSampleLaw mu) := by
  have hinj : Function.Injective (fun t : Nat => (k, t)) := by
    intro a b h
    exact congrArg Prod.snd h
  simpa using
    (iidTwoIndexSampleLaw_iIndepFun_eval (mu := mu)).precomp hinj

/-- The iid two-index law is a probability measure with independent coordinates
and common marginal `mu`.

Layer: Model | Gap: Level 0 (iid two-index sample-law specification)
Proof: combine the probability-measure instance, flattened coordinate
  independence theorem, and coordinate marginal theorem for the nested law.
Source: Mathlib probability product measures, coordinate marginal, and independence APIs
Used in: variance-reduced accelerated gradient descent canonical two-index component sample law
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  variance-reduced accelerated gradient descent -/
theorem iidTwoIndexSampleLaw_spec
    {A : Type*} [MeasurableSpace A] (mu : MeasureTheory.Measure A)
    [MeasureTheory.IsProbabilityMeasure mu] :
    MeasureTheory.IsProbabilityMeasure (iidTwoIndexSampleLaw mu) ∧
      ProbabilityTheory.iIndepFun
        (fun (q : Prod Nat Nat) (omega : twoIndexSamplePath A) => omega q.1 q.2)
        (iidTwoIndexSampleLaw mu) ∧
      forall k t : Nat,
        MeasureTheory.Measure.map (fun omega : twoIndexSamplePath A => omega k t)
          (iidTwoIndexSampleLaw mu) = mu := by
  exact ⟨inferInstance, iidTwoIndexSampleLaw_iIndepFun_eval mu,
    iidTwoIndexSampleLaw_map_eval mu⟩

/-- Extend a finite sample window to a full Nat-indexed stream by a default value.

The window `pref : Fin len -> A` is placed at indices
`offset, offset + 1, ..., offset + len - 1`; all other stream coordinates use
`sampleDefault`.

Layer: Model | Concept: Sampling
Proof: (definitional construction; Fin-indexed window inserted into a Nat-indexed
  stream with a default value outside the window)
Source: Mathlib natural-number intervals, Fin coordinate, and Pi-function APIs
Used in: random primal-dual gradient finite-prefix expectation sections and
  generated-process determinism over a reconstructed full sample stream
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
def extendSampleWindow {A : Type*} (offset len : ℕ)
    (pref : Fin len → A) (sampleDefault : A) :
    ℕ → A :=
  fun t =>
    if h : offset ≤ t ∧ t < offset + len then
      pref ⟨t - offset, by omega⟩
    else
      sampleDefault

@[simp]
theorem extendSampleWindow_def {A : Type*} (offset len : ℕ)
    (pref : Fin len → A) (sampleDefault : A) :
    extendSampleWindow offset len pref sampleDefault =
      (fun t =>
        if h : offset ≤ t ∧ t < offset + len then
          pref ⟨t - offset, by omega⟩
        else
          sampleDefault) := rfl

/-- A one-based finite prefix reads back from its extended sample window.

This is the specialization of `extendSampleWindow` for prefix types indexed by
`{t : Nat // 1 <= t /\ t <= k}` rather than by `Fin k`.

Layer: Model | Gap: Level 0 (one-based sample-window extension evaluation)
Proof: unfold `extendSampleWindow`, discharge the one-based window membership
  by arithmetic, and identify the resulting subtype indices extensionally.
Source: Mathlib natural-number intervals, Fin coordinate, subtype extensionality,
  and Pi-function APIs
Used in: random primal-dual gradient generated-process determinism over a
  one-based reconstructed sample prefix
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
@[simp]
theorem extendSampleWindow_one_based_apply {A : Type*}
    {k t : ℕ} (pref : {t : ℕ // 1 ≤ t ∧ t ≤ k} → A)
    (sampleDefault : A)
    (ht : 1 ≤ t) (htk : t ≤ k) :
    extendSampleWindow 1 k (fun r : Fin k => pref ⟨r.1 + 1, by omega⟩)
      sampleDefault t = pref ⟨t, ht, htk⟩ := by
  simp [extendSampleWindow, ht, show t < 1 + k by omega, Nat.sub_add_cancel ht]

/-- Restricting an extended finite sample window at the same offset recovers it.

Layer: Model | Gap: Level 0 (sample-window extension section)
Proof: extensionality over finite coordinates, then unfold `sampleWindow` and
  `extendSampleWindow`; the remaining obligations are natural-number arithmetic.
Source: Mathlib natural-number intervals, Fin coordinate, and Pi-function APIs
Used in: random primal-dual gradient finite-prefix expectation sections and
  generated-process determinism over a reconstructed full sample stream
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
@[simp]
theorem sampleWindow_extendSampleWindow {A : Type*}
    (offset len : ℕ) (pref : Fin len → A)
    (sampleDefault : A) :
    sampleWindow (fun t (_ : Unit) => extendSampleWindow offset len pref sampleDefault t)
      offset len () = pref := by
  funext r
  simp [sampleWindow, extendSampleWindow]

/-- Expectation of a full-path observable after deterministic finite-prefix extension.

Given a path law `μ`, a finite-prefix map `prefix`, and an extension
`extend : Pref → Ω`, this is the expectation of `F` over the pushed-forward prefix
law, evaluated on the reconstructed full path.

Layer: Model | Concept: Filtration
Proof: (definitional construction; Bochner integral over the pushforward prefix law
  with the observable precomposed by deterministic extension)
Source: Mathlib measure theory Bochner integral and pushforward-measure APIs
Used in: finite-prefix stochastic-process expectations before generated-iterate
  determinism rewrites
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
noncomputable def finitePrefixExpectation
    {Ω Pref : Type*} [MeasurableSpace Ω] [MeasurableSpace Pref]
    {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    (μ : Measure Ω) (prefixMap : Ω → Pref) (extend : Pref → Ω) (F : Ω → R) : R :=
  ∫ pref, F (extend pref) ∂Measure.map prefixMap μ

/-- The finite-prefix expectation unfolds to its pushforward-law integral.

Layer: Model | Gap: Level 0 (finite-prefix expectation formula)
Proof: by rfl after unfolding `finitePrefixExpectation`.
Source: Mathlib measure theory Bochner integral and pushforward-measure APIs
Used in: finite-prefix stochastic-process expectations before generated-iterate
  determinism rewrites
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
@[simp]
theorem finitePrefixExpectation_def
    {Ω Pref : Type*} [MeasurableSpace Ω] [MeasurableSpace Pref]
    {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    (μ : Measure Ω) (prefixMap : Ω → Pref) (extend : Pref → Ω) (F : Ω → R) :
    finitePrefixExpectation μ prefixMap extend F =
      ∫ pref, F (extend pref) ∂Measure.map prefixMap μ := by
  rfl

/-- Prefix-observable finite-prefix expectations integrate directly over the prefix law.

If `extend` is a right inverse to `prefix`, then an observable that depends only
on `prefix ω` loses the deterministic extension under `finitePrefixExpectation`.

Layer: Model | Gap: Level 0 (finite-prefix section expectation)
Proof: unfold `finitePrefixExpectation` and rewrite the section identity
  `prefix (extend pref) = pref` under the pushforward-law integral.
Source: Mathlib measure theory Bochner integral and pushforward-measure APIs
Used in: finite-prefix stochastic-process expectations of prefix-measurable
  observables before generated-iterate determinism rewrites
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem finitePrefixExpectation_of_prefixObservable
    {Ω Pref : Type*} [MeasurableSpace Ω] [MeasurableSpace Pref]
    {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    (μ : Measure Ω) (prefixMap : Ω → Pref) (extend : Pref → Ω)
    (hsection : ∀ pref, prefixMap (extend pref) = pref) (ψ : Pref → R) :
    finitePrefixExpectation μ prefixMap extend (fun ω => ψ (prefixMap ω)) =
      ∫ pref, ψ pref ∂Measure.map prefixMap μ := by
  simp [finitePrefixExpectation, hsection]

/-- Finite-prefix expectation is additive for integrable reconstructed observables.

This is the finite-prefix-expectation form of Bochner binary additivity.  It
keeps stochastic-process proofs at the prefix-expectation abstraction boundary
instead of unfolding to an integral over the pushed-forward prefix law.

Layer: Model | Gap: Level 0 (finite-prefix expectation binary additivity)
Proof: unfold `finitePrefixExpectation` and apply Mathlib's
  `MeasureTheory.integral_add` to the pushed-forward prefix law.
Source: Mathlib measure theory Bochner integral additivity
Used in: random primal-dual gradient finite-prefix saddle-gap decomposition
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem finitePrefixExpectation_add
    {Ω Pref R : Type*} [MeasurableSpace Ω] [MeasurableSpace Pref]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (μ : Measure Ω) (prefixMap : Ω → Pref) (extend : Pref → Ω)
    (F G : Ω → R)
    (hF : Integrable (fun pref : Pref => F (extend pref)) (Measure.map prefixMap μ))
    (hG : Integrable (fun pref : Pref => G (extend pref)) (Measure.map prefixMap μ)) :
    finitePrefixExpectation μ prefixMap extend (fun ω => F ω + G ω) =
      finitePrefixExpectation μ prefixMap extend F +
        finitePrefixExpectation μ prefixMap extend G := by
  exact MeasureTheory.integral_add hF hG

/-- Finite-prefix expectation commutes with deterministic scalar multiplication.

This is the finite-prefix-expectation form of scalar linearity for `RCLike`
observables.  It keeps stochastic-process proofs at the prefix-expectation
abstraction boundary instead of unfolding to an integral over the pushed-forward
prefix law.

Layer: Model | Gap: Level 0 (finite-prefix expectation scalar linearity)
Proof: unfold `finitePrefixExpectation` and apply Mathlib's
  `MeasureTheory.integral_const_mul` to the pushed-forward prefix law.
Source: Mathlib measure theory Bochner integral scalar multiplication over
  real-or-complex scalar fields
Used in: random primal-dual gradient finite-prefix weighted saddle-gap decomposition
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem finitePrefixExpectation_const_mul
    {Ω Pref L : Type*} [MeasurableSpace Ω] [MeasurableSpace Pref] [RCLike L]
    (μ : Measure Ω) (prefixMap : Ω → Pref) (extend : Pref → Ω)
    (c : L) (F : Ω → L) :
    finitePrefixExpectation μ prefixMap extend (fun ω => c * F ω) =
      c * finitePrefixExpectation μ prefixMap extend F := by
  exact MeasureTheory.integral_const_mul c
    (fun pref : Pref => F (extend pref))

/-- Finite-prefix expectation is subtractive for integrable reconstructed observables.

This is the finite-prefix-expectation form of Bochner subtraction linearity. It
keeps stochastic-process proofs at the prefix-expectation abstraction boundary
instead of unfolding to an integral over the pushed-forward prefix law.

Layer: Model | Gap: Level 0 (finite-prefix expectation subtraction linearity)
Proof: unfold `finitePrefixExpectation` and apply Mathlib's
  `MeasureTheory.integral_sub` to the pushed-forward prefix law.
Source: Mathlib measure theory Bochner integral subtraction
Used in: random primal-dual gradient finite-prefix saddle-gap decomposition
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem finitePrefixExpectation_sub
    {Ω Pref R : Type*} [MeasurableSpace Ω] [MeasurableSpace Pref]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (μ : Measure Ω) (prefixMap : Ω → Pref) (extend : Pref → Ω)
    (F G : Ω → R)
    (hF : Integrable (fun pref : Pref => F (extend pref)) (Measure.map prefixMap μ))
    (hG : Integrable (fun pref : Pref => G (extend pref)) (Measure.map prefixMap μ)) :
    finitePrefixExpectation μ prefixMap extend (fun ω => F ω - G ω) =
      finitePrefixExpectation μ prefixMap extend F -
        finitePrefixExpectation μ prefixMap extend G := by
  exact MeasureTheory.integral_sub hF hG

/-- Finite-prefix expectation commutes with finite sums of integrable summands.

This is the finite-prefix-expectation form of Bochner finite-sum linearity.  It
keeps stochastic-process proofs at the prefix-expectation abstraction boundary
instead of repeatedly unfolding to an integral over the pushed-forward prefix
law.

Layer: Model | Gap: Level 0 (finite-prefix expectation finite-sum linearity)
Proof: unfold `finitePrefixExpectation` and apply Mathlib's
  `MeasureTheory.integral_finset_sum` to the pushed-forward prefix law.
Source: Mathlib measure theory Bochner integral finite-sum linearity
Used in: random primal-dual gradient finite-window saddle-gap decomposition
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem finitePrefixExpectation_sum_finset
    {Ω Pref ι R : Type*} [MeasurableSpace Ω] [MeasurableSpace Pref]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (μ : Measure Ω) (prefixMap : Ω → Pref) (extend : Pref → Ω)
    (s : Finset ι) (F : ι → Ω → R)
    (hF : ∀ i ∈ s,
      Integrable (fun pref : Pref => F i (extend pref)) (Measure.map prefixMap μ)) :
    finitePrefixExpectation μ prefixMap extend (fun ω => ∑ i ∈ s, F i ω) =
      ∑ i ∈ s, finitePrefixExpectation μ prefixMap extend (F i) := by
  classical
  simpa only [finitePrefixExpectation, Finset.sum_apply] using
    (MeasureTheory.integral_finset_sum (μ := Measure.map prefixMap μ) (s := s)
      (f := fun i pref => F i (extend pref)) hF)

/-- A finite-prefix expectation of a prefix observable is its full-stream integral.

If `extend` is a section for `prefixMap`, then evaluating a prefix observable
through `finitePrefixExpectation` and integrating the same observable composed
with `prefixMap` over the original stream law give the same Bochner integral.

Layer: Model | Gap: Level 0 (finite-prefix observable stream integral bridge)
Proof: first rewrite `finitePrefixExpectation` to the pushed-forward prefix-law
  integral using the section identity, then apply Bochner `MeasureTheory.integral_map`.
Source: Mathlib measure theory Bochner integral and pushforward-measure APIs
Used in: random primal-dual gradient finite-prefix Bregman observable transport
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem finitePrefixExpectation_prefixObservable_eq_integral_comp
    {Ω Pref R : Type*} [MeasurableSpace Ω] [MeasurableSpace Pref]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (μ : Measure Ω) (prefixMap : Ω → Pref) (extend : Pref → Ω)
    (hprefix : AEMeasurable prefixMap μ)
    (hsection : ∀ pref, prefixMap (extend pref) = pref)
    (ψ : Pref → R)
    (hψ : AEStronglyMeasurable ψ (Measure.map prefixMap μ)) :
    finitePrefixExpectation μ prefixMap extend (fun ω => ψ (prefixMap ω)) =
      ∫ ω, ψ (prefixMap ω) ∂μ := by
  calc
    finitePrefixExpectation μ prefixMap extend (fun ω => ψ (prefixMap ω)) =
        ∫ pref, ψ pref ∂Measure.map prefixMap μ := by
          exact finitePrefixExpectation_of_prefixObservable μ prefixMap extend hsection ψ
    _ = ∫ ω, ψ (prefixMap ω) ∂μ := by
          exact MeasureTheory.integral_map hprefix hψ

/-- A finite-prefix expectation of an extension-invariant observable is its full-stream integral.

If replacing a path by the deterministic extension of its prefix leaves `F`
unchanged almost everywhere, then the finite-prefix expectation of `F` equals
the ordinary integral of `F` over the original path law.

Layer: Model | Gap: Level 0 (finite-prefix invariant observable stream integral)
Proof: unfold the finite-prefix expectation and apply Bochner
  `MeasureTheory.integral_map`, then use `MeasureTheory.integral_congr_ae` for
  the extension-invariance hypothesis.
Source: Mathlib measure theory Bochner integral, pushforward-measure, and
  almost-everywhere congruence APIs
Used in: random primal-dual gradient generated-prefix observable transport for
  Bregman and residual scalar terms
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem finitePrefixExpectation_eq_integral_of_extend_prefix_eq
    {Ω Pref R : Type*} [MeasurableSpace Ω] [MeasurableSpace Pref]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (μ : Measure Ω) (prefixMap : Ω → Pref) (extend : Pref → Ω)
    (F : Ω → R)
    (hprefix : AEMeasurable prefixMap μ)
    (hF_meas :
      AEStronglyMeasurable (fun pref : Pref => F (extend pref))
        (Measure.map prefixMap μ))
    (hF : (fun ω => F (extend (prefixMap ω))) =ᵐ[μ] F) :
    finitePrefixExpectation μ prefixMap extend F = ∫ ω, F ω ∂μ := by
  calc
    finitePrefixExpectation μ prefixMap extend F =
        ∫ ω, F (extend (prefixMap ω)) ∂μ := by
          simpa [finitePrefixExpectation] using
            (MeasureTheory.integral_map hprefix hF_meas)
    _ = ∫ ω, F ω ∂μ := by
          exact MeasureTheory.integral_congr_ae hF

/-- Finite-prefix expectation is monotone under pointwise bounds after extension.

If two reconstructed prefix observables are integrable under the prefix law and
`F` is bounded by `G` on every deterministic extension of a prefix, then the
finite-prefix expectation of `F` is bounded by that of `G`.

Layer: Model | Gap: Level 0 (finite-prefix expectation monotonicity)
Proof: unfold `finitePrefixExpectation` and apply Mathlib's
  `MeasureTheory.integral_mono` to the pushed-forward prefix law.
Source: Mathlib measure theory Bochner integral monotonicity APIs
Used in: random primal-dual gradient finite-prefix saddle-gap upper-bound transport
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem finitePrefixExpectation_mono_of_forall_extend
    {Ω Prefix R : Type*} [MeasurableSpace Ω] [MeasurableSpace Prefix]
    [NormedAddCommGroup R] [NormedSpace ℝ R] [PartialOrder R]
    [IsOrderedAddMonoid R] [IsOrderedModule ℝ R] [ClosedIciTopology R]
    (μ : Measure Ω) (prefixMap : Ω → Prefix) (extend : Prefix → Ω)
    (F G : Ω → R)
    (hF : Integrable (fun pref : Prefix => F (extend pref)) (Measure.map prefixMap μ))
    (hG : Integrable (fun pref : Prefix => G (extend pref)) (Measure.map prefixMap μ))
    (h : ∀ pref : Prefix, F (extend pref) ≤ G (extend pref)) :
    finitePrefixExpectation μ prefixMap extend F ≤
      finitePrefixExpectation μ prefixMap extend G := by
  exact MeasureTheory.integral_mono hF hG h

end SOptLib
