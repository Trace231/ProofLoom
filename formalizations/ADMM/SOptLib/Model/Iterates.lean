import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Order.Filter.Extr
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Function
import SOptLib.Model.BlockSampling

open scoped BigOperators
open scoped MeasureTheory

namespace SOptLib

/-- Abstract update-rule bridge for an iterative stochastic process.

Given a raw process `xProcess`, a public iterate view `x`, a sampled oracle view `G`,
and definitional bridges from the public views to the raw process, the raw recursive
update transports to the public update statement.
Layer: Model | Gap: Level 1 (iterate update view bridge)
Proof: pointwise extensionality followed by rewriting the public-view equations.
Source: Mathlib function extensionality and definitional rewriting primitives
Used in: stochastic mirror descent paper iterate recursion
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/steps/0/math
Origin algorithm: Lan stochastic mirror descent -/
theorem iterateProcess
    {Ω T P S D : Type*}
    (next : T → T)
    (xProcess : T → Ω → P)
    (update : P → D → ℝ → P)
    (oracle : P → S → D)
    (ξ : T → Ω → S)
    (γ : T → ℝ)
    (x : T → Ω → P)
    (G : T → Ω → D)
    (stepSize : T → ℝ)
    (h_x : ∀ t, x t = xProcess t)
    (h_G : ∀ t, G t = fun ω => oracle (x t ω) (ξ t ω))
    (h_stepSize : ∀ t, stepSize t = γ t)
    (h_update : ∀ t, xProcess (next t) = fun ω =>
      update (xProcess t ω) (oracle (xProcess t ω) (ξ t ω)) (γ t))
    (t : T) :
    x (next t) = fun ω => update (x t ω) (G t ω) (stepSize t) := by
  funext ω
  have h := congrFun (h_update t) ω
  simp [h_x, h_G, h_stepSize, h]

open scoped BigOperators


/-- Positive natural-number times in a closed output window `[start, stop]`.
Layer: Model | Concept: Iterates
Proof: (definitional construction; positive-time index window for output averaging)
Source: finite output windows over paper time indices
Used in: stochastic mirror descent output denominators
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan stochastic mirror descent -/
def positiveTimeOutputWindowTimes (start stop : ℕ) (hstart : 1 ≤ start) :
    Finset {t : ℕ // 1 ≤ t} := by
  classical
  let e : {t : ℕ // t ∈ Finset.Icc start stop} ↪ {t : ℕ // 1 ≤ t} :=
    { toFun := fun t => ⟨t.1, le_trans hstart (Finset.mem_Icc.mp t.2).1⟩
      inj' := by
        intro a b h
        exact Subtype.ext (by simpa using congrArg Subtype.val h) }
  exact (Finset.Icc start stop).attach.map e

/-- A positive step-size sequence has positive total weight on every nonempty
closed output window of positive paper time indices.
Layer: Model | Gap: Level 1 (positive output-window denominator)
Proof: the start index belongs to `[start, stop]`, so a finite sum of strictly
  positive weights over the window is strictly positive.
Source: Mathlib finite sums over natural intervals
Used in: stochastic mirror descent weighted-output normalization
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/output/math
Book citation: book/FOML/StochasticMirrorDescent.json#/main_theorem/statement_math
Origin algorithm: Lan stochastic mirror descent -/
theorem positiveTimeOutputWindow
    {M : Type*} [AddCommMonoid M] [Preorder M] [IsOrderedCancelAddMonoid M]
    [AddLeftStrictMono M]
    (γ : {t : ℕ // 1 ≤ t} → M)
    (hγ_pos : ∀ t, 0 < γ t)
    {start stop : ℕ} (hstart : 1 ≤ start) (hle : start ≤ stop) :
    0 < Finset.sum (positiveTimeOutputWindowTimes start stop hstart) γ := by
  classical
  refine Finset.sum_pos (fun t _ => hγ_pos t) ?_
  refine ⟨⟨start, hstart⟩, ?_⟩
  simp [positiveTimeOutputWindowTimes, hle]

/-- Paper-facing time slice of an abstract iterate process.

`iterateProcessView xProcess t` exposes the stochastic iterate process `x_t` at
paper time `t` as the random variable `ω ↦ xProcess t ω`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; paper-time projection of an iterate process)
Source: Lan stochastic mirror descent iterate-process notation
Used in: stochastic mirror descent paper iterate process `x_t`
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
noncomputable def iterateProcessView
    {Ω T P : Type*}
    (xProcess : T → Ω → P) (t : T) : Ω → P :=
  xProcess t

/-- The public iterate view of a raw process is definitionally its time slice.

Layer: Model | Gap: Level 0 (iterate-process time-slice unfolding)
Proof: by rfl after unfolding iterateProcessView.
Source: Mathlib Init equality and Pi-function application APIs
Used in: stochastic mirror descent iterate-process initialization and time-indexed
  state extraction
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
@[simp]
theorem iterateProcessView_eq
    {Ω T P : Type*}
    (xProcess : T → Ω → P) (t : T) :
    iterateProcessView xProcess t = xProcess t := by
  rfl

/-- The public iterate process inherits a constant raw initialization.

If the raw process `x` is initialized at `t0` by the constant point `x0`, then
its public `iterateProcessView` has the same constant value at `t0`.

Layer: Model | Gap: Level 0 (iterate initialization bridge)
Proof: by rfl after unfolding `iterateProcessView`; the stated raw
  initialization is transported by `simpa`.
Source: Mathlib simplifier and definitional unfolding APIs
Used in: stochastic mirror descent iterate initialization at the first time step
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem iterateProcess_init
    {Ω T P : Type*}
    (x : T → Ω → P)
    (t0 : T)
    (x0 : P)
    (h_init : x t0 = fun _ => x0) :
    iterateProcessView x t0 = fun _ => x0 := by
  simpa [iterateProcessView] using h_init

/-- A subtype-valued iterate process belongs to the feasible carrier at every time and sample.

For an iterate process valued in `{z : E // z ∈ X}`, projecting to `E` preserves the
carrier membership proof stored in the subtype.

Layer: Model | Gap: Level 0 (iterate subtype carrier membership)
Proof: projection from the subtype exposes the membership witness; the result is
  exactly the `.2` field of `x t ω`.
Source: Mathlib subtype and Set membership APIs
Used in: stochastic mirror descent iterate feasibility for subtype-valued processes
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem iterateProcess_mem
    {Ω T E : Type*} {X : Set E}
    (x : T → Ω → {z : E // z ∈ X})
    (t : T) (ω : Ω) :
    (x t ω).1 ∈ X := by
  exact (x t ω).2

/-- Map a zero-based recursion counter to the positive paper time `t + 1`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; subtype wrapper pairing `t + 1` with the
  proof that it is at least `1`)
Source: Mathlib natural-number order and subtype APIs
Used in: stochastic mirror descent index bridge from zero-based Lean recursion
  counters to positive paper time
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
def natSuccPositiveTime (t : ℕ) : {n : ℕ // 1 ≤ n} :=
  ⟨t + 1, Nat.succ_le_succ (Nat.zero_le t)⟩

/-- The first positive natural-number paper time.

This distinguished subtype value packages natural time `1` with its proof that it
is a positive paper index.

Layer: Model | Concept: Iterates
Proof: (definitional construction; canonical positive-time subtype witness at
  natural value `1`)
Source: Mathlib natural-number order and subtype APIs
Used in: stochastic mirror descent initialization at the first positive paper
  time
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
def positiveTimeOne : {t : ℕ // 1 ≤ t} :=
  ⟨1, le_rfl⟩

/-- The first positive paper time is represented by the natural number `1`.

Layer: Model | Gap: Level 0 (positive paper-time literal normalization)
Proof: by rfl after unfolding positiveTimeOne.
Source: Mathlib subtype projection and natural-number literal normalization APIs
Used in: stochastic mirror descent iterate indexing at the first paper time
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
@[simp]
theorem positiveTimeOne_val :
    positiveTimeOne.1 = 1 := by
  rfl

/-- The successor operation on positive natural-number paper times.

This model-level time index map sends a positive paper time `t` to `t + 1`
while preserving the proof that the index remains at least one.

Layer: Model | Concept: Iterates
Proof: (definitional construction; subtype-wrapped natural-number successor
  with positivity certified by `Nat.succ_le_succ`)
Source: Mathlib natural-number order and subtype APIs
Used in: stochastic mirror descent successor steps on positive paper times
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
def positiveTimeSucc (t : {n : ℕ // 1 ≤ n}) : {n : ℕ // 1 ≤ n} :=
  ⟨t.1 + 1, Nat.succ_le_succ (Nat.zero_le t.1)⟩

/-- The successor positive paper time increments its natural projection by one.

Layer: Model | Gap: Level 0 (positive paper time successor projection)
Proof: by rfl after unfolding positiveTimeSucc.
Source: Mathlib subtype projections and natural-number arithmetic normalization
Used in: stochastic mirror descent iteration indexing over positive paper times
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
@[simp]
theorem positiveTimeSucc_val (t : {n : ℕ // 1 ≤ n}) :
    (positiveTimeSucc t).1 = t.1 + 1 := by
  rfl

/-- The positive paper time associated to a zero-based natural counter has value `t + 1`.

This exposes the subtype value of `natSuccPositiveTime t`, aligning Lean's zero-based
iterate counter with the paper's one-based time index.

Layer: Model | Gap: Level 0 (paper time indexing normalization)
Proof: by rfl after unfolding natSuccPositiveTime.
Source: Mathlib natural-number arithmetic and subtype value APIs
Used in: stochastic mirror descent iterate indexing and step-size lookup
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
@[simp]
theorem natSuccPositiveTime_val (t : ℕ) :
    (natSuccPositiveTime t).1 = t + 1 := by
  rfl

/-- Total output weight over a finite family of time indices. -/
@[simp] def outputWeightSum
    {W T R : Type*} [AddCommMonoid R]
    (times : W → Finset T) (stepSize : T → R) (w : W) : R :=
  Finset.sum (times w) stepSize

/-- The total output weight is the finite sum of the step-size weights on the output window.

Layer: Model | Gap: Level 0 (output-window weight-sum unfolding)
Proof: unfold the staged output-weight definition; the statement is judgmentally equal to the finite-sum formula.
Source: Mathlib finite sets and big-operator sums over commutative additive monoids
Used in: stochastic mirror descent weighted-output denominator simplification
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
@[simp] theorem outputWeightSum_eq_sum
    {W T R : Type*} [AddCommMonoid R]
    (times : W → Finset T) (stepSize : T → R) (w : W) :
    outputWeightSum times stepSize w = Finset.sum (times w) stepSize := by
  rfl

/-- Total squared output step size over a finite family of time indices. -/
@[simp] def outputSquaredStepSum
    {W T R : Type*} [Semiring R]
    (times : W → Finset T) (stepSize : T → R) (w : W) : R :=
  Finset.sum (times w) (fun t => (stepSize t) ^ 2)

/-- The total squared step-size weight is the finite sum of squared step sizes on the output window.

Layer: Model | Gap: Level 0 (output-window squared step-size sum unfolding)
Proof: unfold the staged squared output-step definition; the statement is judgmentally equal to the finite-sum formula.
Source: Mathlib finite sets, semiring powers, and big-operator sums
Used in: stochastic mirror descent variance and bounded-subgradient error accumulation
Book citation: book/FOML/StochasticMirrorDescent.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
@[simp] theorem outputSquaredStepSum_eq_sum
    {W T R : Type*} [Semiring R]
    (times : W → Finset T) (stepSize : T → R) (w : W) :
    outputSquaredStepSum times stepSize w =
      Finset.sum (times w) (fun t => (stepSize t) ^ 2) := by
  rfl

/-- The paper step-size schedule `γ_t` as a public accessor indexed by time.

This definition names the stochastic mirror descent step-size sequence so later
specs can refer to `stepSize γ t` while remaining definitionally equal to `γ t`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; public step-size sequence wrapper indexed by
  the iteration/time parameter)
Source: Lan stochastic mirror descent step-size schedule notation
Used in: stochastic mirror descent iteration update and prox-step weighting by
  positive time step sizes
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
def stepSize {T R : Type*} (γ : T → R) (t : T) : R :=
  γ t

/-- The stochastic mirror descent step-size accessor is definitionally the underlying schedule.

Layer: Model | Gap: Level 0 (step-size accessor definitional equation)
Proof: by rfl after unfolding stepSize.
Source: Mathlib equality and definitional reduction APIs
Used in: stochastic mirror descent step update rewriting from paper step size to abstract schedule
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem stepSize_eq_gamma
    {T R : Type*}
    (γ : T → R) (t : T) :
    stepSize γ t = γ t := by
  rfl

/-- A step-size wrapper preserves positivity at every iterate.

If the paper assumption gives `0 < γ t` for every index `t`, then the modeled
step size `stepSize γ t` is positive at the same index.

Layer: Model | Gap: Level 0 (step-size positivity wrapper)
Proof: unfold `stepSize` and discharge the goal by the pointwise positivity
  hypothesis using `simp`.
Source: Mathlib real-order simplification and definitional unfolding APIs
Used in: stochastic mirror descent update with positive step-size parameter
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem stepSize_pos
    {T : Type*}
    (γ : T → ℝ)
    (t : T)
    (hγ_pos : ∀ t, 0 < γ t) :
    0 < stepSize γ t := by
  simpa [stepSize] using hγ_pos t

/-- Reindex a finite sum over a positive-time output window as a sum over `Finset.Icc`.

The subtype-indexed output window `{t : ℕ // 1 ≤ t}` carries the same terms as the
underlying natural-number interval once the positivity proof is reconstructed from
`start ≤ n`.

Layer: Model | Gap: Level 0 (finite-sum reindexing over positive output windows)
Proof: expands `positiveTimeOutputWindowTimes` and uses `Finset.sum_bij` after
  `Finset.sum_map`; injectivity is subtype extensionality and the summand equality
  is discharged by `dif_pos`.
Source: Mathlib Finset intervals, big operators, and subtype extensionality APIs
Used in: stochastic mirror descent normalized weighted output averaging over a
  positive natural-number output window
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem sum_positiveTimeOutputWindowTimes_eq_Icc
    {α : Type*} [AddCommMonoid α]
    (start stop : ℕ) (hstart : 1 ≤ start) (_hle : start ≤ stop)
    (φ : {t : ℕ // 1 ≤ t} → α) :
    Finset.sum (positiveTimeOutputWindowTimes start stop hstart) φ =
      Finset.sum (Finset.Icc start stop) (fun n =>
        if hn : n ∈ Finset.Icc start stop then
          φ ⟨n, le_trans hstart (Finset.mem_Icc.mp hn).1⟩
        else 0) := by
  classical
  simp only [positiveTimeOutputWindowTimes, Finset.sum_map]
  refine Finset.sum_bij (fun a _ => (a : ℕ)) ?_ ?_ ?_ ?_
  · intro a _
    exact a.2
  · intro a _ b _ h
    exact Subtype.ext h
  · intro b hb
    exact ⟨⟨b, hb⟩, Finset.mem_attach _ _, rfl⟩
  · intro a _
    rw [dif_pos a.2]
    rfl

/-- A closed output window `[start, stop]` over positive natural-number paper time.

The window stores the positivity and nonemptiness proofs needed to coerce every
natural index in `[start, stop]` into the positive-time subtype `{t : ℕ // 1 ≤ t}`.

Layer: Model | Concept: Iterates
Proof: (structure) the fields bundle the lower positive-time bound and the closed-window nonemptiness condition.
Source: Mathlib finite intervals over natural numbers
Used in: stochastic mirror descent weighted-output normalization over positive paper times
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
structure PositiveOutputWindow where
  start : ℕ
  stop : ℕ
  start_pos : 1 ≤ start
  le_stop : start ≤ stop

namespace PositiveOutputWindow

/-- The initial positive paper time of a closed output window.

Layer: Model | Gap: Level 1 (positive output-window initial time)
Proof: package the start index with the stored positivity proof.
Source: Mathlib subtype construction over natural-number order
Used in: stochastic mirror descent initial Bregman term for output-window telescoping
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
def startTime (w : PositiveOutputWindow) : {t : ℕ // 1 ≤ t} :=
  ⟨w.start, w.start_pos⟩

/-- Positive natural-number paper times in a closed output window.

Layer: Model | Gap: Level 1 (positive output-window time set)
Proof: reuse the canonical `SOptLib` finite interval embedding into positive paper times.
Source: Mathlib finite sums over natural intervals
Used in: stochastic mirror descent weighted-output finite sums
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
def times (w : PositiveOutputWindow) : Finset {t : ℕ // 1 ≤ t} :=
  SOptLib.positiveTimeOutputWindowTimes w.start w.stop w.start_pos

/-- Reindex a finite sum over positive output-window times back to the natural interval.

Layer: Model | Gap: Level 1 (positive output-window reindexing)
Proof: reuse the canonical `SOptLib` reindexing theorem for positive-time output windows.
Source: Mathlib finite sums over natural intervals
Used in: stochastic mirror descent output-window telescoping and weighted sums
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem sum_times_eq_Icc
    {α : Type*} [AddCommMonoid α]
    (w : PositiveOutputWindow) (φ : {t : ℕ // 1 ≤ t} → α) :
    Finset.sum w.times φ =
      Finset.sum (Finset.Icc w.start w.stop) (fun n =>
        if hn : n ∈ Finset.Icc w.start w.stop then
          φ ⟨n, le_trans w.start_pos (Finset.mem_Icc.mp hn).1⟩
        else 0) := by
  simpa [times] using
    SOptLib.sum_positiveTimeOutputWindowTimes_eq_Icc
      w.start w.stop w.start_pos w.le_stop φ

/-- A positive weight sequence has positive total weight on a positive output window.

Layer: Model | Gap: Level 1 (positive output-window denominator)
Proof: the start index belongs to the closed window, so the finite sum contains a strictly positive term.
Source: Mathlib ordered finite sums over natural intervals
Used in: stochastic mirror descent weighted-output normalization
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem weight_sum_pos
    {M : Type*} [AddCommMonoid M] [Preorder M] [IsOrderedCancelAddMonoid M]
    [AddLeftStrictMono M]
    (γ : {t : ℕ // 1 ≤ t} → M)
    (hγ_pos : ∀ t, 0 < γ t)
    (w : PositiveOutputWindow) :
    0 < Finset.sum w.times γ := by
  simpa [times] using
    SOptLib.positiveTimeOutputWindow
      (γ := γ) hγ_pos (hstart := w.start_pos) (hle := w.le_stop)

end PositiveOutputWindow

/-- Finite normalized weighted output average over an abstract output window.

Packages the normalized weighted finite sum of iterates as a point of a convex
carrier, with the window normalizer supplied explicitly and proved equal to the
sum of weights.

Layer: Model | Concept: Iterates
Proof: (definitional construction; normalized finite convex combination of
  iterates packaged in the convex carrier)
Source: Mathlib convexity APIs for finite sums in real modules
Used in: stochastic mirror descent weighted average output over a positive-time
  iterate window
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def weightedOutputAverage
    {Ω T W E : Type*} [AddCommGroup E] [Module ℝ E]
    (X : Set E)
    (times : W → Finset T)
    (γ : T → ℝ)
    (x : T → Ω → E)
    (Wsum : W → ℝ)
    (hX_convex : Convex ℝ X)
    (hγ_nonneg : ∀ w t, t ∈ times w → 0 ≤ γ t)
    (hx_mem : ∀ w t, t ∈ times w → ∀ ω, x t ω ∈ X)
    (hW_pos : ∀ w, 0 < Wsum w)
    (hW_eq : ∀ w, Wsum w = Finset.sum (times w) γ)
    (w : W) : Ω → {y : E // y ∈ X} :=
  fun ω =>
    ⟨(Wsum w)⁻¹ • Finset.sum (times w) (fun t => γ t • x t ω), by
      classical
      let s := times w
      let Wtotal := Wsum w
      have hWpos : 0 < Wtotal := by
        simpa [Wtotal] using hW_pos w
      have hWne : Wtotal ≠ 0 := ne_of_gt hWpos
      have hweights_sum : Finset.sum s (fun t => Wtotal⁻¹ * γ t) = 1 := by
        calc
          Finset.sum s (fun t => Wtotal⁻¹ * γ t) =
              Wtotal⁻¹ * Finset.sum s (fun t => γ t) := by
            rw [Finset.mul_sum]
          _ = Wtotal⁻¹ * Wtotal := by
            simp [s, Wtotal, hW_eq w]
          _ = 1 := inv_mul_cancel₀ hWne
      have hweights_nonneg : ∀ t ∈ s, 0 ≤ Wtotal⁻¹ * γ t := by
        intro t ht
        exact mul_nonneg (inv_nonneg.mpr (le_of_lt hWpos))
          (hγ_nonneg w t (by simpa [s] using ht))
      have hpoints_mem : ∀ t ∈ s, x t ω ∈ X := by
        intro t ht
        exact hx_mem w t (by simpa [s] using ht) ω
      have hconv :
          Finset.sum s (fun t => (Wtotal⁻¹ * γ t) • x t ω) ∈ X :=
        hX_convex.sum_mem hweights_nonneg hweights_sum hpoints_mem
      convert hconv using 1
      simp [s, Wtotal, Finset.smul_sum, smul_smul]⟩

/-- The packaged weighted output average exposes the normalized ambient vector.

For a finite time window with nonnegative weights and positive total weight, the
first projection of `weightedOutputAverage` is exactly the inverse-total-weight
scaled weighted sum of the iterate values.

Layer: Model | Gap: Level 0 (weighted output average value projection)
Proof: by rfl after unfolding `weightedOutputAverage`.
Source: Mathlib finite sums, module scalar actions, and subtype projection APIs
Used in: stochastic mirror descent weighted output extraction from averaged iterates
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
@[simp]
theorem weightedOutputAverage_val
    {Ω T W E : Type*} [AddCommGroup E] [Module ℝ E]
    (X : Set E)
    (times : W → Finset T)
    (γ : T → ℝ)
    (x : T → Ω → E)
    (Wsum : W → ℝ)
    (hX_convex : Convex ℝ X)
    (hγ_nonneg : ∀ w t, t ∈ times w → 0 ≤ γ t)
    (hx_mem : ∀ w t, t ∈ times w → ∀ ω, x t ω ∈ X)
    (hW_pos : ∀ w, 0 < Wsum w)
    (hW_eq : ∀ w, Wsum w = Finset.sum (times w) γ)
    (w : W) (ω : Ω) :
    (weightedOutputAverage X times γ x Wsum hX_convex hγ_nonneg hx_mem hW_pos hW_eq w ω).1 =
      (Wsum w)⁻¹ • Finset.sum (times w) (fun t => γ t • x t ω) := by
  rfl

/-- Ambient-value formula for a finite normalized weighted output average.

The subtype value of `weightedOutputAverage` is the normalized weighted sum
`(Wsum w)⁻¹ • ∑ t in times w, γ t • x t ω`.

Layer: Model | Gap: Level 0 (weighted average output value formula)
Proof: direct forwarding to `weightedOutputAverage_val`, the projection lemma
  for the subtype-valued weighted average construction.
Source: Mathlib convex sets, modules over `ℝ`, and `Finset.sum` APIs
Used in: stochastic mirror descent normalized weighted output averaging
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem weightedAverageOutput_def
    {Ω T W E : Type*} [AddCommGroup E] [Module ℝ E]
    (X : Set E)
    (times : W → Finset T)
    (γ : T → ℝ)
    (x : T → Ω → E)
    (Wsum : W → ℝ)
    (hX_convex : Convex ℝ X)
    (hγ_nonneg : ∀ w t, t ∈ times w → 0 ≤ γ t)
    (hx_mem : ∀ w t, t ∈ times w → ∀ ω, x t ω ∈ X)
    (hW_pos : ∀ w, 0 < Wsum w)
    (hW_eq : ∀ w, Wsum w = Finset.sum (times w) γ)
    (w : W) (ω : Ω) :
    (weightedOutputAverage X times γ x Wsum hX_convex hγ_nonneg hx_mem hW_pos hW_eq w ω).1 =
      (Wsum w)⁻¹ • Finset.sum (times w) (fun t => γ t • x t ω) := by
  exact weightedOutputAverage_val X times γ x Wsum hX_convex hγ_nonneg hx_mem hW_pos hW_eq w ω

/-- A subtype-valued weighted output average remains in its carrier at every sample.

For a weighted output average represented as a point of the carrier subtype
`{z : E // z ∈ X}`, its projected value belongs to `X`.

Layer: Model | Gap: Level 0 (weighted output carrier membership)
Proof: read the subtype witness attached to `xbar ω`.
Source: Mathlib subtype and set membership projections
Used in: stochastic mirror descent weighted output average feasibility
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem weightedAverageOutput_mem
    {Ω E : Type*} {X : Set E}
    (xbar : Ω → {z : E // z ∈ X})
    (ω : Ω) :
    (xbar ω).1 ∈ X := by
  exact (xbar ω).2

/-- A finite normalized weighted output average of measurable iterates is measurable.

Layer: Model | Gap: Level 0 (measurable finite weighted output average)
Proof: lift measurability through the subtype constructor, then use measurability
  of constant scalar multiplication and `Finset.measurable_sum` for the finite
  weighted sum of measurable iterates.
Source: Mathlib measure theory measurable algebra APIs and Finset finite sums
Used in: stochastic mirror descent weighted output averaging as a measurable
  subtype-valued iterate summary
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem weightedAverageOutput_measurable
    {Ω T W E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [AddCommGroup E] [Module ℝ E] [MeasurableAdd₂ E] [MeasurableSMul₂ ℝ E]
    (X : Set E)
    (times : W → Finset T)
    (γ : T → ℝ)
    (x : T → Ω → E)
    (Wsum : W → ℝ)
    (hX_convex : Convex ℝ X)
    (hγ_nonneg : ∀ w t, t ∈ times w → 0 ≤ γ t)
    (hx_mem : ∀ w t, t ∈ times w → ∀ ω, x t ω ∈ X)
    (hW_pos : ∀ w, 0 < Wsum w)
    (hW_eq : ∀ w, Wsum w = Finset.sum (times w) γ)
    (hx_measurable : ∀ t, Measurable (x t))
    (w : W) :
    Measurable (weightedOutputAverage X times γ x Wsum hX_convex
      hγ_nonneg hx_mem hW_pos hW_eq w) := by
  classical
  refine Measurable.subtype_mk ?_
  refine measurable_const.smul ?_
  refine Finset.measurable_sum _ fun t _ht => ?_
  exact measurable_const.smul (hx_measurable t)

/-- Batch-size selector for 2-RSMD from the SFO budget and balancing constants.

`twoRsmdBatchSizeChoice σ L Dtilde Nbar` names the paper quantity
`ceil (min (max 1 (σ * sqrt (6 * Nbar) / (4 * L * Dtilde))) Nbar)`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; closed-form natural-number selector obtained
  by taking the ceiling of a clipped real-valued batch balance)
Source: Mathlib real square-root, lattice order, division, and natural ceiling
  APIs
Used in: randomized stochastic mirror descent constant mini-batch schedule
  balancing oracle variance against a per-run SFO budget
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
noncomputable def twoRsmdBatchSizeChoice
    (σ L Dtilde : ℝ) (Nbar : ℕ) : ℕ :=
  Nat.ceil (min (max 1 (σ * Real.sqrt (6 * (Nbar : ℝ)) /
    (4 * L * Dtilde))) (Nbar : ℝ))

/-- The clipped 2-RSMD batch-size selector never exceeds its SFO budget.

The selector takes the ceiling of a real-valued balance term clipped above by
`Nbar`; the natural ceiling is therefore bounded by the budget.

Layer: Model | Gap: Level 0 (clipped batch-size budget bound)
Proof: unfold the selector and apply `Nat.ceil_le`; the real-valued clipped
  argument is bounded above by the budget by `min_le_right`.
Source: Mathlib natural ceiling and lattice-order APIs for real clipping
Used in: randomized stochastic mirror descent constant mini-batch schedule
  proving the per-run iteration count is positive under an SFO budget
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
theorem twoRsmdBatchSizeChoice_le_budget
    (σ L Dtilde : ℝ) (Nbar : ℕ) :
    twoRsmdBatchSizeChoice σ L Dtilde Nbar ≤ Nbar := by
  unfold twoRsmdBatchSizeChoice
  apply Nat.ceil_le.mpr
  exact min_le_right _ _

/-- The clipped 2-RSMD batch-size selector is positive for a positive SFO budget.

The selector takes the natural ceiling of a real-valued balance term clipped
below by `1` and above by `Nbar`; when `Nbar` is positive, the clipped real
quantity is strictly positive.

Layer: Model | Gap: Level 0 (clipped batch-size positivity)
Proof: unfold the selector and use `Nat.ceil_pos`; positivity of the clipped
  argument follows from the lower clip by `max` and from the positive budget.
Source: Mathlib natural ceiling, real casts of naturals, and lattice-order APIs
  for clipped real values
Used in: randomized stochastic mirror descent constant mini-batch schedule
  proving the mini-batch count is nonzero before defining per-run iterations
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
theorem twoRsmdBatchSizeChoice_pos
    (σ L Dtilde : ℝ) {Nbar : ℕ} (hNbar_pos : 0 < Nbar) :
    0 < twoRsmdBatchSizeChoice σ L Dtilde Nbar := by
  unfold twoRsmdBatchSizeChoice
  apply Nat.ceil_pos.mpr
  apply lt_min
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  · exact Nat.cast_pos.mpr hNbar_pos

/-- A natural-valued mini-batch schedule that is constant across iteration time.

`constantBatchSchedule m0` exposes a fixed natural mini-batch size as a schedule
indexed by the optimization counter, matching paper algorithms whose batch
choice is made once from a budget and then reused at every inner step.

Layer: Model | Concept: Iterates
Proof: (definitional construction; constant natural-number function over the
  iteration index)
Source: Mathlib natural-number functions and Lan stochastic mirror descent
  mini-batch scheduling notation
Used in: randomized stochastic mirror descent optimization phase with a constant
  mini-batch schedule across inner iterations
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
noncomputable def constantBatchSchedule (m0 : ℕ) (_k : ℕ) : ℕ :=
  m0

/-- A constant natural-valued mini-batch schedule returns its selected batch size at every index.

For any natural batch size `m0`, the schedule `constantBatchSchedule m0` is
definitionally the constant function on optimization time.

Layer: Model | Gap: Level 0 (constant mini-batch schedule unfolding)
Proof: by rfl after unfolding `constantBatchSchedule`; the schedule is a
  constant function of the iteration index.
Source: Mathlib natural-number functions and definitional equality APIs
Used in: randomized stochastic mirror descent optimization phase with a constant
  mini-batch schedule across inner iterations
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
@[simp]
theorem constantBatchSchedule_eq (m0 : ℕ) (k : ℕ) :
    constantBatchSchedule m0 k = m0 := by
  rfl

/-- A constant natural-valued mini-batch schedule is positive at every index if
its selected batch size is positive.

Layer: Model | Gap: Level 0 (constant mini-batch schedule positivity)
Proof: by rfl after unfolding `constantBatchSchedule`; positivity is transported
  from the fixed natural batch size to every iteration index.
Source: Mathlib natural-number order and definitional equality APIs
Used in: randomized stochastic mirror descent optimization phase proving each
  mini-batch count is nonzero before forming empirical oracle averages
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
theorem constantBatchSchedule_pos
    (m0 : ℕ) (k : ℕ) (hm0_pos : 0 < m0) :
    0 < constantBatchSchedule m0 k := by
  simpa [constantBatchSchedule] using hm0_pos

/-- The iteration count obtained by dividing a natural SFO budget by the first batch size.

For algorithms with a fixed per-run oracle-call budget and a natural-valued
mini-batch schedule, this names the paper convention `N = ⌊Nbar / m₁⌋` using
Lean's natural-number division.

Layer: Model | Concept: Iterates
Proof: (definitional construction; natural-number quotient of a budget by the batch size at the first positive iteration)
Source: Mathlib natural-number division and Lan stochastic mirror descent budget scheduling notation
Used in: randomized stochastic mirror descent per-run optimization-phase iteration count from total SFO budget and mini-batch size
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/initialization
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, randomized stochastic mirror descent -/
noncomputable def iterationCountFromBudgetAndBatch
    (Nbar : ℕ) (m : ℕ → ℕ) : ℕ :=
  Nbar / m 1

/-- The staged iteration-count wrapper unfolds to natural division by the first batch size.

For a natural oracle-call budget `Nbar` and a natural-valued mini-batch schedule
`m`, the per-run iteration count named by the model layer is exactly
`Nbar / m 1`, Lean's natural-number quotient.

Layer: Model | Gap: Level 0 (iteration-count quotient unfolding)
Proof: by rfl after unfolding `iterationCountFromBudgetAndBatch`.
Source: Mathlib natural-number division and Lan stochastic mirror descent budget scheduling notation
Used in: randomized stochastic mirror descent optimization-phase iteration count from total SFO budget and first mini-batch size
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/initialization
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, randomized stochastic mirror descent -/
theorem iterationCountFromBudgetAndBatch_eq
    (Nbar : ℕ) (m : ℕ → ℕ) :
    iterationCountFromBudgetAndBatch Nbar m = Nbar / m 1 := by
  rfl

/-- The budget-derived iteration count is positive when the first batch size is positive and fits the budget.

For a natural oracle-call budget `Nbar` and a natural-valued mini-batch schedule
`m`, the model iteration count `Nbar / m 1` is positive as soon as the first
batch size is nonzero and no larger than the available budget.

Layer: Model | Gap: Level 0 (positive iteration count from budget and batch bound)
Proof: unfold the model iteration-count wrapper and apply Mathlib's
  natural-division positivity criterion `Nat.div_pos`.
Source: Mathlib natural-number division and ordered semiring arithmetic
Used in: randomized stochastic mirror descent optimization-phase nonempty iteration window
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/initialization
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, randomized stochastic mirror descent -/
theorem iterationCountFromBudgetAndBatch_pos
    (Nbar : ℕ) (m : ℕ → ℕ)
    (hm_pos : 0 < m 1) (hm_le : m 1 ≤ Nbar) :
    0 < iterationCountFromBudgetAndBatch Nbar m := by
  simpa [iterationCountFromBudgetAndBatch] using Nat.div_pos hm_le hm_pos

/-- Positive-time paper view of a zero-based stochastic iterate process.

For a process where zero-based counter `n` stores the paper iterate at time
`n + 1`, `positiveTimeIterateView process k` exposes the paper iterate `x_k`
for a positive natural-number time `k`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; positive-time subtype view of a zero-based
  stochastic iterate process)
Source: Mathlib natural-number subtraction, subtype indexing, and Pi-function
  evaluation APIs for iterate processes
Used in: nonconvex stochastic mirror descent positive-time iterate notation
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def positiveTimeIterateView
    {Ω P : Type*}
    (process : ℕ → Ω → P) (k : {k : ℕ // 1 ≤ k}) (ω : Ω) : P :=
  process (k.1 - 1) ω

/-- The positive-time iterate view evaluates the zero-based process at `k - 1`.

Layer: Model | Gap: Level 0 (positive-time iterate view unfolding)
Proof: by rfl after unfolding `positiveTimeIterateView`.
Source: Mathlib natural-number subtraction, subtype indexing, and Pi-function
  evaluation APIs for iterate processes
Used in: nonconvex stochastic mirror descent positive-time iterate notation
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
@[simp]
theorem positiveTimeIterateView_eq
    {Ω P : Type*}
    (process : ℕ → Ω → P) (k : {k : ℕ // 1 ≤ k}) (ω : Ω) :
    positiveTimeIterateView process k ω = process (k.1 - 1) ω := by
  rfl

/-- Canonical zero-based recursive stochastic iterate process.

Layer: Model | Concept: Iterates
Proof: (definitional construction; primitive recursion over natural time)
Source: Mathlib natural-number primitive recursion and Pi-function APIs
Used in: nonconvex stochastic mirror descent recursive prox-step iterate update
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def recursiveIterateProcess
    {Ω P : Type*} (initial : P) (step : ℕ → P → Ω → P) :
    ℕ → Ω → P
  | 0 => fun _ => initial
  | k + 1 => fun ω => step k (recursiveIterateProcess initial step k ω) ω

/-- A recursively generated stochastic iterate process has the expected initial value.

Layer: Model | Gap: Level 0 (recursive iterate initial value)
Proof: by rfl after unfolding `recursiveIterateProcess`.
Source: Mathlib natural-number primitive recursion and Pi-function APIs
Used in: nonconvex stochastic mirror descent recursive prox-step iterate update
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem recursiveIterateProcess_zero
    {Ω P : Type*}
    (process : ℕ → Ω → P)
    (initial : P)
    (step : ℕ → P → Ω → P)
    (h_process : process = recursiveIterateProcess initial step)
    (ω : Ω) :
    process 0 ω = initial := by
  subst h_process
  rfl

/-- A recursively generated stochastic iterate process unfolds at successor time.

Layer: Model | Gap: Level 0 (recursive iterate successor unfolding)
Proof: by rfl after unfolding `recursiveIterateProcess`.
Source: Mathlib natural-number primitive recursion and Pi-function APIs
Used in: nonconvex stochastic mirror descent recursive prox-step iterate update
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem recursiveIterateProcess_succ
    {Ω P : Type*}
    (process : ℕ → Ω → P)
    (initial : P)
    (step : ℕ → P → Ω → P)
    (h_process : process = recursiveIterateProcess initial step)
    (k : ℕ) (ω : Ω) :
    process (k + 1) ω = step k (process k ω) ω := by
  subst h_process
  rfl

/-- A recursively generated stochastic iterate process has the expected successor function.

If `process` is definitionally the canonical recursive iterate process with
initial state `initial` and transition `step`, then its successor time slice is
the function that applies `step` pointwise to the previous time slice.

Layer: Model | Gap: Level 1 (recursive iterate function bridge)
Proof: apply the pointwise successor theorem for `recursiveIterateProcess` and
  use function extensionality to upgrade it to equality of stochastic processes.
Source: Mathlib natural-number primitive recursion and Pi-function extensionality APIs
Used in: nonconvex stochastic mirror descent recursive prox-step iterate update
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem iterateProcess_bridge_of_recursiveProcess
    {Ω P : Type*}
    (process : ℕ → Ω → P)
    (initial : P)
    (step : ℕ → P → Ω → P)
    (h_process : process = SOptLib.recursiveIterateProcess initial step)
    (k : ℕ) :
    process (k + 1) = fun ω => step k (process k ω) ω := by
  funext ω
  exact recursiveIterateProcess_succ process initial step h_process k ω

/-- A paper iterate inherits strict-past measurability from its raw process slice.

If each raw process slice selected by `time k` is measurable with respect to the
strict-past sigma-algebra `past k`, and the public iterate view is that slice,
then the public iterate is measurable with respect to the same past.

Layer: Model | Gap: Level 1 (iterate view strict-past measurability bridge)
Proof: rewrite the public iterate view to the corresponding raw process slice
  and apply the supplied process measurability hypothesis.
Source: Mathlib measure-theory measurable function rewriting APIs
Used in: nonconvex stochastic mirror descent strict-past iterate measurability
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic mirror descent -/
theorem iterate_measurable_of_process_measurable_strictPast
    {Ω K X : Type*} [MeasurableSpace X]
    (iterate : K → Ω → X)
    (process : ℕ → Ω → X)
    (past : K → MeasurableSpace Ω)
    (time : K → ℕ)
    (h_process : ∀ k, Measurable[past k] (process (time k)))
    (h_iterate : ∀ k, iterate k = process (time k))
    (k : K) :
    Measurable[past k] (iterate k) := by
  simpa [h_iterate k] using h_process k

/-- Every value of a function on a finite index type is bounded by the maximum
of its finite image.

For a finite family `f : ι → α` in a linear order, any indexed value `f i`
belongs to `Finset.univ.image f`, hence it is at most the `max'` of that
nonempty image.

Layer: Model | Gap: Level 0 (finite image maximum upper bound)
Proof: membership of `f i` in `Finset.univ.image f` reduces to `simp`, and
  `Finset.le_max'` supplies the order bound for nonempty finite sets.
Source: Mathlib finite-set maximum API for linearly ordered finsets
Used in: nonconvex stochastic mirror descent validation-error maximum over
  finitely many independent runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem le_finite_image_max
    {ι α : Type*} [Fintype ι] [LinearOrder α]
    (f : ι → α) (i : ι)
    (h : (Finset.univ.image f).Nonempty) :
    f i ≤ (Finset.univ.image f).max' h := by
  classical
  have hmem : f i ∈ Finset.univ.image f := by
    simp
  simpa using
    Finset.le_max' (Finset.univ.image f) (f i) hmem

/-- A constant paper mini-batch size is the selected batch size at the SFO budget.

Given an abstract natural-valued batch-size selector and a natural budget `Nbar`,
this definition names the constant schedule value used by paper algorithms whose
inner mini-batch size does not vary with the iteration counter.

Layer: Model | Concept: Iterates
Proof: (definitional construction; natural-number batch-size selector evaluated
  at the paper SFO budget)
Source: Mathlib natural-number function application and Lan stochastic mirror
  descent mini-batch scheduling notation
Used in: randomized stochastic mirror descent constant mini-batch schedule for
  the optimization phase
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
noncomputable def constantPaperBatchSize
    (batchSizeChoice : ℕ → ℕ) (Nbar : ℕ) : ℕ :=
  batchSizeChoice Nbar

/-- Canonical model-level value for the maximum of a nonempty finite set of real run values.

This wrapper names the finite maximum used when paper notation writes a run-wise
maximum over finitely many realized real quantities.

Layer: Model | Concept: Iterates
Proof: (definitional construction; nonempty finite real-set maximum via `Finset.max'`)
Source: Mathlib finite-set maximum API for linearly ordered finsets
Used in: nonconvex stochastic mirror descent validation-error maximum over
  independent runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def finiteRunMaxValue
    (values : Finset ℝ) (hvalues : values.Nonempty) : ℝ :=
  values.max' hvalues

/-- The maximum of a nonempty finite image is attained by some index.

For a finite family `f : ι → α` in a linear order, the `max'` of
`Finset.univ.image f` is a member of that image, so it is equal to `f i` for
some index `i`.

Layer: Model | Gap: Level 0 (finite image maximum attainment)
Proof: `Finset.max'_mem` places the maximum in the finite image, and
  `Finset.mem_image` recovers an index whose value is that maximum.
Source: Mathlib finite-set maximum API for linearly ordered finsets
Used in: nonconvex stochastic mirror descent validation-error maximum over
  finitely many independent runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem finite_image_max_attained
    {ι α : Type*} [Fintype ι] [LinearOrder α]
    (f : ι → α) (h : (Finset.univ.image f).Nonempty) :
    ∃ i : ι, (Finset.univ.image f).max' h = f i := by
  classical
  have hmem :
      (Finset.univ.image f).max' h ∈ Finset.univ.image f :=
    Finset.max'_mem (Finset.univ.image f) h
  rcases Finset.mem_image.mp hmem with ⟨i, _hi, hi⟩
  exact ⟨i, hi.symm⟩

/-- The canonical finite-run maximum wrapper unfolds to `Finset.max'`.

This spec theorem exposes the Mathlib finite-set maximum used by the
paper-facing `finiteRunMaxValue` notation for nonempty finite real value sets.

Layer: Model | Gap: Level 0 (finite-run maximum selector unfolding)
Proof: by rfl after unfolding `finiteRunMaxValue`; the wrapper is definitionally `Finset.max'`.
Source: Mathlib finite-set maximum API for linearly ordered finsets
Used in: nonconvex stochastic mirror descent validation-error maximum over independent runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic mirror descent -/
theorem finiteRunMaxValue_eq_finset_max
    (values : Finset ℝ) (hvalues : values.Nonempty) :
    finiteRunMaxValue values hvalues = values.max' hvalues := by
  rfl

/-- The minimum of a nonempty finite real value set is below every member.

This packages the order fact used when a paper proof writes a minimum over a
finite collection of run-wise real values and then compares it to one chosen run.

Layer: Model | Gap: Level 0 (finite run minimum lower bound)
Proof: the selected value supplies membership in the nonempty finset, and
  Mathlib's `Finset.min'_le` gives the lower bound for the finite minimum.
Source: Mathlib finite-set minimum API for linearly ordered finsets
Used in: nonconvex stochastic mirror descent exact projected-gradient
  stationarity minimum over independent runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem finiteRunMinValue
    (values : Finset ℝ) (hvalues : values.Nonempty)
    {value : ℝ} (hvalue : value ∈ values) :
    values.min' hvalues ≤ value := by
  simpa using Finset.min'_le values value hvalue

/-- The minimum of a nonempty finite image is attained by some index.

For a finite family `value : ι → α` in a linear order, the `min'` of
`Finset.univ.image value` is a member of that image, so it is equal to
`value i` for some index `i`.

Layer: Model | Gap: Level 0 (finite image minimum attainment)
Proof: `Finset.min'_mem` places the minimum in the finite image, and
  `Finset.mem_image` recovers an index whose value is that minimum.
Source: Mathlib finite-set minimum API for linearly ordered finsets
Used in: nonconvex stochastic mirror descent exact projected-gradient
  stationarity minimum over finitely many independent runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem finiteRunMinValue_attained
    {ι α : Type*} [Fintype ι] [LinearOrder α]
    (value : ι → α) (h : (Finset.univ.image value).Nonempty) :
    ∃ i : ι, (Finset.univ.image value).min' h = value i := by
  classical
  have hmem :
      (Finset.univ.image value).min' h ∈ Finset.univ.image value :=
    Finset.min'_mem (Finset.univ.image value) h
  rcases Finset.mem_image.mp hmem with ⟨i, _hi, hi⟩
  exact ⟨i, hi.symm⟩

/-- Canonical model-level value for the minimum of a nonempty finite set of real run values.

This wrapper names the finite minimum used when paper notation writes a run-wise
minimum over finitely many realized real quantities.

Layer: Model | Concept: Iterates
Proof: (definitional construction; nonempty finite real-set minimum via `Finset.min'`)
Source: Mathlib finite-set minimum API for linearly ordered finsets
Used in: nonconvex stochastic mirror descent exact projected-gradient
  stationarity minimum over independent runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def finiteRunMinValueOfFinset
    (values : Finset ℝ) (hvalues : values.Nonempty) : ℝ :=
  values.min' hvalues

/-- The finite-run minimum wrapper unfolds to `Finset.min'` on its nonempty value set.

For a nonempty finite set of real run values, the model-layer finite-run minimum
is exactly Mathlib's selected minimum for that finite set.

Layer: Model | Gap: Level 0 (finite run minimum unfolding)
Proof: by rfl after unfolding `finiteRunMinValueOfFinset`.
Source: Mathlib finite-set minimum API for linearly ordered finsets
Used in: nonconvex stochastic mirror descent exact projected-gradient
  stationarity minimum over independent runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem finiteRunMinValue_eq_finset_min
    (values : Finset ℝ) (hvalues : values.Nonempty) :
    finiteRunMinValueOfFinset values hvalues = values.min' hvalues := by
  rfl

/-- The minimum of a finite indexed family is bounded above by each indexed value.

For a nonempty finite index type, Mathlib's `min'` on the universal image
represents the paper minimum over runs, and every concrete run value belongs to
that image.

Layer: Model | Gap: Level 0 (finite indexed minimum lower bound)
Proof: the selected index contributes membership in `Finset.univ.image value`;
  `Finset.min'_le` then gives the comparison with the chosen indexed value.
Source: Mathlib finite-set image and minimum APIs for linearly ordered finsets
Used in: nonconvex stochastic mirror descent exact projected-gradient
  stationarity minimum over independent runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem finiteRunMinValue_le
    {ι α : Type*} [Fintype ι] [LinearOrder α]
    (value : ι → α) (i : ι) :
    (Finset.univ.image value).min'
        (by
          classical
          exact ⟨value i, by simp⟩) ≤
      value i := by
  classical
  exact Finset.min'_le (Finset.univ.image value) (value i) (by simp)

/-- Total output denominator over a finite family of weighted indices.

For an abstract finite set of output times and a real or additive weight
function, this names the finite sum used to normalize a randomized output
distribution.

Layer: Model | Concept: Iterates
Proof: (definitional construction; finite output-weight denominator as a
  big-operator sum)
Source: Mathlib finite sets and big-operator sums over commutative additive
  monoids
Used in: nonconvex stochastic mirror descent randomized stopping distribution
  denominator
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
@[simp] def outputWeightDenominator
    {T R : Type*} [AddCommMonoid R]
    (times : Finset T) (weight : T → R) : R :=
  Finset.sum times weight

/-- A finite output-weight denominator is positive when all selected weights are positive.

For any finite set of output indices, strict positivity of every weight on the
selected support and nonemptiness of that support imply strict positivity of the
normalizing denominator `outputWeightDenominator`.

Layer: Model | Gap: Level 0 (positive finite output-weight denominator)
Proof: unfold the denominator to a finite sum and apply `Finset.sum_pos` using
  the supplied pointwise positivity and nonempty support.
Source: Mathlib finite sums over ordered real additive monoids
Used in: nonconvex stochastic mirror descent randomized stopping distribution
  denominator positivity
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem outputWeightDenominator_pos
    {T : Type*} (times : Finset T) (weight : T → ℝ)
    (hweight_pos : ∀ t ∈ times, 0 < weight t)
    (htimes_nonempty : times.Nonempty) :
    0 < Finset.sum times weight := by
  exact Finset.sum_pos hweight_pos htimes_nonempty

/-- Pointwise mass obtained by normalizing a real-valued output weight by a denominator.

For an abstract output index type, this names the mass assignment
`k ↦ weight k / denom` used after summing a finite family of stopping weights.

Layer: Model | Concept: Iterates
Proof: (definitional construction; pointwise quotient of an output weight by
  its normalizing denominator)
Source: Mathlib real division and function application APIs
Used in: nonconvex stochastic mirror descent randomized stopping distribution
  masses
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def normalizedOutputMass
    {T : Type*} (weight : T → ℝ) (denom : ℝ) (k : T) : ℝ :=
  weight k / denom

/-- Normalizing an output weight by the finite output-weight denominator is the paper mass formula.

For an arbitrary finite family of output indices, the named pointwise mass
`normalizedOutputMass` unfolds to the weight at `k` divided by the finite sum
of all output weights.

Layer: Model | Gap: Level 0 (normalized output mass definitional bridge)
Proof: by rfl after unfolding `normalizedOutputMass`.
Source: Mathlib finite sums and real division APIs
Used in: nonconvex stochastic mirror descent randomized stopping distribution
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem normalizedOutputMass_def
    {T : Type*} (weight : T → ℝ) (times : Finset T) (k : T) :
    normalizedOutputMass weight (Finset.sum times weight) k =
      weight k / Finset.sum times weight := by
  rfl

/-- A normalized output mass is nonnegative when its window weight and denominator are nonnegative.

For an abstract finite output window, the pointwise normalized mass
`weight k / denom` is nonnegative at every window index whose weight is
nonnegative, provided the normalizing denominator is also nonnegative.

Layer: Model | Gap: Level 0 (normalized output mass nonnegativity)
Proof: unfold `normalizedOutputMass` and apply nonnegativity of division from
  the pointwise weight bound and denominator bound.
Source: Mathlib ordered real division APIs
Used in: nonconvex stochastic mirror descent randomized stopping mass
  construction over the positive output window
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem normalizedOutputMass_nonneg
    {T : Type*}
    (times : Finset T)
    (weight : T → ℝ)
    (denom : ℝ)
    (k : T)
    (hk : k ∈ times)
    (hweight_nonneg : ∀ j, j ∈ times → 0 ≤ weight j)
    (hdenom_nonneg : 0 ≤ denom) :
    0 ≤ normalizedOutputMass weight denom k := by
  simpa [normalizedOutputMass] using
    div_nonneg (hweight_nonneg k hk) hdenom_nonneg

/-- The normalized output masses over a finite window sum to one.

For any finite output window, if the denominator is the sum of the raw
weights over that window and is nonzero, then the pointwise mass
`weight k / denom` is normalized.

Layer: Model | Gap: Level 0 (finite normalized output mass total)
Proof: unfold `normalizedOutputMass`, factor the common denominator out of the
  finite sum using `Finset.sum_div`, and cancel the nonzero denominator.
Source: Mathlib finite sums and ordered-field division APIs
Used in: nonconvex stochastic mirror descent randomized stopping distribution
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem normalizedOutputMass_sum_one
    {T : Type*}
    (times : Finset T)
    (weight : T → ℝ)
    (denom : ℝ)
    (hdenom : denom = Finset.sum times weight)
    (hdenom_ne : denom ≠ 0) :
    Finset.sum times (normalizedOutputMass weight denom) = 1 := by
  calc
    Finset.sum times (normalizedOutputMass weight denom)
        = Finset.sum times (fun k => weight k / denom) := by
          rfl
    _ = Finset.sum times weight / denom := by
          rw [← Finset.sum_div]
    _ = denom / denom := by
          rw [← hdenom]
    _ = 1 := div_self hdenom_ne

/-- A constant half-Lipschitz stepsize gives the standard output weight.

For any index type, if the stepsize sequence is constantly `1 / (2 * L)`,
then the quadratic stopping weight `γ k - L * γ k ^ 2` is the constant
`1 / (4 * L)`.

Layer: Model | Gap: Level 0 (constant stepsize output-weight normalization)
Proof: rewrite the stepsize by the constant-step hypothesis, clear the
  nonzero denominator, and close the polynomial identity by ring normalization.
Source: Mathlib real field simplification and commutative semiring
  normalization APIs
Used in: nonconvex stochastic mirror descent randomized stopping weight
  simplification under the constant half-Lipschitz stepsize
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem constantStep_outputWeight_eq
    {T : Type*} (L : ℝ) (γ : T → ℝ)
    (hL_ne : L ≠ 0) (hγ : ∀ k, γ k = 1 / (2 * L)) (k : T) :
    γ k - L * γ k ^ 2 = 1 / (4 * L) := by
  rw [hγ k]
  field_simp [hL_ne]
  ring

/-- A positive constant half-Lipschitz stepsize gives a positive output weight.

For any index type, if `L` is positive and the stepsize sequence is constantly
`1 / (2 * L)`, then the quadratic randomized-stopping weight
`γ k - L * γ k ^ 2` is strictly positive at every index.

Layer: Model | Gap: Level 0 (constant stepsize output-weight positivity)
Proof: first normalize the quadratic output weight using the constant-step
  identity, then prove positivity of `1 / (4 * L)` from positivity of `L`.
Source: Mathlib ordered real field and finite-dimensional optimization
  stepsize algebra APIs
Used in: nonconvex stochastic mirror descent randomized stopping mass
  positivity under the constant half-Lipschitz stepsize
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem constantStep_outputWeight_pos
    {T : Type*} (L : ℝ) (γ : T → ℝ)
    (hL_pos : 0 < L) (hγ : ∀ k, γ k = 1 / (2 * L)) (k : T) :
    0 < γ k - L * γ k ^ 2 := by
  rw [constantStep_outputWeight_eq L γ (ne_of_gt hL_pos) hγ k]
  exact one_div_pos.mpr (mul_pos (by norm_num : (0 : ℝ) < 4) hL_pos)

/-- A recursive process prefix is measurable with respect to a fixed sample-block sigma-algebra.

For a process whose initial slice is measurable, whose time-`n` driver is
measurable whenever the previous slice is measurable, and whose update map is
measurable on state-driver pairs, every process slice up to the finite prefix
bound is measurable with respect to the same source sigma-algebra.

Layer: Model | Gap: Level 1 (sample-block recursive process prefix measurability)
Proof: induction on the natural-number process time; the successor case builds
  the measurable state-driver product and composes it with the measurable update.
Source: Mathlib MeasureTheory product measurable-space and measurable composition APIs
Used in: nonconvex stochastic mirror descent optimization-block measurability
  of the process prefix before randomized output selection
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem process_prefix_measurable_wrt_sampleBlock
    {Ω P D : Type*} [MeasurableSpace Ω] [MeasurableSpace P] [MeasurableSpace D]
    (mΩ : MeasurableSpace Ω)
    (process : ℕ → Ω → P)
    (oracle : ℕ → (Ω → P) → Ω → D)
    (update : ℕ → P → D → P)
    (R : ℕ)
    (h_init : Measurable[mΩ] (process 0))
    (h_oracle : ∀ n, n + 1 ≤ R →
      ∀ x : Ω → P, Measurable[mΩ] x → Measurable[mΩ] (fun ω => oracle n x ω))
    (h_update : ∀ n, n + 1 ≤ R →
      Measurable (fun p : P × D => update n p.1 p.2))
    (h_succ : ∀ n, n + 1 ≤ R →
      process (n + 1) = fun ω => update n (process n ω) (oracle n (process n) ω)) :
    ∀ n : ℕ, n ≤ R → Measurable[mΩ] (process n) := by
  intro n hn
  induction n with
  | zero =>
      simpa using h_init
  | succ n ih =>
      have hn' : n ≤ R := Nat.le_of_succ_le hn
      have hproc : Measurable[mΩ] (process n) := ih hn'
      have hg : Measurable[mΩ] (fun ω => oracle n (process n) ω) :=
        h_oracle n hn (process n) hproc
      have hnext :
          Measurable[mΩ] (fun ω => update n (process n ω) (oracle n (process n) ω)) :=
        (h_update n hn).comp (hproc.prodMk hg)
      simpa [h_succ n hn] using hnext

/-- A recursively defined stochastic process is measurable up to a strict-past cutoff.

If the initial state is measurable, each driver at time `n` is measurable once
the previous process state is measurable, and the recursive step map is
measurable on state-driver pairs, then every process state up to `N` is
measurable with respect to the selected past sigma-algebra.

Layer: Model | Gap: Level 1 (recursive process measurability over a fixed past filtration)
Proof: induction on the recursion counter; the successor step composes the
  measurable state-driver pair with the measurable update map and rewrites by
  the recursive update equation.
Source: Mathlib measure-theory measurable function composition and product APIs
Used in: nonconvex stochastic mirror descent strict-past iterate measurability
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic mirror descent -/
theorem recursiveProcess_measurable_wrt_strictPast
    {Ω K X U : Type*} [MeasurableSpace X] [MeasurableSpace U]
    (past : K → MeasurableSpace Ω)
    (process : ℕ → Ω → X)
    (driver : ℕ → Ω → U)
    (step : ℕ → X → U → X)
    (k : K) (N : ℕ)
    (h_init : Measurable[past k] (process 0))
    (h_driver : ∀ n, n + 1 ≤ N →
      Measurable[past k] (process n) → Measurable[past k] (driver n))
    (h_step : ∀ n, n + 1 ≤ N →
      Measurable (fun p : X × U => step n p.1 p.2))
    (h_update : ∀ n, n + 1 ≤ N →
      process (n + 1) = fun ω => step n (process n ω) (driver n ω)) :
    ∀ n, n ≤ N → Measurable[past k] (process n) := by
  intro n hn
  induction n with
  | zero =>
      simpa using h_init
  | succ n ih =>
      have hn' : n ≤ N := Nat.le_of_succ_le hn
      have hproc : Measurable[past k] (process n) := ih hn'
      have hdrv : Measurable[past k] (driver n) := h_driver n hn hproc
      have hnext :
          Measurable[past k] (fun ω => step n (process n ω) (driver n ω)) :=
        (h_step n hn).comp (hproc.prodMk hdrv)
      simpa [h_update n hn] using hnext

/-- Select the realized output of one run by evaluating an iterate process at a
sampled stopping time.

`randomizedRunOutput iterate s R ω` is the abstract model object behind paper
notation of the form `x_{R_s}`: choose run `s`, choose stopping time `R`, and
evaluate the stochastic iterate at sample point `ω`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; run-index and stopping-time projection of a
  stochastic iterate process)
Source: Mathlib Pi-function evaluation and subtype-indexed iterate notation
Used in: nonconvex stochastic mirror descent randomized one-run output
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def randomizedRunOutput
    {Ω ι τ P : Type*}
    (iterate : ι → τ → Ω → P) (s : ι) (R : τ) (ω : Ω) : P :=
  iterate s R ω

/-- The randomized run output is definitionally the iterate at the selected run
and stopping time.

Layer: Model | Gap: Level 0 (randomized run-output unfolding)
Proof: by rfl after unfolding `randomizedRunOutput`.
Source: Mathlib Pi-function evaluation and definitional equality APIs
Used in: nonconvex stochastic mirror descent randomized one-run output
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
@[simp]
theorem randomizedRunOutput_eq_iterate
    {Ω ι τ P : Type*}
    (iterate : ι → τ → Ω → P) (s : ι) (R : τ) (ω : Ω) :
    randomizedRunOutput iterate s R ω = iterate s R ω := by
  rfl

/-- A randomized output view is measurable when it is a selected measurable process slice.

If every raw process slice is measurable and the randomized-output view at
time `t` is definitionally the slice selected by `time t`, measurability
transfers directly to the output.

Layer: Model | Gap: Level 1 (randomized-output process-slice measurability bridge)
Proof: rewrite the randomized-output view to the corresponding raw process
  slice and apply the supplied process measurability hypothesis.
Source: Mathlib measure-theory measurable function rewriting APIs
Used in: nonconvex stochastic mirror descent randomized iterate output
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic mirror descent -/
theorem randomizedOutput_measurable_of_process_measurable
    {Ω P T : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
    (process : ℕ → Ω → P)
    (time : T → ℕ)
    (output : T → Ω → P)
    (h_process : ∀ n : ℕ, Measurable (process n))
    (h_output : ∀ t : T, output t = process (time t))
    (t : T) :
    Measurable (output t) := by
  simpa [h_output t] using h_process (time t)

/-- A fixed randomized-output view is measurable with respect to a sample-block sigma-algebra.

If the output at `t` is the process slice selected by `time t`, and that
selected process slice is measurable with respect to the sample-block
measurable space `mΩ`, then the output has the same measurability.

Layer: Model | Gap: Level 1 (sample-block randomized-output measurability bridge)
Proof: rewrite the output view to the selected process slice and apply the
  supplied sample-block measurability hypothesis.
Source: Mathlib measure-theory measurable function rewriting APIs
Used in: nonconvex stochastic mirror descent randomized output measurability
  from its finite optimization sample footprint
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem randomizedOutput_measurable_wrt_sampleBlock
    {Ω P T : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
    (mΩ : MeasurableSpace Ω)
    (process : ℕ → Ω → P)
    (output : T → Ω → P)
    (time : T → ℕ)
    (t : T)
    (h_process : ∀ n : ℕ, n ≤ time t → @Measurable Ω P mΩ inferInstance (process n))
    (h_output : ∀ t : T, output t = process (time t)) :
    @Measurable Ω P mΩ inferInstance (output t) := by
  simpa [h_output t] using h_process (time t) le_rfl

end SOptLib

namespace SOptLib

/-- Feasible state for an accelerated two-sequence recursion.

The state stores the current prox/update iterate `x`, the averaged output
iterate `xBar`, and feasibility witnesses for both coordinates in the same
carrier set `X`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; bundled accelerated prox and averaged
  iterate coordinates with carrier-membership invariants)
Source: accelerated stochastic approximation state notation and Mathlib Set
  membership APIs
Used in: stochastic accelerated gradient descent recursion state for prox
  updates and output averaging over a shared feasible carrier
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/initialization
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
structure FeasibleAcceleratedState {E : Type*} (X : Set E) where
  x : E
  xBar : E
  hx : x ∈ X
  hxBar : xBar ∈ X

/-- The feasible accelerated two-coordinate state carries the sigma-algebra
generated by its ambient prox and averaged-output coordinates.

The membership certificates in `FeasibleAcceleratedState` are proof fields, so
they should not refine the stochastic state sigma-algebra. This construction makes
state measurability coincide with measurability of `(x, xBar)`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; comap of the product coordinate reader
  `s ↦ (s.x, s.xBar)`)
Source: Mathlib measure-theory measurable-space comap and product
  measurable-space APIs
Used in: stochastic accelerated gradient descent generated state recursion
  before sample-kernel step measurability
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/initialization
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
@[reducible]
def feasibleAcceleratedStateMeasurableSpace
    {E : Type*} [MeasurableSpace E] (X : Set E) :
    MeasurableSpace (FeasibleAcceleratedState X) :=
  MeasurableSpace.comap
    (fun s : FeasibleAcceleratedState X => (s.x, s.xBar)) inferInstance

/-- The feasible accelerated state sigma-algebra unfolds to the comap of the
ambient coordinate pair.

Layer: Model | Gap: Level 0 (accelerated feasible-state measurable-space unfolding)
Proof: by rfl after unfolding `feasibleAcceleratedStateMeasurableSpace`.
Source: Mathlib measure-theory measurable-space comap and product
  measurable-space APIs
Used in: stochastic accelerated gradient descent coordinate-comap
  measurability reductions for generated state transitions
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/initialization
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
@[simp]
theorem feasibleAcceleratedStateMeasurableSpace_eq
    {E : Type*} [MeasurableSpace E] (X : Set E) :
    (feasibleAcceleratedStateMeasurableSpace X :
        MeasurableSpace (FeasibleAcceleratedState X)) =
      MeasurableSpace.comap
        (fun s : FeasibleAcceleratedState X => (s.x, s.xBar)) inferInstance := by
  rfl

/-- The accelerated feasible-state coordinate reader is measurable for the
coordinate-generated state sigma-algebra.

Layer: Model | Gap: Level 0 (accelerated feasible-state coordinate measurability)
Proof: by the defining comap measurable-space construction.
Source: Mathlib measure-theory measurable-space comap APIs
Used in: stochastic accelerated gradient descent state/sample transition
  measurability
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/initialization
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem feasibleAcceleratedState_coordinates_measurable
    {E : Type*} [MeasurableSpace E] (X : Set E) :
    @Measurable (FeasibleAcceleratedState X) (E × E)
      (feasibleAcceleratedStateMeasurableSpace X) inferInstance
      (fun s => (s.x, s.xBar)) := by
  exact measurable_iff_comap_le.mpr le_rfl

/-- Accelerated averaged iterate `x̄_t = (1 - α_t) x̄_{t-1} + α_t x_t`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; two-point affine average)
Source: accelerated stochastic approximation averaged-iterate recurrence
Used in: stochastic accelerated gradient descent feasible state updates
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
def acceleratedAveragePoint
    {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    (alpha : ℕ → ℝ) (t : {n : ℕ // 1 ≤ n}) (xBarPrev xNext : E) : E :=
  (1 - alpha t.1) • xBarPrev + alpha t.1 • xNext

/-- The accelerated averaged iterate unfolds to its affine-combination formula.

Layer: Model | Gap: Level 0 (accelerated average-point unfolding)
Proof: by rfl after unfolding `acceleratedAveragePoint`.
Source: accelerated stochastic approximation averaged-iterate recurrence
Used in: stochastic accelerated gradient descent feasible state updates
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
@[simp]
theorem acceleratedAveragePoint_def
    {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    (alpha : ℕ → ℝ) (t : {n : ℕ // 1 ≤ n}) (xBarPrev xNext : E) :
    acceleratedAveragePoint alpha t xBarPrev xNext =
      (1 - alpha t.1) • xBarPrev + alpha t.1 • xNext := by
  rfl

/-- The accelerated averaged iterate stays in a convex feasible set.

If the previous averaged iterate and the new iterate are feasible, and the
averaging coefficient `alpha_t` lies in `[0,1]`, then the two-point affine blend
`(1 - alpha_t) • xBarPrev + alpha_t • xNext` is feasible.

Layer: Model | Gap: Level 0 (accelerated average-point convex feasibility)
Proof: split `alpha_t ∈ [0,1]` into nonnegativity and upper-bound facts, build
  the two nonnegative convex weights, and close the affine blend by the
  two-point convex-combination membership characterization.
Source: Mathlib convex-set API for real affine combinations
Used in: accelerated stochastic gradient descent feasibility of the averaged
  iterate after the stochastic prox step
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem acceleratedAveragePoint_mem
    {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    {X : Set E} (hX : Convex ℝ X)
    (alpha : ℕ → ℝ) (t : {n : ℕ // 1 ≤ n})
    (halpha : alpha t.1 ∈ Set.Icc (0 : ℝ) 1)
    {xBarPrev xNext : E}
    (hxBarPrev : xBarPrev ∈ X) (hxNext : xNext ∈ X) :
    acceleratedAveragePoint alpha t xBarPrev xNext ∈ X := by
  rcases Set.mem_Icc.mp halpha with ⟨halpha_nonneg, halpha_le_one⟩
  exact convex_iff_add_mem.mp hX hxBarPrev hxNext
    (sub_nonneg.mpr halpha_le_one) halpha_nonneg (by ring)

/-- Alias form of accelerated averaged-iterate feasibility for callers using
the `_of_mem` suffix.

Layer: Model | Gap: Level 0 (accelerated average-point convex feasibility)
Proof: direct application of `acceleratedAveragePoint_mem`.
Source: Mathlib convex-set API for real affine combinations
Used in: accelerated stochastic gradient descent feasible state updates
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem acceleratedAveragePoint_mem_of_mem
    {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    {X : Set E} (hX : Convex ℝ X)
    (alpha : ℕ → ℝ) (t : {n : ℕ // 1 ≤ n})
    (halpha : alpha t.1 ∈ Set.Icc (0 : ℝ) 1)
    {xBarPrev xNext : E}
    (hxBarPrev : xBarPrev ∈ X) (hxNext : xNext ∈ X) :
    acceleratedAveragePoint alpha t xBarPrev xNext ∈ X :=
  acceleratedAveragePoint_mem hX alpha t halpha hxBarPrev hxNext

/-- Feasible accelerated state transition from a time-indexed sample kernel.

Given a sample kernel for the next prox coordinate and an averaging update for
the output coordinate, this constructor packages the two coordinates together
with their carrier-membership witnesses as a feasible accelerated state.

Layer: Model | Concept: Iterates
Proof: (definitional construction; bundled prox-coordinate sample-kernel update
  plus averaged-output coordinate with pointwise feasibility witnesses)
Source: accelerated stochastic approximation state recursions and Mathlib
  subtype/Set membership APIs
Used in: stochastic accelerated gradient descent sample-kernel transition before
  recursive-process adaptedness and measurability arguments
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
noncomputable def accelerated_step_from_sample
    {E Time Sample : Type*} {X : Set E}
    (timeOfNat : ℕ → Time)
    (average : Time → FeasibleAcceleratedState X → E → E)
    (kernel : Time → FeasibleAcceleratedState X → Sample → E)
    (hkernel_mem :
      ∀ (t : Time) (prev : FeasibleAcceleratedState X) (ξ : Sample),
        kernel t prev ξ ∈ X)
    (haverage_mem :
      ∀ (t : Time) (prev : FeasibleAcceleratedState X) {xNext : E},
        xNext ∈ X → average t prev xNext ∈ X)
    (k : ℕ)
    (prev : FeasibleAcceleratedState X)
    (ξ : Sample) :
    FeasibleAcceleratedState X :=
  let t := timeOfNat k
  let xNext := kernel t prev ξ
  let hxNext := hkernel_mem t prev ξ
  let xBarNext := average t prev xNext
  let hxBarNext := haverage_mem t prev hxNext
  ⟨xNext, xBarNext, hxNext, hxBarNext⟩

@[simp]
theorem accelerated_step_from_sample_def
    {E Time Sample : Type*} {X : Set E}
    (timeOfNat : ℕ → Time)
    (average : Time → FeasibleAcceleratedState X → E → E)
    (kernel : Time → FeasibleAcceleratedState X → Sample → E)
    (hkernel_mem :
      ∀ (t : Time) (prev : FeasibleAcceleratedState X) (ξ : Sample),
        kernel t prev ξ ∈ X)
    (haverage_mem :
      ∀ (t : Time) (prev : FeasibleAcceleratedState X) {xNext : E},
        xNext ∈ X → average t prev xNext ∈ X)
    (k : ℕ)
    (prev : FeasibleAcceleratedState X)
    (ξ : Sample) :
    accelerated_step_from_sample timeOfNat average kernel hkernel_mem haverage_mem
        k prev ξ =
      ⟨kernel (timeOfNat k) prev ξ,
        average (timeOfNat k) prev (kernel (timeOfNat k) prev ξ),
        hkernel_mem (timeOfNat k) prev ξ,
        haverage_mem (timeOfNat k) prev (hkernel_mem (timeOfNat k) prev ξ)⟩ := rfl

@[simp]
theorem accelerated_step_from_sample_x
    {E Time Sample : Type*} {X : Set E}
    (timeOfNat : ℕ → Time)
    (average : Time → FeasibleAcceleratedState X → E → E)
    (kernel : Time → FeasibleAcceleratedState X → Sample → E)
    (hkernel_mem :
      ∀ (t : Time) (prev : FeasibleAcceleratedState X) (ξ : Sample),
        kernel t prev ξ ∈ X)
    (haverage_mem :
      ∀ (t : Time) (prev : FeasibleAcceleratedState X) {xNext : E},
        xNext ∈ X → average t prev xNext ∈ X)
    (k : ℕ)
    (prev : FeasibleAcceleratedState X)
    (ξ : Sample) :
    (accelerated_step_from_sample timeOfNat average kernel hkernel_mem haverage_mem
        k prev ξ).x =
      kernel (timeOfNat k) prev ξ := rfl

@[simp]
theorem accelerated_step_from_sample_x_bar
    {E Time Sample : Type*} {X : Set E}
    (timeOfNat : ℕ → Time)
    (average : Time → FeasibleAcceleratedState X → E → E)
    (kernel : Time → FeasibleAcceleratedState X → Sample → E)
    (hkernel_mem :
      ∀ (t : Time) (prev : FeasibleAcceleratedState X) (ξ : Sample),
        kernel t prev ξ ∈ X)
    (haverage_mem :
      ∀ (t : Time) (prev : FeasibleAcceleratedState X) {xNext : E},
        xNext ∈ X → average t prev xNext ∈ X)
    (k : ℕ)
    (prev : FeasibleAcceleratedState X)
    (ξ : Sample) :
    (accelerated_step_from_sample timeOfNat average kernel hkernel_mem haverage_mem
        k prev ξ).xBar =
      average (timeOfNat k) prev (kernel (timeOfNat k) prev ξ) := rfl

theorem accelerated_step_from_sample_x_mem
    {E Time Sample : Type*} {X : Set E}
    (timeOfNat : ℕ → Time)
    (average : Time → FeasibleAcceleratedState X → E → E)
    (kernel : Time → FeasibleAcceleratedState X → Sample → E)
    (hkernel_mem :
      ∀ (t : Time) (prev : FeasibleAcceleratedState X) (ξ : Sample),
        kernel t prev ξ ∈ X)
    (haverage_mem :
      ∀ (t : Time) (prev : FeasibleAcceleratedState X) {xNext : E},
        xNext ∈ X → average t prev xNext ∈ X)
    (k : ℕ)
    (prev : FeasibleAcceleratedState X)
    (ξ : Sample) :
    (accelerated_step_from_sample timeOfNat average kernel hkernel_mem haverage_mem
        k prev ξ).x ∈ X := by
  simpa using hkernel_mem (timeOfNat k) prev ξ

theorem accelerated_step_from_sample_x_bar_mem
    {E Time Sample : Type*} {X : Set E}
    (timeOfNat : ℕ → Time)
    (average : Time → FeasibleAcceleratedState X → E → E)
    (kernel : Time → FeasibleAcceleratedState X → Sample → E)
    (hkernel_mem :
      ∀ (t : Time) (prev : FeasibleAcceleratedState X) (ξ : Sample),
        kernel t prev ξ ∈ X)
    (haverage_mem :
      ∀ (t : Time) (prev : FeasibleAcceleratedState X) {xNext : E},
        xNext ∈ X → average t prev xNext ∈ X)
    (k : ℕ)
    (prev : FeasibleAcceleratedState X)
    (ξ : Sample) :
    (accelerated_step_from_sample timeOfNat average kernel hkernel_mem haverage_mem
        k prev ξ).xBar ∈ X := by
  simpa using haverage_mem (timeOfNat k) prev (hkernel_mem (timeOfNat k) prev ξ)

/-- Feasible omega-indexed accelerated state transition from a prox-step selector.

Given a feasible omega-indexed prox/update coordinate, the standard accelerated
averaged-coordinate formula also remains feasible under convexity and
`alpha_t ∈ [0,1]`; the two coordinates are bundled as a feasible accelerated
state.

Layer: Model | Concept: Iterates
Proof: (definitional construction; instantiate the generic sample-step state
  constructor with `Sample = Ω`, use `acceleratedAveragePoint` for the averaged
  coordinate, and close its feasibility by convex combination membership)
Source: accelerated stochastic approximation state recursions and Mathlib
  convex-set APIs for real affine combinations
Used in: stochastic accelerated gradient descent omega-indexed recursive step
  before comparison with the causal sample-kernel transition
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
noncomputable def accelerated_step_from_state
    {E Ω : Type*} [AddCommMonoid E] [SMul ℝ E]
    {X : Set E}
    (alpha : ℕ → ℝ)
    (hX : Convex ℝ X)
    (halpha : ∀ t : {n : ℕ // 1 ≤ n}, alpha t.1 ∈ Set.Icc (0 : ℝ) 1)
    (proxStep : {n : ℕ // 1 ≤ n} → FeasibleAcceleratedState X → Ω → E)
    (hprox_mem :
      ∀ (t : {n : ℕ // 1 ≤ n}) (prev : FeasibleAcceleratedState X) (ω : Ω),
        proxStep t prev ω ∈ X)
    (k : ℕ)
    (prev : FeasibleAcceleratedState X)
    (ω : Ω) :
    FeasibleAcceleratedState X :=
  accelerated_step_from_sample natSuccPositiveTime
    (fun t prev xNext => acceleratedAveragePoint alpha t prev.xBar xNext)
    proxStep hprox_mem
    (fun t prev {_xNext} hxNext =>
      acceleratedAveragePoint_mem_of_mem hX alpha t (halpha t) prev.hxBar hxNext)
    k prev ω

@[simp]
theorem accelerated_step_from_state_def
    {E Ω : Type*} [AddCommMonoid E] [SMul ℝ E]
    {X : Set E}
    (alpha : ℕ → ℝ)
    (hX : Convex ℝ X)
    (halpha : ∀ t : {n : ℕ // 1 ≤ n}, alpha t.1 ∈ Set.Icc (0 : ℝ) 1)
    (proxStep : {n : ℕ // 1 ≤ n} → FeasibleAcceleratedState X → Ω → E)
    (hprox_mem :
      ∀ (t : {n : ℕ // 1 ≤ n}) (prev : FeasibleAcceleratedState X) (ω : Ω),
        proxStep t prev ω ∈ X)
    (k : ℕ)
    (prev : FeasibleAcceleratedState X)
    (ω : Ω) :
    accelerated_step_from_state alpha hX halpha proxStep hprox_mem k prev ω =
      ⟨proxStep (natSuccPositiveTime k) prev ω,
        acceleratedAveragePoint alpha (natSuccPositiveTime k) prev.xBar
          (proxStep (natSuccPositiveTime k) prev ω),
        hprox_mem (natSuccPositiveTime k) prev ω,
        acceleratedAveragePoint_mem_of_mem hX alpha (natSuccPositiveTime k)
          (halpha (natSuccPositiveTime k)) prev.hxBar
          (hprox_mem (natSuccPositiveTime k) prev ω)⟩ := rfl

@[simp]
theorem accelerated_step_from_state_x
    {E Ω : Type*} [AddCommMonoid E] [SMul ℝ E]
    {X : Set E}
    (alpha : ℕ → ℝ)
    (hX : Convex ℝ X)
    (halpha : ∀ t : {n : ℕ // 1 ≤ n}, alpha t.1 ∈ Set.Icc (0 : ℝ) 1)
    (proxStep : {n : ℕ // 1 ≤ n} → FeasibleAcceleratedState X → Ω → E)
    (hprox_mem :
      ∀ (t : {n : ℕ // 1 ≤ n}) (prev : FeasibleAcceleratedState X) (ω : Ω),
        proxStep t prev ω ∈ X)
    (k : ℕ)
    (prev : FeasibleAcceleratedState X)
    (ω : Ω) :
    (accelerated_step_from_state alpha hX halpha proxStep hprox_mem k prev ω).x =
      proxStep (natSuccPositiveTime k) prev ω := rfl

@[simp]
theorem accelerated_step_from_state_x_bar
    {E Ω : Type*} [AddCommMonoid E] [SMul ℝ E]
    {X : Set E}
    (alpha : ℕ → ℝ)
    (hX : Convex ℝ X)
    (halpha : ∀ t : {n : ℕ // 1 ≤ n}, alpha t.1 ∈ Set.Icc (0 : ℝ) 1)
    (proxStep : {n : ℕ // 1 ≤ n} → FeasibleAcceleratedState X → Ω → E)
    (hprox_mem :
      ∀ (t : {n : ℕ // 1 ≤ n}) (prev : FeasibleAcceleratedState X) (ω : Ω),
        proxStep t prev ω ∈ X)
    (k : ℕ)
    (prev : FeasibleAcceleratedState X)
    (ω : Ω) :
    (accelerated_step_from_state alpha hX halpha proxStep hprox_mem k prev ω).xBar =
      acceleratedAveragePoint alpha (natSuccPositiveTime k) prev.xBar
        (proxStep (natSuccPositiveTime k) prev ω) := rfl

theorem accelerated_step_from_state_x_mem
    {E Ω : Type*} [AddCommMonoid E] [SMul ℝ E]
    {X : Set E}
    (alpha : ℕ → ℝ)
    (hX : Convex ℝ X)
    (halpha : ∀ t : {n : ℕ // 1 ≤ n}, alpha t.1 ∈ Set.Icc (0 : ℝ) 1)
    (proxStep : {n : ℕ // 1 ≤ n} → FeasibleAcceleratedState X → Ω → E)
    (hprox_mem :
      ∀ (t : {n : ℕ // 1 ≤ n}) (prev : FeasibleAcceleratedState X) (ω : Ω),
        proxStep t prev ω ∈ X)
    (k : ℕ)
    (prev : FeasibleAcceleratedState X)
    (ω : Ω) :
    (accelerated_step_from_state alpha hX halpha proxStep hprox_mem k prev ω).x ∈ X := by
  simpa using hprox_mem (natSuccPositiveTime k) prev ω

theorem accelerated_step_from_state_x_bar_mem
    {E Ω : Type*} [AddCommMonoid E] [SMul ℝ E]
    {X : Set E}
    (alpha : ℕ → ℝ)
    (hX : Convex ℝ X)
    (halpha : ∀ t : {n : ℕ // 1 ≤ n}, alpha t.1 ∈ Set.Icc (0 : ℝ) 1)
    (proxStep : {n : ℕ // 1 ≤ n} → FeasibleAcceleratedState X → Ω → E)
    (hprox_mem :
      ∀ (t : {n : ℕ // 1 ≤ n}) (prev : FeasibleAcceleratedState X) (ω : Ω),
        proxStep t prev ω ∈ X)
    (k : ℕ)
    (prev : FeasibleAcceleratedState X)
    (ω : Ω) :
    (accelerated_step_from_state alpha hX halpha proxStep hprox_mem k prev ω).xBar ∈ X := by
  simpa using
    acceleratedAveragePoint_mem_of_mem hX alpha (natSuccPositiveTime k)
      (halpha (natSuccPositiveTime k)) prev.hxBar
      (hprox_mem (natSuccPositiveTime k) prev ω)

/-- An accelerated omega-indexed state step agrees with its sample-kernel form
along the realized sample stream.

If the prox/update coordinate selected from `Ω` factors through a sample kernel,
and the sample-step averaging map is the standard accelerated averaged point,
then the bundled feasible accelerated state transition factors through the same
sample kernel.

Layer: Model | Gap: Level 1 (accelerated state sample-factorization bridge)
Proof: unfold the omega-indexed and sample-kernel accelerated state
  constructors, rewrite the prox coordinate by the supplied kernel
  factorization, rewrite the averaged coordinate by the supplied average
  compatibility, and close record proof fields by proof irrelevance.
Source: accelerated stochastic approximation state recursions, Mathlib subtype
  record equality, and proof-irrelevance APIs
Used in: stochastic accelerated gradient descent adaptedness bridge from an
  omega-indexed prox selector to a causal fresh-sample state kernel
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem accelerated_step_from_state_eq_step_from_sample
    {E Ω Sample : Type*} [AddCommMonoid E] [SMul ℝ E]
    {X : Set E}
    (alpha : ℕ → ℝ)
    (hX : Convex ℝ X)
    (halpha : ∀ t : {n : ℕ // 1 ≤ n}, alpha t.1 ∈ Set.Icc (0 : ℝ) 1)
    (sample : ℕ → Ω → Sample)
    (omegaKernel : {n : ℕ // 1 ≤ n} → FeasibleAcceleratedState X → Ω → E)
    (sampleKernel : {n : ℕ // 1 ≤ n} → FeasibleAcceleratedState X → Sample → E)
    (homega_mem :
      ∀ (t : {n : ℕ // 1 ≤ n}) (prev : FeasibleAcceleratedState X) (ω : Ω),
        omegaKernel t prev ω ∈ X)
    (hsample_mem :
      ∀ (t : {n : ℕ // 1 ≤ n}) (prev : FeasibleAcceleratedState X) (ξ : Sample),
        sampleKernel t prev ξ ∈ X)
    (average : {n : ℕ // 1 ≤ n} → FeasibleAcceleratedState X → E → E)
    (haverage_mem :
      ∀ (t : {n : ℕ // 1 ≤ n}) (prev : FeasibleAcceleratedState X) {xNext : E},
        xNext ∈ X → average t prev xNext ∈ X)
    (k : ℕ)
    (prev : FeasibleAcceleratedState X)
    (ω : Ω)
    (hkernel :
      omegaKernel (natSuccPositiveTime k) prev ω =
        sampleKernel (natSuccPositiveTime k) prev (sample (k + 1) ω))
    (haverage_eq :
      average (natSuccPositiveTime k) prev
          (sampleKernel (natSuccPositiveTime k) prev (sample (k + 1) ω)) =
        acceleratedAveragePoint alpha (natSuccPositiveTime k) prev.xBar
          (sampleKernel (natSuccPositiveTime k) prev (sample (k + 1) ω))) :
    accelerated_step_from_state alpha hX halpha omegaKernel homega_mem k prev ω =
      accelerated_step_from_sample natSuccPositiveTime average sampleKernel
        hsample_mem haverage_mem k prev (sample (k + 1) ω) := by
  have hkernel' :
      omegaKernel ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩ prev ω =
        sampleKernel ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩ prev
          (sample (k + 1) ω) := by
    simpa [natSuccPositiveTime] using hkernel
  have haverage_eq' :
      average ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩ prev
          (sampleKernel ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩ prev
            (sample (k + 1) ω)) =
        acceleratedAveragePoint alpha
          ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩ prev.xBar
          (sampleKernel ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩ prev
            (sample (k + 1) ω)) := by
    simpa [natSuccPositiveTime] using haverage_eq
  simp [accelerated_step_from_state, accelerated_step_from_sample,
    natSuccPositiveTime]
  constructor
  · exact hkernel'
  · rw [hkernel']
    simpa [acceleratedAveragePoint, natSuccPositiveTime] using haverage_eq'.symm

/-- A recursive process whose raw transition factors through a sample driver has
the corresponding sample-update successor equation.

If `process` is generated by an omega-indexed transition `omegaStep`, and
`omegaStep n state omega` agrees pointwise with a sample update applied to
`driver n omega`, then the successor time slice of `process` is exactly the
sample-update function of the previous slice.

Layer: Model | Gap: Level 1 (recursive process sample-update bridge)
Proof: unfold the recursive successor using `recursiveIterateProcess_succ`, then
  rewrite the raw transition by the supplied sample-factorization law.
Source: Mathlib natural-number primitive recursion and Pi-function extensionality APIs
Used in: accelerated stochastic gradient descent generated-process adaptedness
  through a fresh-sample prox kernel
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem recursiveProcess_succ_eq_sample_update
    {Ω State Sample : Type*}
    (process : ℕ → Ω → State)
    (initial : State)
    (omegaStep : ℕ → State → Ω → State)
    (driver : ℕ → Ω → Sample)
    (sampleStep : ℕ → State → Sample → State)
    (h_process : process = recursiveIterateProcess initial omegaStep)
    (h_step : ∀ n state ω, omegaStep n state ω = sampleStep n state (driver n ω))
    (k : ℕ) :
    process (k + 1) = fun ω => sampleStep k (process k ω) (driver k ω) := by
  funext ω
  calc
    process (k + 1) ω = omegaStep k (process k ω) ω :=
      recursiveIterateProcess_succ process initial omegaStep h_process k ω
    _ = sampleStep k (process k ω) (driver k ω) :=
      h_step k (process k ω) ω

/-- A recursive process driven by sample-prefix-measurable coordinates is
measurable with respect to any containing sample prefix.

If each driver coordinate `driver j` is measurable with respect to its own
prefix `past ((j + 1) + 1)`, the prefix family is monotone, and the process
recurses through a measurable state-driver update, then every state up to `N`
is measurable with respect to the containing prefix `past (N + 1)`.

Layer: Model | Gap: Level 1 (recursive process measurability over containing sample prefixes)
Proof: apply the fixed-sigma-algebra recursive measurability induction from
  `recursiveProcess_measurable_wrt_strictPast`; the only extra step is lifting
  each driver coordinate into the containing prefix by monotonicity.
Source: Mathlib measure-theory APIs for measurable-space monotonicity and
  measurable product composition
Used in: accelerated stochastic gradient prefix-adapted state recursion
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem recursive_process_measurable_wrt_sample_prefix
    {Ω X U : Type*} [MeasurableSpace X] [MeasurableSpace U]
    (past : ℕ → MeasurableSpace Ω)
    (process : ℕ → Ω → X)
    (driver : ℕ → Ω → U)
    (step : ℕ → X → U → X)
    (N n : ℕ)
    (h_past_mono : ∀ {a b : ℕ}, a ≤ b → past a ≤ past b)
    (h_init : Measurable[past (N + 1)] (process 0))
    (h_driver_prefix :
      ∀ j, j + 1 ≤ N → Measurable[past ((j + 1) + 1)] (driver j))
    (h_step :
      ∀ j, j + 1 ≤ N → Measurable (fun p : X × U => step j p.1 p.2))
    (h_update :
      ∀ j, j + 1 ≤ N →
        process (j + 1) = fun ω => step j (process j ω) (driver j ω))
    (hn : n ≤ N) :
    Measurable[past (N + 1)] (process n) := by
  refine
    recursiveProcess_measurable_wrt_strictPast
      (past := past)
      (process := process)
      (driver := driver)
      (step := step)
      (k := N + 1)
      (N := N)
      h_init ?_ h_step h_update n hn
  intro j hj _hprocess
  have hle : (j + 1) + 1 ≤ N + 1 := Nat.succ_le_succ hj
  exact (h_driver_prefix j hj).mono (h_past_mono hle) le_rfl

/-- A two-coordinate state/sample transition is measurable when its kernel
coordinate is measurable and its second coordinate is an affine average.

The target state measurable space may be no finer than the sigma-algebra
generated by `coord`. This captures feasible accelerated states where proof
fields are ignored by measurability and the recursive state is determined by
the prox/update coordinate and averaged output coordinate.

Layer: Model | Gap: Level 1 (two-coordinate state/sample transition measurability)
Proof: compose the measurable coordinate reader with product projection, build
  the affine averaged coordinate from measurable scalar multiplication and
  addition, then close the target-state statement through the coordinate-generated
  measurable space.
Source: Mathlib measure-theory product measurable-space and additive measurable
  algebra APIs
Used in: stochastic accelerated gradient descent generated prox-kernel update
  before recursive-process prefix measurability
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem state_sample_step_measurable_of_coordinate_kernel_average
    {State Sample E : Type*}
    [MeasurableSpace State] [MeasurableSpace Sample] [MeasurableSpace E]
    [Add E] [SMul ℝ E] [MeasurableAdd₂ E] [MeasurableConstSMul ℝ E]
    (coord : State → E × E)
    (kernel : State → Sample → E)
    (average : State → E → E)
    (step : State → Sample → State)
    (leftWeight rightWeight : ℝ)
    (hcoord_measurable : Measurable coord)
    (hstate_le_coord :
      (inferInstance : MeasurableSpace State) ≤
        MeasurableSpace.comap coord (inferInstance : MeasurableSpace (E × E)))
    (hkernel_measurable :
      Measurable (fun p : State × Sample => kernel p.1 p.2))
    (haverage_on_kernel :
      ∀ s ξ,
        average s (kernel s ξ) =
          leftWeight • (coord s).2 + rightWeight • kernel s ξ)
    (hstep :
      ∀ s ξ, coord (step s ξ) = (kernel s ξ, average s (kernel s ξ))) :
    Measurable (fun p : State × Sample => step p.1 p.2) := by
  have hprevBar :
      Measurable (fun p : State × Sample => (coord p.1).2) :=
    (hcoord_measurable.comp measurable_fst).snd
  have haverage_measurable :
      Measurable
        (fun p : State × Sample =>
          average p.1 (kernel p.1 p.2)) := by
    simpa [haverage_on_kernel] using
      (hprevBar.const_smul leftWeight).add
        (hkernel_measurable.const_smul rightWeight)
  have hcoord_step :
      Measurable
        (fun p : State × Sample =>
          coord (step p.1 p.2)) := by
    simpa [hstep] using hkernel_measurable.prodMk haverage_measurable
  refine Measurable.of_comap_le ?_
  exact le_trans (MeasurableSpace.comap_mono hstate_le_coord) (by
    simpa [Function.comp_def] using hcoord_step.comap_le)

/-- A state-valued map is measurable when its coordinate map is measurable and
the state sigma-algebra is bounded by the coordinate comap.

This is useful for state records whose measurable structure intentionally
forgets proof fields: once the visible coordinates of `f` are measurable,
measurability of `f` follows from the comap bound.

Layer: Glue | Gap: Level 0 (codomain coordinate-comap measurability closure)
Proof: rewrite `coord ∘ f` to the measurable coordinate process, use its comap
  bound, then transport that bound through monotonicity of codomain comap and
  apply `Measurable.of_comap_le`.
Source: Mathlib measure-theory measurable-space comap and product-coordinate APIs
Used in: stochastic accelerated gradient descent sample-kernel state transition
  after prox and averaged-output coordinate measurability
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem measurable_to_comap_state_of_measurable_coordinates
    {Ω A B : Type*} [MeasurableSpace Ω] [mA : MeasurableSpace A]
    [MeasurableSpace B]
    (coord : A → B) (f : Ω → A)
    (hcoord_f : Measurable (fun ω : Ω => coord (f ω)))
    (hA_le_coord :
      mA ≤ MeasurableSpace.comap coord (inferInstance : MeasurableSpace B)) :
    Measurable f := by
  refine Measurable.of_comap_le ?_
  exact le_trans (MeasurableSpace.comap_mono hA_le_coord) (by
    simpa [Function.comp_def] using hcoord_f.comap_le)

end SOptLib

namespace SOptLib

/-- A recursively defined stochastic process is measurable at every time.

If the initial state is constant, every oracle call is measurable along a
measurable random query, and every time-indexed update is measurable on the
state-oracle product, then all slices of the recursive process are measurable.

Layer: Model | Gap: Level 1 (recursive process measurability induction)
Proof: induction on the natural-number iterate counter; the successor step
  composes the measurable product of the previous process and oracle with the
  measurable update map.
Source: Mathlib measure-theory APIs for measurable products and composition
Used in: randomized stochastic mirror descent mini-batch prox iterate
  measurability
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
theorem recursive_process_measurable_of_measurable_update
    {Ω P D : Type*} [MeasurableSpace Ω] [MeasurableSpace P] [MeasurableSpace D]
    (x0 : P)
    (oracle : ℕ → (Ω → P) → Ω → D)
    (update : ℕ → P → D → P)
    (process : ℕ → Ω → P)
    (h_zero : process 0 = fun _ => x0)
    (h_oracle : ∀ n (x : Ω → P), Measurable x → Measurable (fun ω => oracle n x ω))
    (h_update : ∀ n, Measurable (fun p : P × D => update n p.1 p.2))
    (h_succ : ∀ n,
      process (n + 1) = fun ω => update n (process n ω) (oracle n (process n) ω)) :
    ∀ n : ℕ, Measurable (process n) := by
  intro n
  induction n with
  | zero =>
      simp [h_zero]
  | succ n ih =>
      have hg : Measurable (fun ω => oracle n (process n) ω) :=
        h_oracle n (process n) ih
      have hu : Measurable (fun p : P × D => update n p.1 p.2) :=
        h_update n
      simpa [h_succ n] using hu.comp (ih.prodMk hg)

/-- The finite set of squared real values indexed by a finite run type.

For a finite family of real observables `value : ι → ℝ`, this packages the
image of `i ↦ value i ^ 2` over all runs as a canonical finite set.

Layer: Model | Concept: Iterates
Proof: (definitional construction; finite image of the squared run observable)
Source: Mathlib finite-set image API for finitely indexed real families
Used in: nonconvex stochastic mirror descent finite-run exact stationarity
  minimum over independent runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def finiteRunSqValues
    {ι : Type*} [Fintype ι]
    (value : ι → ℝ) : Finset ℝ := by
  classical
  exact Finset.univ.image (fun i : ι => value i ^ 2)

/-- Membership in the finite squared-value set is exactly attainment by an index.

For a finite run family `value : ι → ℝ`, a real number belongs to
`finiteRunSqValues value` iff it is the square of one indexed value.

Layer: Model | Gap: Level 0 (finite squared-value membership)
Proof: unfold `finiteRunSqValues` and use Mathlib's `Finset.mem_image`
  simplification for the universal finite set.
Source: Mathlib finite-set image membership API for finitely indexed real families
Used in: nonconvex stochastic mirror descent finite-run exact stationarity
  minimum over independent runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
@[simp]
theorem mem_finiteRunSqValues
    {ι : Type*} [Fintype ι]
    (value : ι → ℝ) (x : ℝ) :
    x ∈ finiteRunSqValues value ↔ ∃ i : ι, value i ^ 2 = x := by
  classical
  simp [finiteRunSqValues]

/-- The image of `Finset.univ` under a function from a nonempty finite type is nonempty.

For any finite nonempty index type, choosing one index gives a witness in the
finite image value set. This is the abstract finite-run nonemptiness fact used
before taking minima or maxima over run-indexed values.

Layer: Model | Gap: Level 0 (finite image value set nonemptiness)
Proof: choose an index from the `Nonempty` instance and simplify membership in
  the image of `Finset.univ`.
Source: Mathlib finite-set image and finite type APIs
Used in: nonconvex stochastic mirror descent finite-run exact stationarity
  minimum over independent runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem finset_univ_image_nonempty
    {ι α : Type*} [Fintype ι] [Nonempty ι] [DecidableEq α]
    (value : ι → α) :
    (Finset.univ.image value).Nonempty := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ⟨value i, by simp⟩

/-- Select a run output from a stopping-vector outcome.

`runOutput output R s ω` is the abstract model object behind the notation
`\bar{x}_s = x_{R_s}`: the stopping vector `R` chooses the output time for
run `s`, and the output process is evaluated at the sample point `ω`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; stopping-vector projection followed by
  sample-wise output-process evaluation)
Source: Mathlib Pi-function evaluation and subtype-indexed iterate notation
Used in: nonconvex stochastic mirror descent stopping-vector randomized output
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def runOutput
    {Run Out Ω X : Type*}
    (output : Run → Out → Ω → X)
    (R : Run → Out) (s : Run) (ω : Ω) : X :=
  output s (R s) ω

/-- Product weight of a finite vector of stopping outcomes.

For a one-coordinate real mass function `p`, `stoppingVectorWeight p R`
multiplies the masses of all coordinates in the finite vector `R`. This is
the real-valued product weight used before embedding the mass into `ℝ≥0∞`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; finite product of coordinate stopping masses)
Source: Mathlib finite products over `Fintype` index sets
Used in: nonconvex stochastic mirror descent independent randomized stopping
  vector law for multiple runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def stoppingVectorWeight
    {ι α : Type*} [Fintype ι]
    (p : α → ℝ) (R : ι → α) : ℝ :=
  ∏ s : ι, p (R s)

/-- Product stopping-vector weights normalize when the one-coordinate weights normalize.

For finite index and outcome types, nonnegative real one-coordinate weights whose
`ENNReal.ofReal` masses sum to one induce normalized product weights on vectors
`ι → α` after embedding the real product weight into `ℝ≥0∞`.

Layer: Model | Gap: Level 1 (finite product stopping-vector normalization)
Proof: rewrite `ofReal` of the finite real product as a product of one-coordinate
  `ofReal` masses using nonnegativity, then apply `Finset.prod_univ_sum`.
Source: Mathlib finite products, finite sums, and extended nonnegative real APIs
Used in: nonconvex stochastic mirror descent independent randomized stopping
  vector law for multiple runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem stoppingVectorWeight_ofReal_sum_eq_one
    {ι α : Type*} [DecidableEq ι] [Fintype ι] [Fintype α]
    (p : α → ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a)
    (hp_sum : (∑ a : α, ENNReal.ofReal (p a)) = 1) :
    (∑ R : ι → α, ENNReal.ofReal (stoppingVectorWeight p R)) = 1 := by
  classical
  calc
    (∑ R : ι → α, ENNReal.ofReal (stoppingVectorWeight p R))
        = ∑ R : ι → α, ∏ s : ι, ENNReal.ofReal (p (R s)) := by
          refine Finset.sum_congr rfl ?_
          intro R _hR
          rw [stoppingVectorWeight, ENNReal.ofReal_prod_of_nonneg]
          intro s _hs
          exact hp_nonneg (R s)
    _ = ∏ s : ι, ∑ a : α, ENNReal.ofReal (p a) := by
          simpa [Fintype.piFinset_univ] using
            (Finset.prod_univ_sum
              (fun _ : ι => (Finset.univ : Finset α))
              (fun _s a => ENNReal.ofReal (p a))).symm
    _ = 1 := by
          simp [hp_sum]

/-- Build the product PMF for a finite vector of independent stopping indices.

Given nonnegative real masses on a finite stopping-index type whose
`ENNReal.ofReal` masses sum to one, this constructs the finite product law on
vectors `ι → α`.  The vector-weight function is explicit so callers can keep
their local notation for the product of coordinate masses.

Layer: Model | Concept: Iterates
Proof: (definitional construction; finite product PMF from normalized real
  coordinate weights via `Finset.prod_univ_sum`)
Source: Mathlib probability mass functions, finite products, and extended
  nonnegative real APIs
Used in: nonconvex stochastic mirror descent independent randomized stopping
  vector law for multiple runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def stoppingVectorPMF
    {ι α : Type*} [DecidableEq ι] [Fintype ι] [Fintype α]
    (p : α → ℝ)
    (w : (ι → α) → ℝ)
    (hw : ∀ R, w R = ∏ s : ι, p (R s))
    (hp_nonneg : ∀ a, 0 ≤ p a)
    (hp_sum : (∑ a : α, ENNReal.ofReal (p a)) = 1) :
    PMF (ι → α) :=
  PMF.ofFintype (fun R : ι → α => ENNReal.ofReal (w R)) (by
    classical
    calc
      (∑ R : ι → α, ENNReal.ofReal (w R))
          = ∑ R : ι → α, ENNReal.ofReal (∏ s : ι, p (R s)) := by
            refine Finset.sum_congr rfl ?_
            intro R _hR
            rw [hw R]
      _ = ∑ R : ι → α, ∏ s : ι, ENNReal.ofReal (p (R s)) := by
            refine Finset.sum_congr rfl ?_
            intro R _hR
            rw [ENNReal.ofReal_prod_of_nonneg]
            intro s _hs
            exact hp_nonneg (R s)
      _ = ∏ s : ι, ∑ a : α, ENNReal.ofReal (p a) := by
            simpa [Fintype.piFinset_univ] using
              (Finset.prod_univ_sum
                (fun _ : ι => (Finset.univ : Finset α))
                (fun _s a => ENNReal.ofReal (p a))).symm
      _ = 1 := by
            simp [hp_sum])

/-- The product PMF assigns each stopping vector its explicit vector weight.

This is the pointwise specification for `stoppingVectorPMF`: the mass of a
finite vector `R` is the extended nonnegative embedding of the caller-provided
vector weight, whose product form is supplied by a separate hypothesis.

Layer: Model | Gap: Level 0 (finite product stopping-vector PMF evaluation)
Proof: unfold `stoppingVectorPMF`; the `PMF.ofFintype` constructor stores the
  stated mass function definitionally.
Source: Mathlib probability mass functions and finite product APIs
Used in: nonconvex stochastic mirror descent finite weighted-sum expansions over
  independent randomized stopping vectors
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
@[simp]
theorem stoppingVectorPMF_apply
    {ι α : Type*} [DecidableEq ι] [Fintype ι] [Fintype α]
    (p : α → ℝ)
    (w : (ι → α) → ℝ)
    (hw : ∀ R, w R = ∏ s : ι, p (R s))
    (hp_nonneg : ∀ a, 0 ≤ p a)
    (hp_sum : (∑ a : α, ENNReal.ofReal (p a)) = 1)
    (R : ι → α) :
    stoppingVectorPMF p w hw hp_nonneg hp_sum R = ENNReal.ofReal (w R) := by
  rw [stoppingVectorPMF, PMF.ofFintype_apply]

/-- The product PMF assigns each stopping vector the product of its coordinate masses.

This alternate pointwise specification unfolds the caller-provided vector
weight into the finite product of its coordinate real masses.

Layer: Model | Gap: Level 0 (finite product stopping-vector PMF product form)
Proof: combine `stoppingVectorPMF_apply` with the supplied vector-weight product
  identity.
Source: Mathlib probability mass functions and finite product APIs
Used in: nonconvex stochastic mirror descent finite weighted-sum expansions over
  independent randomized stopping vectors
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem stoppingVectorPMF_apply_eq_product
    {ι α : Type*} [DecidableEq ι] [Fintype ι] [Fintype α]
    (p : α → ℝ)
    (w : (ι → α) → ℝ)
    (hw : ∀ R, w R = ∏ s : ι, p (R s))
    (hp_nonneg : ∀ a, 0 ≤ p a)
    (hp_sum : (∑ a : α, ENNReal.ofReal (p a)) = 1)
    (R : ι → α) :
    stoppingVectorPMF p w hw hp_nonneg hp_sum R =
      ENNReal.ofReal (∏ s : ι, p (R s)) := by
  rw [stoppingVectorPMF_apply, hw R]

/-- The finite set of squared norm differences between two finitely indexed families.

For finite run-indexed empirical and exact vector families, this packages the
canonical image of `i ↦ ‖empirical i - exact i‖ ^ 2` as a finite set of real
validation-error values.

Layer: Model | Concept: Iterates
Proof: (definitional construction; finite image of the squared norm difference
  between paired run observables)
Source: Mathlib finite-set image API and normed additive group notation
Used in: nonconvex stochastic mirror descent validation-error maximum over
  independent runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def finiteRunErrorSqValues
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (empirical exact : ι → E) : Finset ℝ := by
  classical
  exact Finset.univ.image (fun i : ι => ‖empirical i - exact i‖ ^ 2)

/-- Membership in the finite squared-error set is exactly attainment by an index.

For finite run-indexed empirical and exact vector families, a real value belongs
to `finiteRunErrorSqValues empirical exact` iff it is the squared norm
difference at some run index.

Layer: Model | Gap: Level 0 (finite squared-error membership)
Proof: unfold `finiteRunErrorSqValues` and use Mathlib's `Finset.mem_image`
  simplification for the universal finite set.
Source: Mathlib finite-set image membership API for finitely indexed normed families
Used in: nonconvex stochastic mirror descent validation-error maximum over
  independent runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
@[simp]
theorem mem_finiteRunErrorSqValues
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (empirical exact : ι → E) (x : ℝ) :
    x ∈ finiteRunErrorSqValues empirical exact ↔
      ∃ i : ι, ‖empirical i - exact i‖ ^ 2 = x := by
  classical
  simp [finiteRunErrorSqValues]

/-- Selected output obtained by evaluating a run-wise output process at a
sample-dependent selected run.

This abstracts the paper object `\bar{x}^*`: after a validation rule chooses a
run from the sample point, the run-wise output is evaluated at that same sample.

Layer: Model | Concept: Iterates
Proof: (definitional construction; compose the run-wise output process with the selected-run map)
Source: Mathlib dependent function application and stochastic iterate notation
Used in: nonconvex stochastic mirror descent final selected output after empirical run validation
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def selectedOutput
    {Run Ω X : Type*}
    (runOutput : Run → Ω → X) (selectedRun : Ω → Run) (ω : Ω) : X :=
  runOutput (selectedRun ω) ω

/-- The selected-output wrapper unfolds to the run-wise output at the selected
run and the same sample point.

Layer: Model | Gap: Level 0 (selected output unfolding)
Proof: by rfl after unfolding `selectedOutput`.
Source: Mathlib dependent function application and stochastic iterate notation
Used in: nonconvex stochastic mirror descent final selected output after empirical run validation
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
@[simp]
theorem selectedOutput_apply
    {Run Ω X : Type*}
    (runOutput : Run → Ω → X) (selectedRun : Ω → Run) (ω : Ω) :
    selectedOutput runOutput selectedRun ω = runOutput (selectedRun ω) ω := by
  rfl

/-- Canonical minimizer selected from a finite nonempty family of ordered scores.

For a finite nonempty index type and any score into a linear order,
`finiteArgmin score` chooses an index whose score is no larger than every
other score.

Layer: Model | Concept: Objective
Proof: (definitional construction; `Classical.choose` applied to Mathlib's finite minimum existence theorem)
Source: Mathlib finite type lattice API for extrema of finite indexed families
Used in: nonconvex stochastic mirror descent selected run minimizing empirical projected-gradient norm over finitely many independent runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def finiteArgmin
    {ι α : Type*} [Finite ι] [Nonempty ι] [LinearOrder α]
    (score : ι → α) : ι :=
  Classical.choose (Finite.exists_min score)

/-- A finite nonempty family of scores in a linear order has a minimizing index.

This names the common finite-run selection step: from a finite nonempty index
type and an arbitrary ordered score, choose an index whose score is no larger
than every other indexed score.

Layer: Model | Gap: Level 0 (finite score minimizer existence)
Proof: this is exactly Mathlib's `Finite.exists_min` for finite nonempty types
  and linearly ordered score codomains.
Source: Mathlib finite type lattice API for extrema of finite indexed families
Used in: nonconvex stochastic mirror descent selected run minimizing empirical
  projected-gradient norm over finitely many independent runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem finite_exists_min_score
    {ι α : Type*} [Finite ι] [Nonempty ι] [LinearOrder α]
    (score : ι → α) :
    ∃ istar : ι, ∀ i : ι, score istar ≤ score i := by
  exact Finite.exists_min score

/-- The canonical finite argmin selector has minimal score.

For every candidate index, the score at `finiteArgmin score` is bounded above
by the score at that candidate.

Layer: Model | Gap: Level 0 (finite argmin selector specification)
Proof: project the universal minimality certificate from `Classical.choose_spec`
  for Mathlib's `Finite.exists_min`.
Source: Mathlib finite type lattice API for extrema of finite indexed families
Used in: nonconvex stochastic mirror descent selected run minimizing empirical projected-gradient norm over finitely many independent runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic mirror descent -/
theorem finiteArgmin_spec
    {ι α : Type*} [Finite ι] [Nonempty ι] [LinearOrder α]
    (score : ι → α) (i : ι) :
    score (finiteArgmin score) ≤ score i := by
  exact Classical.choose_spec (Finite.exists_min score) i

/-- The prox-oracle update generated by a time-indexed oracle average and step size.

For a state type `P`, oracle-value type `E`, and sample space `Ω`,
`proxOracleStep prox oracleAvg gamma k x omega` names the model-level update
`prox x (oracleAvg k x omega) (gamma k)`.

Layer: Model | Concept: Prox
Proof: (definitional construction; prox selector applied to a time-indexed oracle
  average and step-size schedule)
Source: Lan stochastic mirror descent prox-oracle update notation
Used in: randomized stochastic mirror descent mini-batch prox update
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
noncomputable def proxOracleStep
    {Ω P E : Type*}
    (prox : P → E → ℝ → P)
    (oracleAvg : ℕ → P → Ω → E)
    (gamma : ℕ → ℝ)
    (k : ℕ) (x : P) (omega : Ω) : P :=
  prox x (oracleAvg k x omega) (gamma k)

/-- The prox-oracle update unfolds to prox applied to the current oracle average.

This identity keeps algorithm-local step notation reducible to the selected
prox point at the mini-batch oracle value and the scheduled step size.

Layer: Model | Gap: Level 0 (prox-oracle step unfolding)
Proof: by rfl after unfolding `proxOracleStep`.
Source: Lan stochastic mirror descent prox-oracle update notation
Used in: randomized stochastic mirror descent mini-batch prox update
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
@[simp]
theorem proxOracleStep_apply
    {Ω P E : Type*}
    (prox : P → E → ℝ → P)
    (oracleAvg : ℕ → P → Ω → E)
    (gamma : ℕ → ℝ)
    (k : ℕ) (x : P) (omega : Ω) :
    proxOracleStep prox oracleAvg gamma k x omega =
      prox x (oracleAvg k x omega) (gamma k) := by
  rfl

/-- The constant half-Lipschitz stepsize schedule `k ↦ 1 / (2 * L)`.

This abstracts the paper convention of choosing the same inverse-Lipschitz
stepsize at every iteration, leaving the index type arbitrary.

Layer: Model | Concept: Iterates
Proof: (definitional construction; constant real-valued schedule over an
  arbitrary iteration index)
Source: Mathlib real field operations and Lan nonconvex stochastic mirror
  descent stepsize notation
Used in: nonconvex stochastic mirror descent optimization phase with constant
  half-Lipschitz inner stepsize
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/steps/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def halfLipschitzStepSizeSchedule {T : Type*} (L : ℝ) (_k : T) : ℝ :=
  1 / (2 * L)

/-- The constant half-Lipschitz stepsize schedule evaluates to `1 / (2 * L)`.

This is the definitional equation for the paper's constant inner-loop stepsize
schedule, stated with an arbitrary iteration index type.

Layer: Model | Gap: Level 0 (half-Lipschitz stepsize schedule unfolding)
Proof: by rfl after unfolding `halfLipschitzStepSizeSchedule`.
Source: Mathlib real field operations and Lan nonconvex stochastic mirror
  descent constant stepsize notation
Used in: nonconvex stochastic mirror descent optimization phase constant
  half-Lipschitz inner stepsize rewriting
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/steps/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem halfLipschitzStepSizeSchedule_eq {T : Type*} (L : ℝ) (k : T) :
    halfLipschitzStepSizeSchedule L k = 1 / (2 * L) := by
  rfl

/-- The half-Lipschitz stepsize `1 / (2 * L)` is positive when `L` is positive.

This isolates the scalar denominator positivity needed by the constant
stepsize choice used in the nonconvex stochastic mirror-descent inner loop.

Layer: Model | Gap: Level 0 (half-Lipschitz stepsize positivity)
Proof: multiply the positive Lipschitz constant by the positive scalar `2`,
  then use positivity of the reciprocal in the ordered real field.
Source: Mathlib ordered real field arithmetic APIs
Used in: nonconvex stochastic mirror descent optimization phase constant
  half-Lipschitz inner stepsize
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/steps/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem halfLipschitzStepSize_pos (L : ℝ) (hL_pos : 0 < L) :
    0 < 1 / (2 * L) := by
  exact one_div_pos.mpr (mul_pos (by norm_num : (0 : ℝ) < 2) hL_pos)

end SOptLib

namespace PMF

/-- Build a finite probability mass function from nonnegative real weights summing to one.

This wraps `PMF.ofFintype` for the common case where finite weights are first
specified as real numbers and then embedded into `ℝ≥0∞` with `ENNReal.ofReal`.

Layer: Model | Concept: Probability
Proof: (definitional construction; finite PMF from normalized real weights via `ENNReal.ofReal`)
Source: Mathlib probability mass functions and extended nonnegative real APIs
Used in: nonconvex stochastic mirror descent randomized stopping distribution
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def ofFintypeOfReal
    {α : Type*} [Fintype α]
    (p : α → ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a)
    (hp_sum : ∑ a, p a = 1) :
  PMF α :=
  PMF.ofFintype (fun a : α => ENNReal.ofReal (p a)) (by
    rw [← ENNReal.ofReal_one, ← hp_sum]
    exact (ENNReal.ofReal_sum_of_nonneg (fun a _ => hp_nonneg a)).symm)

/-- The finite PMF built from normalized real weights has mass `ENNReal.ofReal (p a)`.

Layer: Model | Gap: Level 0 (finite PMF real-weight evaluation)
Proof: unfold `ofFintypeOfReal` and use the `PMF.ofFintype_apply` simp rule.
Source: Mathlib probability mass functions and extended nonnegative real APIs
Used in: nonconvex stochastic mirror descent randomized stopping distribution
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic mirror descent -/
@[simp]
theorem ofFintypeOfReal_apply
    {α : Type*} [Fintype α]
    (p : α → ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a)
    (hp_sum : ∑ a, p a = 1)
    (a : α) :
    ofFintypeOfReal p hp_nonneg hp_sum a = ENNReal.ofReal (p a) := by
  rfl

end PMF

/-- State for a block-iterate recursion with a global iterate, block accumulators,
and per-block update counters.

The field `x` stores the current iterate, `s i` stores the auxiliary data
attached to block `i`, and `u i` stores the natural-number counter associated
with the most recent update window for block `i`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; bundled block-recursion state with global
  iterate, dependent block accumulators, and natural update counters)
Source: block-coordinate stochastic optimization iterate-state notation
Used in: stochastic block mirror descent recursion state for sampled block
  updates and incremental averaging
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
structure BlockIterateState (I : Type*) (E : Type*) (Block : I → Type*) where
  x : E
  s : ∀ i, Block i
  u : I → ℕ

/-- Lift a feasible one-block mirror prox selector to a feasible full-state update.

Given a feasible current state, a coordinate reader, a replacement map preserving feasibility,
and a block prox selector returning a feasible selected coordinate, `blockMirrorUpdate` splices
the selected block prox point into the full state and packages the resulting feasibility proof.

Layer: Model | Concept: Iterates
Proof: (definitional construction; subtype-valued coordinate replacement after a block prox
  selector)
Source: coordinate-update models for block mirror descent and Mathlib subtype APIs
Used in: stochastic block mirror descent full iterate update after sampling a block prox point
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic block mirror descent -/
def blockMirrorUpdate
    {ι State : Type*} {B G : ι → Type*}
    (X : Set State) (XBlock : ∀ i, Set (B i))
    (coord : ∀ i, State → B i)
    (replace : ∀ i, State → B i → State)
    (replace_mem :
      ∀ i (x : State) (u : B i), x ∈ X → u ∈ XBlock i → replace i x u ∈ X)
    (coord_mem : ∀ i (x : State), x ∈ X → coord i x ∈ XBlock i)
    (blockProx :
      ∀ i, {z : B i // z ∈ XBlock i} → G i → ℝ → {z : B i // z ∈ XBlock i})
    (i : ι) (x : {x : State // x ∈ X}) (g : G i) (γ : ℝ) :
    {x : State // x ∈ X} :=
  let u := blockProx i ⟨coord i x.1, coord_mem i x.1 x.2⟩ g γ
  Subtype.map
    (fun y : State => replace i y u.1)
    (fun y hy => replace_mem i y u.1 hy u.2)
    x

/-- The underlying state of `blockMirrorUpdate` is the replacement of the current state by
the selected feasible block prox point.

Layer: Model | Gap: Level 0 (block mirror update unfolding)
Proof: by rfl after unfolding `blockMirrorUpdate`.
Source: Mathlib subtype projection and definitional unfolding APIs
Used in: stochastic block mirror descent readability for the full iterate update equation
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic block mirror descent -/
@[simp]
theorem blockMirrorUpdate_coe
    {ι State : Type*} {B G : ι → Type*}
    (X : Set State) (XBlock : ∀ i, Set (B i))
    (coord : ∀ i, State → B i)
    (replace : ∀ i, State → B i → State)
    (replace_mem :
      ∀ i (x : State) (u : B i), x ∈ X → u ∈ XBlock i → replace i x u ∈ X)
    (coord_mem : ∀ i (x : State), x ∈ X → coord i x ∈ XBlock i)
    (blockProx :
      ∀ i, {z : B i // z ∈ XBlock i} → G i → ℝ → {z : B i // z ∈ XBlock i})
    (i : ι) (x : {x : State // x ∈ X}) (g : G i) (γ : ℝ) :
    (blockMirrorUpdate X XBlock coord replace replace_mem coord_mem blockProx i x g γ).1 =
      replace i x.1
        (blockProx i ⟨coord i x.1, coord_mem i x.1 x.2⟩ g γ).1 := by
  rfl

/-- Non-selected coordinates of a full-state block mirror update are unchanged.

If the replacement map leaves every off coordinate unchanged, then the staged
`blockMirrorUpdate` obtained by inserting the selected block prox point has the same
off-coordinate preservation property.

Layer: Model | Gap: Level 0 (block mirror update off-coordinate preservation)
Proof: unfold the underlying state of `blockMirrorUpdate`, then apply the
  off-coordinate preservation law for the replacement map to the selected block.
Source: Mathlib subtype projection APIs and coordinate-update model laws
Used in: stochastic block mirror descent preservation of non-sampled blocks after
  the sampled block prox step
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic block mirror descent -/
theorem blockMirrorUpdate_other
    {ι State : Type*} {B G : ι → Type*}
    (X : Set State) (XBlock : ∀ i, Set (B i))
    (coord : ∀ i, State → B i)
    (replace : ∀ i, State → B i → State)
    (replace_mem :
      ∀ i (x : State) (u : B i), x ∈ X → u ∈ XBlock i → replace i x u ∈ X)
    (coord_mem : ∀ i (x : State), x ∈ X → coord i x ∈ XBlock i)
    (replace_other :
      ∀ i j (x : State) (u : B i), j ≠ i → coord j (replace i x u) = coord j x)
    (blockProx :
      ∀ i, {z : B i // z ∈ XBlock i} → G i → ℝ → {z : B i // z ∈ XBlock i})
    (i j : ι) (x : {x : State // x ∈ X}) (g : G i) (γ : ℝ) (hji : j ≠ i) :
    coord j (blockMirrorUpdate X XBlock coord replace replace_mem coord_mem blockProx i x g γ).1 =
      coord j x.1 := by
  rw [blockMirrorUpdate_coe]
  exact replace_other i j x.1
    (blockProx i ⟨coord i x.1, coord_mem i x.1 x.2⟩ g γ).1 hji

/-- The selected coordinate of a full-state block mirror update is the selected block output.

If the replacement map recovers the inserted value at the selected coordinate, then the
staged `blockMirrorUpdate` obtained by inserting the selected block prox point has that
prox point as its selected coordinate.

Layer: Model | Gap: Level 0 (block mirror update selected-coordinate recovery)
Proof: unfold the underlying state of `blockMirrorUpdate`, then apply the
  selected-coordinate recovery law for the replacement map to the selected block.
Source: Mathlib subtype projection APIs and coordinate-update model laws
Used in: stochastic block mirror descent sampled-coordinate identification after the
  sampled block prox step
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic block mirror descent -/
theorem blockMirrorUpdate_selected
    {ι State : Type*} {B G : ι → Type*}
    (X : Set State) (XBlock : ∀ i, Set (B i))
    (coord : ∀ i, State → B i)
    (replace : ∀ i, State → B i → State)
    (replace_mem :
      ∀ i (x : State) (u : B i), x ∈ X → u ∈ XBlock i → replace i x u ∈ X)
    (coord_mem : ∀ i (x : State), x ∈ X → coord i x ∈ XBlock i)
    (replace_selected :
      ∀ i (x : State) (u : B i), coord i (replace i x u) = u)
    (blockProx :
      ∀ i, {z : B i // z ∈ XBlock i} → G i → ℝ → {z : B i // z ∈ XBlock i})
    (i : ι) (x : {x : State // x ∈ X}) (g : G i) (γ : ℝ) :
    coord i (blockMirrorUpdate X XBlock coord replace replace_mem coord_mem blockProx i x g γ).1 =
      (blockProx i ⟨coord i x.1, coord_mem i x.1 x.2⟩ g γ).1 := by
  simpa [blockMirrorUpdate_coe] using
    replace_selected i x.1
      (blockProx i ⟨coord i x.1, coord_mem i x.1 x.2⟩ g γ).1

/-- The selected coordinate of a full-state block update inherits the raw block argmin proof.

If a feasible block selector minimizes a block objective at the current block coordinate, then
the selected coordinate of the full-state update obtained by splicing that selector is the
same minimizer, as a subtype-valued point of the selected block carrier.

Layer: Model | Gap: Level 1 (selected-coordinate block argmin transport)
Proof: identify the selected full-state coordinate with the raw block selector by
  `blockMirrorUpdate_selected`, then use subtype extensionality to transport the supplied
  `IsMinOn` certificate to the displayed selected-coordinate point.
Source: Mathlib subtype equality and `IsMinOn` APIs for coordinate-update models
Used in: stochastic block mirror descent selected-coordinate prox optimality after the
  sampled block update
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic block mirror descent -/
theorem blockMirrorUpdate_selected_isMinOn
    {ι State : Type*} {B G : ι → Type*}
    (X : Set State) (XBlock : ∀ i, Set (B i))
    (coord : ∀ i, State → B i)
    (replace : ∀ i, State → B i → State)
    (replace_mem :
      ∀ i (x : State) (u : B i), x ∈ X → u ∈ XBlock i → replace i x u ∈ X)
    (coord_mem : ∀ i (x : State), x ∈ X → coord i x ∈ XBlock i)
    (replace_selected :
      ∀ i (x : State) (u : B i), coord i (replace i x u) = u)
    (blockProx :
      ∀ i, {z : B i // z ∈ XBlock i} → G i → ℝ → {z : B i // z ∈ XBlock i})
    (blockObjective :
      ∀ i, {z : B i // z ∈ XBlock i} → G i → ℝ →
        {u : B i // u ∈ XBlock i} → ℝ)
    (i : ι) (x : {x : State // x ∈ X}) (g : G i) (γ : ℝ)
    (hmin :
      IsMinOn
        (blockObjective i ⟨coord i x.1, coord_mem i x.1 x.2⟩ g γ)
        Set.univ
        (blockProx i ⟨coord i x.1, coord_mem i x.1 x.2⟩ g γ)) :
    IsMinOn
      (blockObjective i ⟨coord i x.1, coord_mem i x.1 x.2⟩ g γ)
      Set.univ
      ⟨coord i (blockMirrorUpdate X XBlock coord replace replace_mem coord_mem
          blockProx i x g γ).1,
        by
          rw [blockMirrorUpdate_selected X XBlock coord replace replace_mem coord_mem
            replace_selected blockProx i x g γ]
          exact (blockProx i ⟨coord i x.1, coord_mem i x.1 x.2⟩ g γ).2⟩ := by
  let z : {z : B i // z ∈ XBlock i} := ⟨coord i x.1, coord_mem i x.1 x.2⟩
  let y : {u : B i // u ∈ XBlock i} := blockProx i z g γ
  have hsel :
      coord i
          (blockMirrorUpdate X XBlock coord replace replace_mem coord_mem
            blockProx i x g γ).1 = y.1 := by
    simpa [z, y] using
      blockMirrorUpdate_selected X XBlock coord replace replace_mem coord_mem
        replace_selected blockProx i x g γ
  have hpoint :
      (⟨coord i
          (blockMirrorUpdate X XBlock coord replace replace_mem coord_mem
            blockProx i x g γ).1,
        by
          rw [hsel]
          exact y.2⟩ : {u : B i // u ∈ XBlock i}) = y := by
    exact Subtype.ext hsel
  rw [hpoint]
  simpa [z, y] using hmin

/-- Replace one dependent coordinate and assemble the resulting product state.

For a dependent coordinate family `B`, an assembly map from coordinates into a
state type `X`, and coordinate readers from `X`, this is the canonical operation
that keeps all coordinates from `x` except coordinate `i`, where it inserts `u`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; dependent coordinate update followed by an
  abstract product-state assembly map)
Source: Mathlib dependent-function update API for product-coordinate models
Used in: stochastic block mirror descent product iterate rebuilt after a sampled
  one-block prox update
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
def dependentProductCoordinateReplacement
    {ι X : Type*} [DecidableEq ι] {B : ι → Type*}
    (assemble : (∀ j, B j) → X) (coord : ∀ j, X → B j)
    (x : X) (i : ι) (u : B i) : X :=
  assemble (Function.update (fun j => coord j x) i u)

/-- The selected coordinate of a dependent product-coordinate replacement is the inserted value.

Layer: Model | Gap: Level 0 (dependent product-coordinate replacement selected coordinate)
Proof: unfold the replacement constructor, apply the coordinate-after-assembly
  law, and reduce the selected coordinate with `Function.update_self`.
Source: Mathlib dependent-function update API for product-coordinate models
Used in: stochastic block mirror descent feasibility of the updated sampled block
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
@[simp]
theorem dependentProductCoordinateReplacement_selected
    {ι X : Type*} [DecidableEq ι] {B : ι → Type*}
    (assemble : (∀ j, B j) → X) (coord : ∀ j, X → B j)
    (hcoord_assemble : ∀ y j, coord j (assemble y) = y j)
    (x : X) (i : ι) (u : B i) :
    coord i (dependentProductCoordinateReplacement assemble coord x i u) = u := by
  simp [dependentProductCoordinateReplacement, hcoord_assemble]

/-- A non-selected coordinate of a dependent product-coordinate replacement is unchanged.

Layer: Model | Gap: Level 0 (dependent product-coordinate replacement off coordinate)
Proof: unfold the replacement constructor, apply the coordinate-after-assembly
  law, and reduce the off coordinate with `Function.update_of_ne`.
Source: Mathlib dependent-function update API for product-coordinate models
Used in: stochastic block mirror descent preservation of non-sampled blocks
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
@[simp]
theorem dependentProductCoordinateReplacement_other
    {ι X : Type*} [DecidableEq ι] {B : ι → Type*}
    (assemble : (∀ j, B j) → X) (coord : ∀ j, X → B j)
    (hcoord_assemble : ∀ y j, coord j (assemble y) = y j)
    (x : X) (i j : ι) (u : B i) (hji : j ≠ i) :
    coord j (dependentProductCoordinateReplacement assemble coord x i u) = coord j x := by
  simp [dependentProductCoordinateReplacement, hcoord_assemble, Function.update_of_ne hji]

/-- Replacing one dependent product coordinate by a feasible value preserves product feasibility.

For an abstract assembled product state with coordinate readers, if every coordinate of `x`
belongs to its block carrier and the inserted coordinate belongs to the selected carrier, then
the assembled one-coordinate replacement again belongs to the pointwise product carrier.

Layer: Model | Gap: Level 0 (dependent product-coordinate feasibility preservation)
Proof: split on whether the queried coordinate is the updated coordinate; use the selected
  coordinate law in the updated case and the off-coordinate law otherwise.
Source: Mathlib dependent-function update API and Set membership for product-coordinate models
Used in: stochastic block mirror descent feasibility of the full iterate after a sampled
  one-block prox update
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic block mirror descent -/
theorem dependentProductCoordinateReplacement_mem
    {ι X : Type*} [DecidableEq ι] {B : ι → Type*}
    (assemble : (∀ j, B j) → X) (coord : ∀ j, X → B j)
    (hcoord_assemble : ∀ y j, coord j (assemble y) = y j)
    (XBlock : ∀ j, Set (B j))
    (x : X) (i : ι) (u : B i)
    (hx : ∀ j, coord j x ∈ XBlock j) (hu : u ∈ XBlock i) :
    ∀ j, coord j (dependentProductCoordinateReplacement assemble coord x i u) ∈ XBlock j := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa using
      (show coord i (dependentProductCoordinateReplacement assemble coord x i u) ∈ XBlock i from
        by
          rw [dependentProductCoordinateReplacement_selected assemble coord hcoord_assemble x i u]
          exact hu)
  · rw [dependentProductCoordinateReplacement_other assemble coord hcoord_assemble x i j u hji]
    exact hx j

/-- Feasible one-coordinate replacement is measurable after product reassembly.

If each coordinate reader is measurable and the product-coordinate assembly map
is measurable, then replacing a fixed coordinate by a feasible block value,
reassembling the full state, and packaging the feasibility proof is a
measurable map on the product of feasible subtypes.

Layer: Model | Gap: Level 1 (feasible product-coordinate replacement measurability)
Proof: prove measurability of the underlying state by composing the measurable
  assembly map with a coordinatewise measurable `Function.update`; close the
  subtype-valued statement with `Measurable.subtype_mk`.
Source: Mathlib measure-theory APIs for dependent product measurable spaces and subtypes
Used in: stochastic block mirror descent fixed-block feasible splice after a
  one-block prox update
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem feasibleCoordinateReplacement_measurable
    {ι State : Type*} [DecidableEq ι]
    {B : ι → Type*} [∀ j, MeasurableSpace (B j)] [MeasurableSpace State]
    (assemble : (∀ j, B j) → State)
    (coord : ∀ j, State → B j)
    (X : Set State) (XBlock : ∀ j, Set (B j))
    (hassemble : Measurable assemble)
    (hcoord : ∀ j, Measurable (coord j))
    (replace_mem :
      ∀ i (x : State) (u : B i), x ∈ X → u ∈ XBlock i →
        assemble (Function.update (fun j => coord j x) i u) ∈ X)
    (i : ι) :
    Measurable
      (fun p : {x : State // x ∈ X} × {u : B i // u ∈ XBlock i} =>
        Subtype.map
          (fun y : State => assemble (Function.update (fun j => coord j y) i p.2.1))
          (fun y hy => replace_mem i y p.2.1 hy p.2.2)
          p.1) := by
  classical
  refine Measurable.subtype_mk ?_
  change Measurable
    (fun p : {x : State // x ∈ X} × {u : B i // u ∈ XBlock i} =>
      assemble (Function.update (fun j => coord j p.1.1) i p.2.1))
  refine hassemble.comp ?_
  refine measurable_pi_lambda _ ?_
  intro j
  by_cases hji : j = i
  · subst j
    simpa using
      (measurable_subtype_coe.comp measurable_snd :
        Measurable
          (fun p : {x : State // x ∈ X} × {u : B i // u ∈ XBlock i} =>
            (p.2 : B i)))
  · simpa [Function.update_of_ne hji] using
      ((hcoord j).comp (measurable_subtype_coe.comp measurable_fst) :
        Measurable
          (fun p : {x : State // x ∈ X} × {u : B i // u ∈ XBlock i} =>
            coord j (p.1 : State)))

/-- Feasible one-coordinate replacement is measurable after product reassembly.

If each coordinate reader is measurable and the product-coordinate assembly map
is measurable, then replacing a fixed coordinate by a feasible block value,
reassembling the full state, and packaging the feasibility proof is a
measurable map on the product of feasible subtypes.

Layer: Model | Gap: Level 1 (feasible product-coordinate replacement measurability)
Proof: prove measurability of the underlying state by composing the measurable
  assembly map with a coordinatewise measurable `Function.update`; close the
  subtype-valued statement with `Measurable.subtype_mk`.
Source: Mathlib measure-theory APIs for dependent product measurable spaces and subtypes
Used in: stochastic block mirror descent fixed-block feasible splice after a
  one-block prox update
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem feasible_coordinate_replacement_measurable
    {ι State : Type*} [DecidableEq ι]
    {B : ι → Type*} [∀ j, MeasurableSpace (B j)] [MeasurableSpace State]
    (assemble : (∀ j, B j) → State)
    (coord : ∀ j, State → B j)
    (X : Set State) (i : ι) (X_i : Set (B i))
    (hassemble : Measurable assemble)
    (hcoord : ∀ j, Measurable (fun x : {x : State // x ∈ X} => coord j x.1))
    (replace_mem :
      ∀ (x : State) (u : B i), x ∈ X → u ∈ X_i →
        assemble (Function.update (fun j => coord j x) i u) ∈ X) :
    Measurable
      (fun p : {x : State // x ∈ X} × {u : B i // u ∈ X_i} =>
        Subtype.map
          (fun y : State => assemble (Function.update (fun j => coord j y) i p.2.1))
          (fun y hy => replace_mem y p.2.1 hy p.2.2)
          p.1) := by
  classical
  refine Measurable.subtype_mk ?_
  change Measurable
    (fun p : {x : State // x ∈ X} × {u : B i // u ∈ X_i} =>
      assemble (Function.update (fun j => coord j p.1.1) i p.2.1))
  refine hassemble.comp ?_
  refine measurable_pi_lambda _ ?_
  intro j
  by_cases hji : j = i
  · subst j
    simpa using
      (measurable_subtype_coe.comp measurable_snd :
        Measurable
          (fun p : {x : State // x ∈ X} × {u : B i // u ∈ X_i} =>
            (p.2 : B i)))
  · simpa [Function.update_of_ne hji] using
      ((hcoord j).comp measurable_fst :
        Measurable
          (fun p : {x : State // x ∈ X} × {u : B i // u ∈ X_i} =>
            coord j (p.1 : State)))

/-- Recursive sampled-block mirror-descent state process with incremental averaging.

Starting from an initial state and per-block zero accumulators, the successor
step samples a block, evaluates the block oracle at the previous state, applies
the supplied full-state block update, and updates only the sampled block's
accumulator and counter. The accumulator increment uses the window
`∑ k in Icc (u_i) t, θ k` multiplying the selected coordinate of the previous
state.

Layer: Model | Concept: Iterates
Proof: (definitional construction; primitive recursion with sampled-block
  oracle, state update, finite-window accumulator weight, and block counter)
Source: block-coordinate stochastic mirror descent recursion and Mathlib finite
  interval sums
Used in: stochastic block mirror descent sampled prox recursion and incremental
  output averaging
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
noncomputable def stochasticBlockMirrorDescentProcess
    {Ω I State : Type*} {Block : I → Type*} [DecidableEq I]
    (instAdd : ∀ i, Add (Block i))
    (instSMul : ∀ i, SMul ℝ (Block i))
    (init : State)
    (zeroBlock : ∀ i, Block i)
    (sampleBlock : ℕ → Ω → I)
    (oracle : ∀ i, ℕ → State → Ω → Block i)
    (blockCoord : ∀ i, State → Block i)
    (blockUpdate : ∀ i, ℕ → State → Block i → ℝ → State)
    (η θ : ℕ → ℝ) :
    ℕ → Ω → BlockIterateState I State Block
  | 0 => fun _ =>
      { x := init
        s := zeroBlock
        u := fun _ => 0 }
  | t + 1 => fun ω =>
      let prev :=
        stochasticBlockMirrorDescentProcess instAdd instSMul init zeroBlock
          sampleBlock oracle blockCoord blockUpdate η θ t ω
      let i_t := sampleBlock t ω
      letI := instAdd i_t
      letI := instSMul i_t
      let g_t := oracle i_t t prev.x ω
      let xNext := blockUpdate i_t t prev.x g_t (η t)
      let weight := Finset.sum (Finset.Icc (prev.u i_t) t) θ
      { x := xNext
        s := Function.update prev.s i_t (prev.s i_t + weight • blockCoord i_t prev.x)
        u := Function.update prev.u i_t (t + 1) }

namespace SOptLib

/-- Positive-time view of a zero-based step-size schedule.

For a recursive process whose internal counter starts at zero while the
mathematical statement indexes step sizes by positive natural times,
`positiveTimeStepSize η k` exposes the step size at the predecessor of `k`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; predecessor lookup of a zero-based schedule
  through a positive natural-number time index)
Source: stochastic approximation step-size notation and Mathlib natural-number
  subtraction over subtype indices
Used in: stochastic block mirror descent positive-time weighting by step sizes
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
def positiveTimeStepSize
    {R : Type*}
    (η : ℕ → R) (k : {n : ℕ // 1 ≤ n}) : R :=
  η (k.1 - 1)

/-- The positive-time step-size view evaluates the zero-based schedule at `k - 1`.

Layer: Model | Gap: Level 0 (positive-time step-size unfolding)
Proof: by rfl after unfolding `positiveTimeStepSize`.
Source: Mathlib natural-number subtraction and subtype projection APIs
Used in: stochastic block mirror descent rewriting of positive-time step sizes
  back to the recursive zero-based schedule
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
@[simp]
theorem positiveTimeStepSize_eq
    {R : Type*}
    (η : ℕ → R) (k : {n : ℕ // 1 ≤ n}) :
    positiveTimeStepSize η k = η (k.1 - 1) := by
  rfl

/-- A zero-based output-weight schedule that agrees with the step-size schedule
also agrees with the positive-time step-size view.

For algorithms whose recursive process is zero-based while the paper output
window is indexed by positive natural times, this transports the schedule
identity `theta_t = eta_t` to the one-based statement `theta_{k-1} = eta_k`.

Layer: Model | Gap: Level 0 (positive-time weight and step-size bridge)
Proof: unfold the positive-time step-size view to the predecessor lookup, then
  apply the pointwise zero-based equality hypothesis at that predecessor.
Source: Mathlib subtype indexing and natural-number predecessor APIs for
  stochastic approximation schedules
Used in: stochastic block mirror descent rewriting positive-time output weights
  into step-size weights in the weighted gap bound
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem positiveTimeWeight_eq_stepSize
    {R : Type*}
    (eta theta : ℕ → R)
    (h_theta_eq_eta : ∀ t, theta t = eta t)
    (k : {n : ℕ // 1 ≤ n}) :
    theta (k.1 - 1) = positiveTimeStepSize eta k := by
  rw [positiveTimeStepSize_eq]
  exact h_theta_eq_eta (k.1 - 1)

/-- The positive-time view preserves pointwise nonnegativity of a zero-based
averaging-weight schedule.

For algorithms whose recursive state is indexed from zero but whose output
window is indexed by positive natural times, this turns `0 <= theta_t` into
the one-based statement for the predecessor-indexed weight.

Layer: Model | Gap: Level 0 (positive-time weight nonnegativity)
Proof: unfold the positive-time schedule view to the predecessor lookup, then
  apply the pointwise nonnegativity hypothesis at that predecessor.
Source: Mathlib ordered-type APIs and natural-number predecessor indexing for
  stochastic approximation schedules
Used in: stochastic block mirror descent normalized weighted output averaging
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem positiveTimeWeight_nonneg
    {R : Type*} [Preorder R] [Zero R]
    (theta : ℕ → R)
    (htheta_nonneg : ∀ t, 0 ≤ theta t)
    (k : {n : ℕ // 1 ≤ n}) :
    0 ≤ positiveTimeStepSize theta k := by
  simpa [positiveTimeStepSize] using htheta_nonneg (k.1 - 1)

/-- Public one-based view of a zero-based stochastic coordinate counter.

For algorithms whose recursive state stores a zero-based natural counter for each
coordinate, `oneBasedCounter uInternal t ω i` exposes the paper-facing counter
obtained by adding one at time `t`, sample path `ω`, and coordinate `i`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; pointwise successor view of a zero-based
  per-coordinate stochastic counter)
Source: stochastic approximation iterate-counter notation and Mathlib
  natural-number successor arithmetic
Used in: stochastic block mirror descent paper-facing block averaging counter
  extracted from the recursive sampled-block state
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
def oneBasedCounter
    {T Ω ι : Type*}
    (uInternal : T → Ω → ι → ℕ)
    (t : T) (ω : Ω) (i : ι) : ℕ :=
  uInternal t ω i + 1

/-- The one-based public counter is the internal zero-based counter plus one.

Layer: Model | Gap: Level 0 (one-based counter unfolding)
Proof: by rfl after unfolding `oneBasedCounter`.
Source: Mathlib natural-number arithmetic and Pi-function application APIs
Used in: stochastic block mirror descent rewriting of the paper-facing block
  averaging counter back to the recursive sampled-block state counter
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
@[simp]
theorem oneBasedCounter_eq
    {T Ω ι : Type*}
    (uInternal : T → Ω → ι → ℕ)
    (t : T) (ω : Ω) (i : ι) :
    oneBasedCounter uInternal t ω i = uInternal t ω i + 1 := by
  rfl

/-- A one-based coordinate counter initialized from a zero raw counter starts at one.

If the internal zero-based counter is initialized to `0` at recursive time `0`,
then the public one-based counter view is initialized to `1` at the same sample
path and coordinate.

Layer: Model | Gap: Level 0 (one-based counter initialization)
Proof: unfold the one-based counter view, rewrite by the pointwise raw-counter
  initialization hypothesis, and normalize natural-number arithmetic.
Source: stochastic approximation iterate-counter notation and Mathlib
  natural-number successor arithmetic
Used in: stochastic block mirror descent initialization of the paper-facing
  block averaging counter
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem oneBasedCounter_init
    {Ω ι : Type*}
    (uInternal : ℕ → Ω → ι → ℕ)
    (ω : Ω) (i : ι)
    (h_init : uInternal 0 ω i = 0) :
    oneBasedCounter uInternal 0 ω i = 1 := by
  simp [oneBasedCounter, h_init]

/-- A one-based coordinate counter is unchanged away from a selected raw update.

If the raw zero-based counter at `next t` is obtained from its value at `t` by
updating only the selected coordinate, then the public one-based counter agrees
with its previous value at every non-selected coordinate.

Layer: Model | Gap: Level 0 (one-based counter off-coordinate update)
Proof: unfold the one-based counter view, rewrite the raw pointwise update law,
  and reduce the non-selected coordinate with `Function.update` arithmetic.
Source: Mathlib dependent-function update API and natural-number successor
  arithmetic
Used in: stochastic block mirror descent preservation of non-sampled
  paper-facing block averaging counters
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem oneBasedCounter_update_other
    {T Ω ι : Type*} [DecidableEq ι]
    (uInternal : T → Ω → ι → ℕ)
    (selected : T → Ω → ι)
    {next : T → T} {t : T} {ω : Ω} {j : ι} {updatedValue : ℕ}
    (h_update :
      uInternal (next t) ω =
        Function.update (uInternal t ω) (selected t ω) updatedValue)
    (hji : j ≠ selected t ω) :
    oneBasedCounter uInternal (next t) ω j = oneBasedCounter uInternal t ω j := by
  simp [oneBasedCounter, h_update, Function.update, hji]

/-- A one-based coordinate counter records the inserted value at a selected raw update.

If the raw zero-based counter at `next t` is obtained from its value at `t` by
updating the selected coordinate to `updatedValue`, then the public one-based
counter at that selected coordinate is `updatedValue + 1`.

Layer: Model | Gap: Level 0 (one-based counter selected-coordinate update)
Proof: unfold the one-based counter view, rewrite the raw pointwise update law,
  and reduce the selected coordinate with `Function.update` arithmetic.
Source: Mathlib dependent-function update API and natural-number successor
  arithmetic
Used in: stochastic block mirror descent sampled block averaging counter update
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem oneBasedCounter_update_selected
    {T Ω ι : Type*} [DecidableEq ι]
    (uInternal : T → Ω → ι → ℕ)
    (selected : T → Ω → ι)
    {next : T → T} {t : T} {ω : Ω} {updatedValue : ℕ}
    (h_update :
      uInternal (next t) ω =
        Function.update (uInternal t ω) (selected t ω) updatedValue) :
    oneBasedCounter uInternal (next t) ω (selected t ω) = updatedValue + 1 := by
  simp [oneBasedCounter, h_update]

/-- Ambient value of a finite normalized weighted output average.

For a window selector `times`, raw weights `weight`, sample-dependent iterates
`x`, and explicit normalizer `Wsum`, this is the pointwise value
`(Wsum w)⁻¹ • ∑ t in times w, weight t • x t ω`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; explicit-denominator finite weighted
  average of stochastic iterates)
Source: Mathlib finite sums and real module scalar multiplication APIs
Used in: stochastic block mirror descent ambient weighted-output value before
  applying feasibility and Jensen-style weighted-average lemmas
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
noncomputable def weightedAverageOutputValue
    {Ω T W E : Type*} [AddCommGroup E] [Module ℝ E]
    (times : W → Finset T)
    (weight : T → ℝ)
    (x : T → Ω → E)
    (Wsum : W → ℝ)
    (w : W) (ω : Ω) : E :=
  (Wsum w)⁻¹ • Finset.sum (times w) (fun t => weight t • x t ω)

/-- The ambient weighted-output value unfolds to its normalized finite-sum formula.

Layer: Model | Gap: Level 0 (weighted output value unfolding)
Proof: by rfl after unfolding `weightedAverageOutputValue`.
Source: Mathlib finite sums and real module scalar multiplication APIs
Used in: stochastic block mirror descent rewriting the named output value to
  the finite weighted sum required by convexity and telescope bounds
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
@[simp]
theorem weightedAverageOutputValue_def
    {Ω T W E : Type*} [AddCommGroup E] [Module ℝ E]
    (times : W → Finset T)
    (weight : T → ℝ)
    (x : T → Ω → E)
    (Wsum : W → ℝ)
    (w : W) (ω : Ω) :
    weightedAverageOutputValue times weight x Wsum w ω =
      (Wsum w)⁻¹ • Finset.sum (times w) (fun t => weight t • x t ω) := by
  rfl

/-- Realization-side parameter regime for a conditional-gradient path.

The contract packages the three scalar side conditions that often sit between
a paper's displayed conditional-gradient formulas and the proof objects that
Lean must build: a nonzero diameter denominator, a stepsize small enough for an
affine update to be a convex combination, and a nonempty finite inner window.

Layer: Model | Concept: Iterates
Proof: (definitional construction; bundled scalar side conditions for a
  conditional-gradient realization)
Source: Frank-Wolfe conditional-gradient parameter regimes and finite
  inner-loop maxima
Used in: stochastic nonconvex conditional-gradient realization of displayed
  stepsize, convex-combination update, and inner epoch maximum
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
structure ConditionalGradientRealizationContract
    (D : ℝ) (α : 0 < D → ℝ) (T : ℕ) : Prop where
  /-- The displayed diameter denominator is nonzero. -/
  nonzeroDiameter : 0 < D
  /-- The realized conditional-gradient stepsize is at most one. -/
  alpha_le_one : α nonzeroDiameter ≤ 1
  /-- The displayed inner maximum window beginning at index `2` is nonempty. -/
  two_le_T : 2 ≤ T

/-- Boundary conditions for a weighted epoch-output construction.

The contract packages the scalar facts usually needed before an epoch-indexed
stochastic-optimization proof can use a normalized weighted output, affine
updates with weights as stepsizes, a maximum over the inner window `{2, ..., T}`,
and a recursive mini-batch whose size dominates the epoch length.

Layer: Model | Concept: Iterates
Proof: (structure) the fields bundle the independent scalar side conditions for
  finite weighted epoch-output realizations.
Source: finite weighted-output windows and epoch decompositions in stochastic
  first-order optimization
Used in: stochastic nonconvex conditional-gradient weighted output law and
  epoch-window domain boundary
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/key_lemmas/2/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
structure WeightedEpochOutputBoundary
    (weightSum : ℝ) (weight : ℕ → ℝ) (N T batch : ℕ) : Prop where
  /-- Positivity of the normalizer for the weighted output law. -/
  outputNormalizerPositive : 0 < weightSum
  /-- The output/update weights are at most one on the output window. -/
  weight_le_one : ∀ k, k ∈ Finset.Icc 1 N → weight k ≤ 1
  /-- The inner epoch window `{2, ..., T}` is nonempty. -/
  two_le_T : 2 ≤ T
  /-- The mini-batch size dominates the epoch length. -/
  epoch_le_batch : T ≤ batch

/-- Active within-epoch coordinates whose global iteration index remains in the run horizon.

For an epoch length `T`, a total output horizon `N`, and an encoder
`globalIndex s j` from epoch coordinates to global iteration indices, this
finite set records the coordinates `j ∈ {1, ..., T}` still generated before the
run stops.

Layer: Model | Concept: Iterates
Proof: (definitional construction; finite epoch window filtered by a global
  horizon predicate)
Source: Mathlib finite intervals and filtered finset APIs
Used in: stochastic variance-reduced conditional-gradient partial final epoch
  indexing
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
def activeEpochSteps
    (T N : ℕ) (globalIndex : ℕ → ℕ → ℕ) (s : ℕ) : Finset ℕ :=
  (Finset.Icc 1 T).filter (fun j => globalIndex s j ≤ N)

/-- Membership in the active epoch-coordinate window.

Layer: Model | Gap: Level 0 (active epoch-window membership)
Proof: by simplification after unfolding `activeEpochSteps` and the filtered
  finite interval membership predicate.
Source: Mathlib finite intervals and filtered finset membership APIs
Used in: stochastic variance-reduced conditional-gradient partial final epoch
  indexing
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
@[simp]
theorem mem_activeEpochSteps
    {T N : ℕ} {globalIndex : ℕ → ℕ → ℕ} {s j : ℕ} :
    j ∈ activeEpochSteps T N globalIndex s ↔
      j ∈ Finset.Icc 1 T ∧ globalIndex s j ≤ N := by
  simp [activeEpochSteps]

/-- Active epoch coordinates lie in the underlying epoch interval.

Layer: Model | Gap: Level 0 (active epoch-coordinate bounds)
Proof: project the finite-interval component from the active-window membership
  characterization and convert it with `Finset.mem_Icc`.
Source: Mathlib finite intervals and conjunction projection APIs
Used in: stochastic variance-reduced conditional-gradient within-epoch
  recurrence bounds
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem activeEpochSteps_mem_epoch
    {T N : ℕ} {globalIndex : ℕ → ℕ → ℕ} {s j : ℕ}
    (hj : j ∈ activeEpochSteps T N globalIndex s) :
    1 ≤ j ∧ j ≤ T := by
  exact Finset.mem_Icc.mp ((mem_activeEpochSteps.mp hj).1)

/-- Active epoch coordinates have global indices bounded by the run horizon.

Layer: Model | Gap: Level 0 (active epoch global-index bound)
Proof: project the global-horizon component from the active-window membership
  characterization.
Source: Mathlib filtered finset membership APIs
Used in: stochastic variance-reduced conditional-gradient one-step bounds over
  the generated run window
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem activeEpochSteps_globalIndex_le
    {T N : ℕ} {globalIndex : ℕ → ℕ → ℕ} {s j : ℕ}
    (hj : j ∈ activeEpochSteps T N globalIndex s) :
    globalIndex s j ≤ N :=
  (mem_activeEpochSteps.mp hj).2

/-- A nonzero-diameter branch gives a positive interval output denominator.

For a diameter-dependent realized stepsize schedule, once the realization
caller supplies the nonzero-diameter branch and the schedule is positive on the
nonempty output window `{1, ..., N}`, the normalizing denominator for the
randomized output law is strictly positive.

Layer: Model | Gap: Level 1 (conditional-gradient output denominator positivity)
Proof: the index `1` witnesses nonemptiness of `{1, ..., N}` when `0 < N`;
  after selecting the supplied nonzero-diameter branch, finite-sum positivity
  gives the denominator bound.
Source: Mathlib finite sums over natural-number intervals and Frank-Wolfe
  conditional-gradient parameter regimes
Used in: stochastic nonconvex conditional-gradient randomized output law after
  realizing the displayed nonzero-diameter stepsize
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem outputWeightDenominator_pos_Icc_of_nonzeroDiameter
    {D : ℝ} (hD : 0 < D) (N : ℕ) (α : 0 < D → ℕ → ℝ)
    (hN : 0 < N)
    (hα_pos : ∀ k, k ∈ Finset.Icc 1 N → 0 < α hD k) :
    0 < SOptLib.outputWeightDenominator (Finset.Icc 1 N) (α hD) := by
  have hnonempty : (Finset.Icc 1 N).Nonempty := by
    exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩⟩
  exact SOptLib.outputWeightDenominator_pos
    (Finset.Icc 1 N) (α hD) hα_pos hnonempty

/-- A conditional-gradient realization contract gives a positive output denominator.

For a diameter-dependent realized stepsize schedule, once the realization
contract supplies the nonzero-diameter branch and the schedule is positive on
the nonempty output window `{1, ..., N}`, the normalizing denominator for the
randomized output law is strictly positive.

Layer: Model | Gap: Level 1 (conditional-gradient output denominator positivity)
Proof: the index `1` witnesses nonemptiness of `{1, ..., N}` when `0 < N`;
  after selecting the contract's nonzero-diameter branch, finite-sum positivity
  gives the denominator bound.
Source: Mathlib finite sums over natural-number intervals and Frank-Wolfe
  conditional-gradient parameter regimes
Used in: stochastic nonconvex conditional-gradient randomized output law after
  realizing the displayed nonzero-diameter stepsize
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem outputWeightDenominator_pos_of_conditionalGradientContract
    {D : ℝ} {a : 0 < D → ℝ} {T : ℕ}
    (N : ℕ) (α : 0 < D → ℕ → ℝ)
    (c : ConditionalGradientRealizationContract D a T)
    (hN : 0 < N)
    (hα_pos : ∀ k, k ∈ Finset.Icc 1 N → 0 < α c.nonzeroDiameter k) :
    0 < SOptLib.outputWeightDenominator (Finset.Icc 1 N) (α c.nonzeroDiameter) :=
  outputWeightDenominator_pos_Icc_of_nonzeroDiameter
    c.nonzeroDiameter N α hN hα_pos

/-- Positive weights on the one-based interval have a positive output denominator.

For a natural-number output window `{1, ..., N}`, strict positivity of every
selected output weight and `0 < N` imply strict positivity of the named finite
output-weight denominator.

Layer: Model | Gap: Level 1 (one-based interval output denominator positivity)
Proof: the index `1` belongs to `Finset.Icc 1 N` when `0 < N`, so
  finite-sum positivity applies to the named output-weight denominator.
Source: Mathlib finite sums over ordered additive commutative monoids and
  natural-number intervals
Used in: stochastic nonconvex conditional-gradient randomized output law
  denominator after realizing the displayed stepsize branch
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem outputWeightDenominator_pos_of_Icc_pos
    {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedCancelAddMonoid M]
    (N : ℕ) (α : ℕ → M) (hN : 0 < N)
    (hα_pos : ∀ k, k ∈ Finset.Icc 1 N → 0 < α k) :
    0 < SOptLib.outputWeightDenominator (Finset.Icc 1 N) α := by
  have hnonempty : (Finset.Icc 1 N).Nonempty := by
    exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩⟩
  simpa [SOptLib.outputWeightDenominator] using
    (Finset.sum_pos hα_pos hnonempty)

/-- Accumulated squared differences of an indexed stochastic path inside an epoch.

For a path `x`, an epoch-step encoder `index`, and epoch coordinates `(s, t)`,
this is the closed-interval sum of squared increments
`‖x (index s i) - x (index s (i - 1))‖ ^ 2` over `i = 2, ..., t`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; finite closed-interval sum of squared
  consecutive path increments through an epoch-step index encoder)
Source: stochastic approximation epoch indexing and Mathlib finite interval sums
  in normed additive groups
Used in: stochastic nonconvex conditional gradient within-epoch estimator
  second-moment accumulation
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
noncomputable def epochSquaredDifferenceSum
    {Ω E : Type*} [NormedAddCommGroup E]
    (x : ℕ → Ω → E) (index : ℕ → ℕ → ℕ) (s t : ℕ) : Ω → ℝ :=
  fun ω =>
    Finset.sum (Finset.Icc 2 t)
      (fun i => ‖x (index s i) ω - x (index s (i - 1)) ω‖ ^ 2)

/-- The epoch squared-difference sum unfolds to its finite interval formula.

Layer: Model | Gap: Level 0 (epoch squared-difference sum unfolding)
Proof: by rfl after unfolding `epochSquaredDifferenceSum`.
Source: Mathlib finite interval sums and normed additive group APIs
Used in: stochastic nonconvex conditional gradient rewriting of within-epoch
  squared iterate-difference accumulations
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
@[simp]
theorem epochSquaredDifferenceSum_def
    {Ω E : Type*} [NormedAddCommGroup E]
    (x : ℕ → Ω → E) (index : ℕ → ℕ → ℕ) (s t : ℕ) (ω : Ω) :
    epochSquaredDifferenceSum x index s t ω =
      Finset.sum (Finset.Icc 2 t)
        (fun i => ‖x (index s i) ω - x (index s (i - 1)) ω‖ ^ 2) := by
  rfl

/-- The epoch squared-difference sum is pointwise nonnegative.

Layer: Model | Gap: Level 0 (epoch squared-difference sum nonnegativity)
Proof: finite sums of nonnegative squared norms are nonnegative.
Source: Mathlib finite interval sums and square nonnegativity
Used in: stochastic nonconvex conditional gradient bounds where accumulated
  squared iterate differences appear under expectations or scalar weights
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem epochSquaredDifferenceSum_nonneg
    {Ω E : Type*} [NormedAddCommGroup E]
    (x : ℕ → Ω → E) (index : ℕ → ℕ → ℕ) (s t : ℕ) (ω : Ω) :
    0 ≤ epochSquaredDifferenceSum x index s t ω := by
  rw [epochSquaredDifferenceSum_def]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Pointwise equality of indexed processes preserves epoch squared increments.

If two process families agree pointwise after choosing their realization
parameters, then their accumulated squared successive differences over the same
epoch-step indexer are equal.

Layer: Model | Gap: Level 0 (epoch squared-difference process congruence)
Proof: apply function extensionality, unfold `epochSquaredDifferenceSum`, and
  rewrite both adjacent process values in every finite-interval summand.
Source: Mathlib finite interval sums and normed additive group congruence APIs
Used in: stochastic nonconvex conditional gradient replacement of a conditional
  realization by the well-defined iterate process in within-epoch variance
  accumulation
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem epochSuccessiveDiffSqSum_eq_of_process_eq
    {Ω E : Type*} {H H' : Sort*} [NormedAddCommGroup E]
    (x : H → ℕ → Ω → E) (y : H' → ℕ → Ω → E)
    (index : ℕ → ℕ → ℕ)
    (h : H) (h' : H') (s t : ℕ)
    (hxy : ∀ k ω, x h k ω = y h' k ω) :
    epochSquaredDifferenceSum (x h) index s t =
      epochSquaredDifferenceSum (y h') index s t := by
  funext ω
  simp [epochSquaredDifferenceSum, hxy]

/-- Nonnegative weights remain nonnegative at an epoch predecessor coordinate.

For an epoch-step encoder `index`, the difference from coordinate `i - 1` to
`i` is charged to the weight stored at `index s (i - 1)`. Pointwise
nonnegativity of the raw schedule therefore transfers to every such
predecessor-coordinate lookup.

Layer: Model | Gap: Level 0 (epoch predecessor weight nonnegativity)
Proof: apply the pointwise nonnegativity hypothesis at the encoded predecessor
  coordinate.
Source: Mathlib ordered-type APIs and natural-number predecessor indexing for
  stochastic approximation schedules
Used in: stochastic nonconvex conditional gradient epochwise estimator-difference
  bounds
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem epochDifferenceWeight_nonneg
    {R : Type*} [Preorder R] [Zero R]
    (weight : ℕ → R)
    (hweight_nonneg : ∀ k, 0 ≤ weight k)
    (index : ℕ → ℕ → ℕ)
    (s i : ℕ) :
    0 ≤ weight (index s (i - 1)) :=
  hweight_nonneg (index s (i - 1))

/-- Epoch coordinate decoded from a one-based global iteration index.

For a fixed epoch length `T` and a paper-facing global index `k`, the decoded
epoch coordinate is `(k - 1) / T`. The subtraction accounts for algorithms
whose public iteration window is `k = 1, ..., N` while epochs are zero-based.

Layer: Model | Concept: Iterates
Proof: (definitional construction; natural-number quotient after converting a
  one-based global index to a zero-based offset)
Source: Mathlib natural-number subtraction and division APIs with
  stochastic-optimization epoch indexing
Used in: stochastic nonconvex conditional-gradient output-index decoding
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
def epochOfIndex (T k : ℕ) : ℕ :=
  (k - 1) / T

/-- The one-based epoch decoder unfolds to natural-number division of `k - 1`.

Layer: Model | Gap: Level 0 (one-based epoch decoder unfolding)
Proof: by rfl after unfolding `epochOfIndex`.
Source: Mathlib natural-number subtraction and division APIs
Used in: stochastic nonconvex conditional-gradient replacement of local
  one-based epoch notation by a named selector
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
@[simp]
theorem epochOfIndex_eq_div (T k : ℕ) :
    epochOfIndex T k = (k - 1) / T := by
  rfl

/-- Decoding an encoded one-based epoch-step index recovers the epoch coordinate.

If `j` is a valid one-based step in an epoch of length `T`, then decoding the
global index `s * T + j` returns the epoch coordinate `s`.

Layer: Model | Gap: Level 0 (one-based fixed-length epoch coordinate decoding)
Proof: rewrite the shifted global index as `j - 1 + T * s`, use
  `Nat.add_mul_div_left`, and discharge `(j - 1) / T = 0` from `j ≤ T`.
Source: Mathlib natural-number quotient, predecessor, and bounded-remainder arithmetic
Used in: stochastic variance-reduced conditional-gradient active-epoch output
  window decoding
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem epochOfIndex_mul_add_eq_of_pos_le {T s j : ℕ}
    (hj_pos : 1 ≤ j) (hj_le : j ≤ T) :
    epochOfIndex T (s * T + j) = s := by
  have hshift : s * T + j - 1 = j - 1 + T * s := by
    rw [Nat.mul_comm]
    omega
  have hj_lt : j - 1 < T := by
    omega
  have hT_pos : 0 < T := by
    omega
  rw [epochOfIndex_eq_div, hshift, Nat.add_mul_div_left _ _ hT_pos,
    Nat.div_eq_of_lt hj_lt]
  simp

/-- Global iteration index encoded from epoch and within-epoch coordinates.

For a fixed epoch length `T`, epoch coordinate `s`, and within-epoch step `t`,
`global_index T s t` is the natural index `s * T + t`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; natural-number affine encoder for a
  fixed-length epoch block)
Source: Mathlib natural-number arithmetic and stochastic-optimization epoch indexing
Used in: stochastic nonconvex conditional-gradient variance-reduced refresh schedule
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
def global_index (T s t : ℕ) : ℕ :=
  s * T + t

/-- The fixed-length epoch-step encoder unfolds to `s * T + t`.

Layer: Model | Gap: Level 0 (global epoch-step encoder unfolding)
Proof: by rfl after unfolding `global_index`.
Source: Mathlib natural-number multiplication and addition APIs
Used in: stochastic nonconvex conditional-gradient replacement of local global
  iteration notation by a named encoder
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
@[simp]
theorem global_index_def (T s t : ℕ) :
    global_index T s t = s * T + t := by
  rfl

/-- The global-index encoder is monotone in the within-epoch step coordinate.

Layer: Model | Gap: Level 0 (epoch-step encoder monotonicity)
Proof: unfold the encoder and apply monotonicity of addition on natural numbers.
Source: Mathlib natural-number ordered additive monoid APIs
Used in: stochastic nonconvex conditional-gradient propagation of update-window
  membership from a later within-epoch step to an earlier step
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem global_index_mono_step {T s i t : ℕ} (hi : i ≤ t) :
    global_index T s i ≤ global_index T s t := by
  exact Nat.add_le_add_left hi (s * T)

/-- An upper bound on a later encoded step also bounds any earlier step in the same epoch.

Layer: Model | Gap: Level 0 (epoch-step prefix bound)
Proof: combine monotonicity of the encoder in its within-epoch coordinate with
  transitivity of `≤`.
Source: Mathlib natural-number ordered additive monoid APIs
Used in: stochastic nonconvex conditional-gradient source-domain checks for
  recursive estimator updates before a target within-epoch step
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem global_index_le_of_step_le {T N s i t : ℕ}
    (hi : i ≤ t) (ht : global_index T s t ≤ N) :
    global_index T s i ≤ N :=
  le_trans (global_index_mono_step hi) ht

/-- Deprecated compatibility alias for algorithm files staged before the snake_case rename. -/
@[deprecated global_index (since := "2026-06-01")]
abbrev globalIndex (T s t : ℕ) : ℕ :=
  global_index T s t

/-- Decoding and re-encoding a positive one-based global index returns the same index.

For any epoch length `T`, the one-based global index `k` is recovered by
decoding its epoch coordinate with `epochOfIndex`, decoding its within-epoch
coordinate as `(k - 1) % T + 1`, and encoding those coordinates with
`global_index`.

Layer: Model | Gap: Level 0 (one-based fixed-length epoch index reconstruction)
Proof: unfold the named decoders, rewrite by quotient-remainder decomposition
  for `k - 1`, and use `1 ≤ k` to remove the predecessor/successor shift.
Source: Mathlib natural-number quotient-remainder arithmetic
Used in: stochastic variance-reduced conditional-gradient output-window
  reindexing by decoded epoch-step coordinates
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem global_index_epochOfIndex_stepOfIndex {T k : ℕ} (hk : 1 ≤ k) :
    global_index T (epochOfIndex T k) ((k - 1) % T + 1) = k := by
  rw [global_index_def, epochOfIndex_eq_div]
  rw [Nat.mul_comm ((k - 1) / T) T, ← Nat.add_assoc, Nat.div_add_mod]
  omega

/-- An active epoch coordinate maps to the one-based output window.

If `activeEpochSteps T N globalIndex s` records the within-epoch coordinates
whose encoded global iteration remains at most `N`, and the encoded active
coordinate is positive, then the coordinate maps into `{1, ..., N}`.

Layer: Model | Gap: Level 1 (active epoch output-window membership)
Proof: project the epoch-coordinate and horizon components from active-step
  membership; encoder positivity supplies the lower bound and the active-step
  filter supplies the upper bound.
Source: Mathlib natural-number finite intervals and filtered finset APIs
Used in: stochastic variance-reduced conditional-gradient output-window
  membership for active finite-sum and stochastic epoch coordinates
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem global_index_mem_output_window_of_active_epoch_step
    {T N : ℕ} {globalIndex : ℕ → ℕ → ℕ} {s j : ℕ}
    (hglobalIndex_pos : 1 ≤ globalIndex s j)
    (hj : j ∈ activeEpochSteps T N globalIndex s) :
    globalIndex s j ∈ Finset.Icc 1 N := by
  have hjN := activeEpochSteps_globalIndex_le (T := T) (N := N)
    (globalIndex := globalIndex) (s := s) (j := j) hj
  exact Finset.mem_Icc.mpr ⟨hglobalIndex_pos, hjN⟩

/-- A public iterate projection of a feasible state process is feasible.

If `iterateProcess` is pointwise the `stateValue` projection of a state-valued
process, then every feasibility invariant proved for that state projection on
the valid time indices transfers to the public iterate view.

Layer: Model | Gap: Level 1 (state-process iterate feasibility bridge)
Proof: fix the time and sample, rewrite the public iterate by the projection
  equation, and apply the supplied state-process feasibility invariant.
Source: Mathlib Pi-function equality rewriting and set membership APIs
Used in: finite-sum conditional-gradient iterate feasibility from bundled
  state-process feasibility
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem iterateProcess_mem_of_process_mem
    {Ω T State E : Type*} {X : Set E} {Valid : T → Prop}
    (process : T → Ω → State)
    (iterateProcess : T → Ω → E)
    (stateValue : State → E)
    (hiterate : ∀ t ω, iterateProcess t ω = stateValue (process t ω))
    (hprocess : ∀ t ω, Valid t → stateValue (process t ω) ∈ X) :
    ∀ t ω, Valid t → iterateProcess t ω ∈ X := by
  intro t ω ht
  simpa [hiterate t ω] using hprocess t ω ht

/-- Conditional-gradient iterate update from a stepsize schedule and linear minimizer.

Given a current iterate `x`, an estimator or gradient-like input `G`, a
time-indexed stepsize `alpha`, and a linear-minimization selector, this returns
the Frank-Wolfe affine update `(1 - alpha k) • x + alpha k • linearMinimizer G`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; canonical affine LMO-driven
  conditional-gradient step)
Source: Frank-Wolfe conditional-gradient update formulas and Mathlib scalar
  multiplication APIs
Used in: stochastic nonconvex conditional gradient LMO iterate recursion
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
def conditionalGradientIterUpdate
    {E : Type*} [Add E] [SMul ℝ E]
    (alpha : ℕ → ℝ) (linearMinimizer : E → E) (x G : E) (k : ℕ) : E :=
  (1 - alpha k) • x + alpha k • linearMinimizer G

/-- The conditional-gradient iterate update unfolds to its affine LMO formula.

This is the controlled simp theorem for exposing the raw update formula when
downstream proofs need scalar or convexity algebra.

Layer: Model | Gap: Level 0 (conditional-gradient update unfolding)
Proof: by rfl after unfolding `conditionalGradientIterUpdate`.
Source: Frank-Wolfe conditional-gradient update formulas and Mathlib scalar
  multiplication APIs
Used in: stochastic nonconvex conditional gradient feasibility and one-step descent
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
@[simp]
theorem conditionalGradientIterUpdate_def
    {E : Type*} [Add E] [SMul ℝ E]
    (alpha : ℕ → ℝ) (linearMinimizer : E → E) (x G : E) (k : ℕ) :
    conditionalGradientIterUpdate alpha linearMinimizer x G k =
      (1 - alpha k) • x + alpha k • linearMinimizer G := by
  rfl

/-- A conditional-gradient realization contract bounds the realized stepsize at
any positive-diameter witness.

The contract stores the bound at its own `nonzeroDiameter` witness. Since the
stepsize may depend on the proof of `0 < D`, this theorem transports the stored
bound to any equivalent positive-diameter witness by proof irrelevance.

Layer: Model | Gap: Level 0 (conditional-gradient contract stepsize witness bridge)
Proof: identify the requested positive-diameter witness with the contract's
  stored witness by proof irrelevance, then apply the stored stepsize bound.
Source: Frank-Wolfe conditional-gradient parameter regimes and Lean proof
  irrelevance for propositions
Used in: stochastic nonconvex conditional-gradient convex-combination update
  realized from a displayed positive-diameter well-definedness accessor
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem alpha_le_one_of_conditional_gradient_realization_contract
    {D : ℝ} {α : 0 < D → ℝ} {T : ℕ}
    (c : ConditionalGradientRealizationContract D α T) (hD : 0 < D) :
    α hD ≤ 1 := by
  have hproof : hD = c.nonzeroDiameter := Subsingleton.elim _ _
  rw [hproof]
  exact c.alpha_le_one

/-- Finite-sum conditional-gradient state process with exact epoch refreshes.

The process starts from an initial iterate and zero estimator, initializes at
time one with the exact gradient, and then alternates between exact epoch
refreshes and supplied recursive estimator updates while applying a supplied
iterate update rule.

Layer: Model | Concept: Iterates
Proof: (definitional construction; primitive recursion with exact full-gradient
  refreshes, recursive estimator updates, and a generic conditional-gradient
  update rule)
Source: finite-sum variance-reduction recursions and Mathlib natural-number APIs
Used in: finite-sum stochastic nonconvex conditional gradient exact-refresh state recursion
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
noncomputable def finiteSumConditionalGradientProcess
    {Ω State E : Type*} [Zero E]
    (mkState : E → E → ℕ → State)
    (stateX : State → E) (stateEstimator : State → E) (stateEpoch : State → ℕ)
    (x0 : E)
    (grad : E → E)
    (recursiveEstimator : E → E → E → ℕ → ℕ → Ω → E)
    (iterUpdate : E → E → ℕ → E)
    (T b : ℕ) :
    ℕ → Ω → State
  | 0 => fun _ => mkState x0 0 0
  | 1 => fun _ => mkState x0 (grad x0) 0
  | k + 2 => fun ω =>
      let prev :=
        finiteSumConditionalGradientProcess mkState stateX stateEstimator stateEpoch
          x0 grad recursiveEstimator iterUpdate T b (k + 1) ω
      let xk := stateX prev
      let Gk := stateEstimator prev
      let sk := stateEpoch prev
      let xk1 := iterUpdate xk Gk (k + 1)
      let isNextEpochStart := ((k + 1) % T == 0)
      let sk1 := if isNextEpochStart then sk + 1 else sk
      let Gk1 : E :=
        if isNextEpochStart then grad xk1
        else recursiveEstimator Gk xk xk1 ((k + 1) * b) b ω
      mkState xk1 Gk1 sk1

/-- The finite-sum exact-refresh process starts from the initial state.

Layer: Model | Gap: Level 0 (finite-sum process initial state)
Proof: by rfl after unfolding `finiteSumConditionalGradientProcess`.
Source: Mathlib natural-number primitive recursion APIs
Used in: finite-sum stochastic nonconvex conditional gradient process initialization
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/initialization
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
@[simp]
theorem finiteSumConditionalGradientProcess_zero
    {Ω State E : Type*} [Zero E]
    (mkState : E → E → ℕ → State)
    (stateX : State → E) (stateEstimator : State → E) (stateEpoch : State → ℕ)
    (x0 : E)
    (grad : E → E)
    (recursiveEstimator : E → E → E → ℕ → ℕ → Ω → E)
    (iterUpdate : E → E → ℕ → E)
    (T b : ℕ) :
    finiteSumConditionalGradientProcess mkState stateX stateEstimator stateEpoch
        x0 grad recursiveEstimator iterUpdate T b 0 =
      fun _ => mkState x0 0 0 := by
  rfl

/-- At time one, the finite-sum exact-refresh process uses the exact gradient.

Layer: Model | Gap: Level 0 (finite-sum process first exact refresh)
Proof: by rfl after unfolding `finiteSumConditionalGradientProcess`.
Source: Mathlib natural-number primitive recursion APIs
Used in: finite-sum stochastic nonconvex conditional gradient first estimator refresh
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
@[simp]
theorem finiteSumConditionalGradientProcess_one
    {Ω State E : Type*} [Zero E]
    (mkState : E → E → ℕ → State)
    (stateX : State → E) (stateEstimator : State → E) (stateEpoch : State → ℕ)
    (x0 : E)
    (grad : E → E)
    (recursiveEstimator : E → E → E → ℕ → ℕ → Ω → E)
    (iterUpdate : E → E → ℕ → E)
    (T b : ℕ) :
    finiteSumConditionalGradientProcess mkState stateX stateEstimator stateEpoch
        x0 grad recursiveEstimator iterUpdate T b 1 =
      fun _ => mkState x0 (grad x0) 0 := by
  rfl

/-- The successor-after-successor state follows the exact-refresh or recursive branch.

Layer: Model | Gap: Level 0 (finite-sum process recursive unfolding)
Proof: by rfl after unfolding `finiteSumConditionalGradientProcess`.
Source: Mathlib if-then-else and natural-number primitive recursion APIs
Used in: finite-sum stochastic nonconvex conditional gradient recursive estimator update
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
@[simp]
theorem finiteSumConditionalGradientProcess_succ_succ
    {Ω State E : Type*} [Zero E]
    (mkState : E → E → ℕ → State)
    (stateX : State → E) (stateEstimator : State → E) (stateEpoch : State → ℕ)
    (x0 : E)
    (grad : E → E)
    (recursiveEstimator : E → E → E → ℕ → ℕ → Ω → E)
    (iterUpdate : E → E → ℕ → E)
    (T b : ℕ)
    (k : ℕ) :
    finiteSumConditionalGradientProcess mkState stateX stateEstimator stateEpoch
        x0 grad recursiveEstimator iterUpdate T b (k + 2) =
      fun ω =>
        let prev :=
          finiteSumConditionalGradientProcess mkState stateX stateEstimator stateEpoch
            x0 grad recursiveEstimator iterUpdate T b (k + 1) ω
        let xk := stateX prev
        let Gk := stateEstimator prev
        let sk := stateEpoch prev
        let xk1 := iterUpdate xk Gk (k + 1)
        let isNextEpochStart := ((k + 1) % T == 0)
        let sk1 := if isNextEpochStart then sk + 1 else sk
        let Gk1 : E :=
          if isNextEpochStart then grad xk1
          else recursiveEstimator Gk xk xk1 ((k + 1) * b) b ω
        mkState xk1 Gk1 sk1 := by
  rfl

/-- Variance-reduced conditional-gradient state process with epoch refreshes.

The process starts from an initial iterate, builds an initial full-batch
estimator, and then alternates between an epoch-start refresh average and a
within-epoch recursive gradient-difference estimator while applying a supplied
iterate update rule.

Layer: Model | Concept: Iterates
Proof: (definitional construction; primitive recursion with epoch-refresh
  mini-batches, recursive gradient-difference mini-batches, and a generic
  conditional-gradient update rule)
Source: stochastic variance-reduction recursions and Mathlib finite-sum APIs
Used in: stochastic nonconvex conditional gradient Algorithm 7.13 state recursion
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
noncomputable def varianceReducedConditionalGradientProcess
    {Ω State E S : Type*} [AddCommMonoid E] [Sub E] [SMul ℝ E]
    (mkState : E → E → ℕ → State)
    (stateX : State → E) (stateEstimator : State → E) (stateEpoch : State → ℕ)
    (x0 : E)
    (m b T N : ℕ)
    (sample : ℕ → Ω → S)
    (gradF : E → S → E)
    (update : E → E → ℕ → E) :
    ℕ → Ω → State
  | 0 => fun _ => mkState x0 0 0
  | 1 => fun ω =>
      mkState x0
        ((m : ℝ)⁻¹ •
          Finset.sum (Finset.range m) (fun i => gradF x0 (sample i ω)))
        0
  | k + 2 => fun ω =>
      let prev :=
        varianceReducedConditionalGradientProcess mkState stateX stateEstimator stateEpoch
          x0 m b T N sample gradF update (k + 1) ω
      let xk := stateX prev
      let Gk := stateEstimator prev
      let sk := stateEpoch prev
      let xk1 := update xk Gk (k + 1)
      let isNextEpochStart := ((k + 1) % T == 0)
      let sk1 := if isNextEpochStart then sk + 1 else sk
      let Gk1 : E :=
        if isNextEpochStart then
          (m : ℝ)⁻¹ •
            Finset.sum (Finset.range m)
              (fun i => gradF xk1 (sample (sk1 * m + i) ω))
        else
          (b : ℝ)⁻¹ •
              Finset.sum (Finset.range b)
                (fun i =>
                  gradF xk1 (sample (N * m + (k + 1) * b + i) ω) -
                  gradF xk (sample (N * m + (k + 1) * b + i) ω)) +
            Gk
      mkState xk1 Gk1 sk1

/-- The variance-reduced conditional-gradient process starts from the initial state.

Layer: Model | Gap: Level 0 (variance-reduced process initial state)
Proof: by rfl after unfolding `varianceReducedConditionalGradientProcess`.
Source: Mathlib natural-number primitive recursion APIs
Used in: stochastic nonconvex conditional gradient Algorithm 7.13 state recursion
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/initialization
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
@[simp]
theorem varianceReducedConditionalGradientProcess_zero
    {Ω State E S : Type*} [AddCommMonoid E] [Sub E] [SMul ℝ E]
    (mkState : E → E → ℕ → State)
    (stateX : State → E) (stateEstimator : State → E) (stateEpoch : State → ℕ)
    (x0 : E)
    (m b T N : ℕ)
    (sample : ℕ → Ω → S)
    (gradF : E → S → E)
    (update : E → E → ℕ → E) :
    varianceReducedConditionalGradientProcess mkState stateX stateEstimator stateEpoch
        x0 m b T N sample gradF update 0 =
      fun _ => mkState x0 0 0 := by
  rfl

/-- At time one, the variance-reduced conditional-gradient process uses the refresh average.

Layer: Model | Gap: Level 0 (variance-reduced process first refresh)
Proof: by rfl after unfolding `varianceReducedConditionalGradientProcess`.
Source: Mathlib finite-sum and natural-number primitive recursion APIs
Used in: stochastic nonconvex conditional gradient first gradient-estimator construction
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
@[simp]
theorem varianceReducedConditionalGradientProcess_one
    {Ω State E S : Type*} [AddCommMonoid E] [Sub E] [SMul ℝ E]
    (mkState : E → E → ℕ → State)
    (stateX : State → E) (stateEstimator : State → E) (stateEpoch : State → ℕ)
    (x0 : E)
    (m b T N : ℕ)
    (sample : ℕ → Ω → S)
    (gradF : E → S → E)
    (update : E → E → ℕ → E) :
    varianceReducedConditionalGradientProcess mkState stateX stateEstimator stateEpoch
        x0 m b T N sample gradF update 1 =
      fun ω =>
        mkState x0
          ((m : ℝ)⁻¹ •
            Finset.sum (Finset.range m) (fun i => gradF x0 (sample i ω)))
          0 := by
  rfl

/-- The successor-after-successor state follows the epoch-refresh or recursive branch.

Layer: Model | Gap: Level 0 (variance-reduced process recursive unfolding)
Proof: by rfl after unfolding `varianceReducedConditionalGradientProcess`.
Source: Mathlib finite-sum, if-then-else, and natural-number primitive recursion APIs
Used in: stochastic nonconvex conditional gradient recursive estimator and iterate update
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
@[simp]
theorem varianceReducedConditionalGradientProcess_succ_succ
    {Ω State E S : Type*} [AddCommMonoid E] [Sub E] [SMul ℝ E]
    (mkState : E → E → ℕ → State)
    (stateX : State → E) (stateEstimator : State → E) (stateEpoch : State → ℕ)
    (x0 : E)
    (m b T N : ℕ)
    (sample : ℕ → Ω → S)
    (gradF : E → S → E)
    (update : E → E → ℕ → E)
    (k : ℕ) :
    varianceReducedConditionalGradientProcess mkState stateX stateEstimator stateEpoch
        x0 m b T N sample gradF update (k + 2) =
      fun ω =>
        let prev :=
          varianceReducedConditionalGradientProcess mkState stateX stateEstimator stateEpoch
            x0 m b T N sample gradF update (k + 1) ω
        let xk := stateX prev
        let Gk := stateEstimator prev
        let sk := stateEpoch prev
        let xk1 := update xk Gk (k + 1)
        let isNextEpochStart := ((k + 1) % T == 0)
        let sk1 := if isNextEpochStart then sk + 1 else sk
        let Gk1 : E :=
          if isNextEpochStart then
            (m : ℝ)⁻¹ •
              Finset.sum (Finset.range m)
                (fun i => gradF xk1 (sample (sk1 * m + i) ω))
          else
            (b : ℝ)⁻¹ •
                Finset.sum (Finset.range b)
                  (fun i =>
                    gradF xk1 (sample (N * m + (k + 1) * b + i) ω) -
                    gradF xk (sample (N * m + (k + 1) * b + i) ω)) +
              Gk
        mkState xk1 Gk1 sk1 := by
  rfl

/-- Characterization of `varianceReducedConditionalGradientProcess` as a
three-way primitive recursion.

This lemma keeps the named process opaque by default while giving downstream
proofs a single controlled unfolding rule when the raw recursion is needed.

Layer: Model | Gap: Level 0 (variance-reduced process full unfolding)
Proof: function extensionality followed by case splitting on the natural time index.
Source: Mathlib natural-number primitive recursion and Pi-function extensionality APIs
Used in: stochastic nonconvex conditional gradient state-recursion unfolding
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
theorem varianceReducedConditionalGradientProcess_def
    {Ω State E S : Type*} [AddCommMonoid E] [Sub E] [SMul ℝ E]
    (mkState : E → E → ℕ → State)
    (stateX : State → E) (stateEstimator : State → E) (stateEpoch : State → ℕ)
    (x0 : E)
    (m b T N : ℕ)
    (sample : ℕ → Ω → S)
    (gradF : E → S → E)
    (update : E → E → ℕ → E) :
    varianceReducedConditionalGradientProcess mkState stateX stateEstimator stateEpoch
        x0 m b T N sample gradF update =
      fun
        | 0 => fun _ =>
            mkState x0 0 0
        | 1 => fun ω =>
            mkState x0
              ((m : ℝ)⁻¹ •
                Finset.sum (Finset.range m) (fun i => gradF x0 (sample i ω)))
              0
        | k + 2 => fun ω =>
            let prev :=
              varianceReducedConditionalGradientProcess mkState stateX stateEstimator stateEpoch
                x0 m b T N sample gradF update (k + 1) ω
            let xk := stateX prev
            let Gk := stateEstimator prev
            let sk := stateEpoch prev
            let xk1 := update xk Gk (k + 1)
            let isNextEpochStart := ((k + 1) % T == 0)
            let sk1 := if isNextEpochStart then sk + 1 else sk
            let Gk1 : E :=
              if isNextEpochStart then
                (m : ℝ)⁻¹ •
                  Finset.sum (Finset.range m)
                    (fun i => gradF xk1 (sample (sk1 * m + i) ω))
              else
                (b : ℝ)⁻¹ •
                    Finset.sum (Finset.range b)
                      (fun i =>
                        gradF xk1 (sample (N * m + (k + 1) * b + i) ω) -
                        gradF xk (sample (N * m + (k + 1) * b + i) ω)) +
                  Gk
            mkState xk1 Gk1 sk1 := by
  funext n
  rcases n with _ | (_ | k) <;> rfl

/-- A state-valued stochastic process remains feasible through a finite horizon
when the first two slices are feasible and every later transition preserves
feasibility of the displayed state projection.

This covers warm-started recursions whose first successor is initialized
separately from the generic update rule.

Layer: Model | Gap: Level 1 (warm-started process feasibility induction)
Proof: induction on natural time with separate `0`, `1`, and later-successor
  cases; the later case invokes the supplied pointwise transition invariant.
Source: Mathlib natural-number induction, finite interval membership, and set
  membership APIs
Used in: finite-sum and variance-reduced conditional-gradient process
  feasibility through the output horizon
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem process_mem_of_update_mem
    {Ω State E : Type*} {X : Set E}
    (process : ℕ → Ω → State) (stateX : State → E) (N : ℕ)
    (hzero : ∀ ω, stateX (process 0 ω) ∈ X)
    (hone : ∀ ω, stateX (process 1 ω) ∈ X)
    (hupdate :
      ∀ ⦃n : ℕ⦄ ⦃ω : Ω⦄,
        n + 1 ∈ Finset.Icc 1 N →
          stateX (process (n + 1) ω) ∈ X →
            stateX (process (n + 2) ω) ∈ X) :
    ∀ k ω, k ≤ N → stateX (process k ω) ∈ X := by
  intro k
  induction k with
  | zero =>
      intro ω _hk
      exact hzero ω
  | succ k ih =>
      cases k with
      | zero =>
          intro ω _hk
          exact hone ω
      | succ n =>
          intro ω hkN
          have hprev : stateX (process (n + 1) ω) ∈ X := by
            exact ih ω (by omega)
          have hidx : n + 1 ∈ Finset.Icc 1 N := by
            simp [Finset.mem_Icc]
            omega
          simpa [Nat.add_assoc] using
            hupdate (n := n) (ω := ω) hidx hprev

/-- One-based within-epoch step coordinate induced by a fixed epoch length.

For a natural epoch length `T` and zero-based global iteration counter `k`,
`stepOf T k` is the remainder coordinate `k % T + 1`, so valid coordinates
range over `1, ..., T` when `T` is positive.

Layer: Model | Concept: Iterates
Proof: (definitional construction; natural-number remainder converted to a
  one-based within-epoch coordinate)
Source: Mathlib natural-number modulo APIs and stochastic-optimization epoch indexing
Used in: stochastic nonconvex conditional-gradient recursive estimator schedule
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
def stepOf (T k : ℕ) : ℕ :=
  k % T + 1

/-- The within-epoch step selector unfolds to `k % T + 1`.

Layer: Model | Gap: Level 0 (within-epoch step selector unfolding)
Proof: by rfl after unfolding `stepOf`.
Source: Mathlib natural-number modulo and successor APIs
Used in: stochastic nonconvex conditional-gradient replacement of local
  within-epoch notation by a named selector
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
@[simp]
theorem stepOf_eq_mod_add_one (T k : ℕ) :
    stepOf T k = k % T + 1 := by
  rfl

/-- The decoded within-epoch coordinate lies in `1, ..., T`.

Layer: Model | Gap: Level 0 (one-based modulo coordinate bounds)
Proof: use `Nat.mod_lt` for the upper remainder bound and natural-number
  arithmetic for the one-based lower bound.
Source: Mathlib natural-number modulo bounds and order arithmetic
Used in: stochastic variance-reduced conditional-gradient active-epoch
  coordinate membership
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem stepOf_mem_epoch {T k : ℕ} (hT : 0 < T) :
    1 ≤ stepOf T k ∧ stepOf T k ≤ T := by
  have hmod : k % T < T := Nat.mod_lt k hT
  simp [stepOf]
  omega

/-- Decoding an encoded zero-based epoch-step index recovers the one-based step.

If `j` is a valid one-based step in an epoch of length `T`, then the zero-based
global counter `s * T + (j - 1)` has within-epoch coordinate `j`.

Layer: Model | Gap: Level 0 (fixed-length within-epoch coordinate decoding)
Proof: rewrite the encoded counter modulo `T`, reduce the bounded remainder
  `j - 1`, and convert back from the predecessor to the one-based coordinate.
Source: Mathlib natural-number remainder arithmetic for quotient-remainder decoding
Used in: stochastic variance-reduced conditional-gradient epoch-step coordinate
  normalization
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem stepOf_mul_add_sub_one_eq_of_pos_le {T s j : ℕ}
    (hj_pos : 1 ≤ j) (hj_le : j ≤ T) :
    stepOf T (s * T + (j - 1)) = j := by
  have hj_lt : j - 1 < T := by
    omega
  have hshift : s * T + (j - 1) = (j - 1) + T * s := by
    rw [Nat.mul_comm s T]
    omega
  rw [stepOf_eq_mod_add_one, hshift, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hj_lt]
  omega

/-- Within-epoch step coordinate decoded from a one-based global iteration index.

For a fixed epoch length `T` and a paper-facing global index `k`, the decoded
within-epoch coordinate is `(k - 1) % T + 1`. The subtraction converts the
one-based public index into the zero-based counter used by `stepOf`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; one-based global index shifted to the
  zero-based within-epoch selector)
Source: Mathlib natural-number subtraction and modulo APIs with
  stochastic-optimization epoch indexing
Used in: stochastic nonconvex conditional-gradient output-index decoding into
  epoch-local recursive estimator steps
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
def stepOfIndex (T k : ℕ) : ℕ :=
  stepOf T (k - 1)

/-- The one-based within-epoch decoder is the zero-based selector at `k - 1`.

Layer: Model | Gap: Level 0 (one-based step decoder as shifted selector)
Proof: by rfl after unfolding `stepOfIndex`.
Source: Mathlib natural-number subtraction and modulo APIs
Used in: stochastic nonconvex conditional-gradient replacement of local
  one-based step notation by the canonical zero-based selector
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
@[simp]
theorem stepOfIndex_eq_stepOf_pred (T k : ℕ) :
    stepOfIndex T k = stepOf T (k - 1) := by
  rfl

/-- The one-based within-epoch decoder unfolds to `(k - 1) % T + 1`.

Layer: Model | Gap: Level 0 (one-based step decoder unfolding)
Proof: by rfl after unfolding `stepOfIndex` and `stepOf`.
Source: Mathlib natural-number subtraction, modulo, and successor APIs
Used in: stochastic nonconvex conditional-gradient replacement of local
  within-epoch notation by a named selector
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem stepOfIndex_eq_mod_add_one (T k : ℕ) :
    stepOfIndex T k = (k - 1) % T + 1 := by
  rfl

/-- The decoded one-based within-epoch coordinate lies in `1, ..., T`.

Layer: Model | Gap: Level 0 (one-based modulo coordinate bounds)
Proof: reduce to the zero-based `stepOf` bounds at counter `k - 1`.
Source: Mathlib natural-number modulo bounds and order arithmetic
Used in: stochastic variance-reduced conditional-gradient active-epoch
  coordinate membership for output indices
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem stepOfIndex_mem_epoch {T k : ℕ} (hT : 0 < T) :
    1 ≤ stepOfIndex T k ∧ stepOfIndex T k ≤ T := by
  simpa [stepOfIndex] using stepOf_mem_epoch (T := T) (k := k - 1) hT

/-- Decoding an encoded one-based epoch-step index recovers the step coordinate.

If `j` is a valid one-based step in an epoch of length `T`, then decoding the
global index `s * T + j` returns the within-epoch coordinate `j`.

Layer: Model | Gap: Level 0 (one-based fixed-length step coordinate decoding)
Proof: shift `s * T + j` to the zero-based counter `s * T + (j - 1)`,
  then apply the zero-based `stepOf` decode law.
Source: Mathlib natural-number predecessor and remainder arithmetic for
  quotient-remainder decoding
Used in: stochastic variance-reduced conditional-gradient epoch-step coordinate
  normalization
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem stepOfIndex_mul_add_eq_of_pos_le {T s j : ℕ}
    (hj_pos : 1 ≤ j) (hj_le : j ≤ T) :
    stepOfIndex T (s * T + j) = j := by
  rw [stepOfIndex_eq_stepOf_pred]
  have hshift : s * T + j - 1 = s * T + (j - 1) := by
    omega
  rw [hshift]
  exact stepOf_mul_add_sub_one_eq_of_pos_le (T := T) (s := s) (j := j)
    hj_pos hj_le

/-- The one-based step decoder recovers a valid step from the global epoch-step encoder.

For a fixed epoch length `T`, if `j` is a valid one-based coordinate in
`1, ..., T`, then decoding the step coordinate of `global_index T s j`
returns `j`.

Layer: Model | Gap: Level 0 (one-based fixed-length encoder step decoding)
Proof: unfold the named fixed-length encoder and apply the existing
  one-based decoder law for the raw index `s * T + j`.
Source: Mathlib natural-number quotient-remainder arithmetic and fixed-length
  stochastic-optimization epoch indexing
Used in: stochastic variance-reduced conditional-gradient active-output
  reindexing by epoch-local step coordinates
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem nat_stepOf_globalIndex_eq {T s j : ℕ}
    (hj_pos : 1 ≤ j) (hj_le : j ≤ T) :
    stepOfIndex T (global_index T s j) = j := by
  simpa [global_index_def] using
    stepOfIndex_mul_add_eq_of_pos_le (T := T) (s := s) (j := j) hj_pos hj_le

/-- A decoded step coordinate from an output-window index lies in its decoded active epoch.

If a decoder sends every output index `k ∈ {1, ..., N}` to a valid
within-epoch step and re-encoding the decoded epoch and step returns `k`, then
that decoded step belongs to the active step window of the decoded epoch.

Layer: Model | Gap: Level 0 (decoded epoch-step active-window membership)
Proof: unfold membership in the active epoch-step finset, use the step-coordinate
  bound for the interval component, and rewrite the global-index component by
  the reconstruction law.
Source: Mathlib finite intervals, filtered finset membership, and natural-number
  quotient-remainder indexing APIs
Used in: stochastic variance-reduced conditional-gradient output-window
  reindexing by decoded epoch-step coordinates
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem stepOfIndex_mem_activeEpochSteps
    {T N : ℕ}
    {globalIndex : ℕ → ℕ → ℕ}
    {epochOfIndex stepOfIndex : ℕ → ℕ}
    (hstep_mem_epoch :
      ∀ {k : ℕ}, k ∈ Finset.Icc 1 N → stepOfIndex k ∈ Finset.Icc 1 T)
    (hglobalIndex_decode :
      ∀ {k : ℕ}, k ∈ Finset.Icc 1 N →
        globalIndex (epochOfIndex k) (stepOfIndex k) = k)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 N) :
    stepOfIndex k ∈ activeEpochSteps T N globalIndex (epochOfIndex k) := by
  rw [mem_activeEpochSteps]
  exact ⟨hstep_mem_epoch hk, by
    rw [hglobalIndex_decode hk]
    exact (Finset.mem_Icc.mp hk).2⟩

/-- Active epoch coordinates lie in the underlying epoch interval.

For any active-step family whose members lie in the epoch interval
`Finset.Icc 1 T`, membership in that family implies the one-based within-epoch
bounds `1 ≤ j` and `j ≤ T`.

Layer: Model | Gap: Level 0 (active epoch-coordinate bounds)
Proof: apply the supplied interval-membership implication, then decode
  finite-interval membership with `Finset.mem_Icc`.
Source: Mathlib finite intervals and filtered finset membership APIs
Used in: stochastic variance-reduced conditional-gradient epochwise inner-loop
  bounds before summing active steps
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem activeEpochStepsOfGlobalIndex_mem_epoch
    {T : Nat}
    {activeEpochSteps : Nat → Finset Nat}
    (hmem_epoch : ∀ {s j : Nat}, j ∈ activeEpochSteps s → j ∈ Finset.Icc 1 T)
    {s j : Nat}
    (hj : j ∈ activeEpochSteps s) :
    1 ≤ j ∧ j ≤ T := by
  exact Finset.mem_Icc.mp (hmem_epoch hj)

/-- Reindex a finite output window by an epoch-step partition.

If `epochOfIndex` and `stepOfIndex` decode every global output index, and
`globalIndex` encodes every active epoch-step pair back into the output
window, then summing any additive weight over the output window equals the
nested epoch-step sum.

Layer: Model | Gap: Level 1 (finite output-window epoch partition)
Proof: convert the nested sum to a sigma-indexed finite sum and apply
  `Finset.sum_bij` using the supplied encoder/decoder inverse laws.
Source: Mathlib finite sums over intervals, sigma finsets, and bijective
  reindexing APIs
Used in: stochastic variance-reduced methods reindexing active epoch budgets
  into global output-window normalization sums
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem sum_outputWindow_eq_sum_activeEpochSteps
    {R : Type*} [AddCommMonoid R]
    (N S : ℕ) (A : ℕ → R)
    (activeEpochSteps : ℕ → Finset ℕ)
    (globalIndex : ℕ → ℕ → ℕ)
    (epochOfIndex stepOfIndex : ℕ → ℕ)
    (h_mem :
      ∀ k ∈ Finset.Icc 1 N,
        epochOfIndex k ∈ Finset.Icc 0 S ∧
          stepOfIndex k ∈ activeEpochSteps (epochOfIndex k))
    (h_left_inv :
      ∀ k ∈ Finset.Icc 1 N,
        globalIndex (epochOfIndex k) (stepOfIndex k) = k)
    (h_right_inv :
      ∀ {s j : ℕ}, s ∈ Finset.Icc 0 S → j ∈ activeEpochSteps s →
        globalIndex s j ∈ Finset.Icc 1 N ∧
          epochOfIndex (globalIndex s j) = s ∧
            stepOfIndex (globalIndex s j) = j) :
    Finset.sum (Finset.Icc 1 N) A =
      Finset.sum (Finset.Icc 0 S)
        (fun s => Finset.sum (activeEpochSteps s)
          (fun j => A (globalIndex s j))) := by
  classical
  rw [Finset.sum_sigma']
  refine Finset.sum_bij
    (fun k _hk => Sigma.mk (epochOfIndex k) (stepOfIndex k))
    ?mem ?inj ?surj ?sum_eq
  · intro k hk
    rw [Finset.mem_sigma]
    exact h_mem k hk
  · intro k₁ hk₁ k₂ hk₂ hpair
    have hglobal :=
      congrArg (fun p : Sigma fun _s : ℕ => ℕ => globalIndex p.1 p.2) hpair
    simpa [h_left_inv k₁ hk₁, h_left_inv k₂ hk₂] using hglobal
  · intro p hp
    rcases p with ⟨s, j⟩
    have hs : s ∈ Finset.Icc 0 S := (Finset.mem_sigma.mp hp).1
    have hj : j ∈ activeEpochSteps s := (Finset.mem_sigma.mp hp).2
    have hright := h_right_inv hs hj
    refine ⟨globalIndex s j, hright.1, ?_⟩
    apply Sigma.ext
    · exact hright.2.1
    · simp [hright.2.2]
  · intro k hk
    simp [h_left_inv k hk]

/-- The active epoch-step partition has real cardinality equal to the output window size.

When `globalIndex` encodes active epoch-step pairs and `epochOfIndex`/`stepOfIndex`
decode every generated output index, the sum of the real cardinalities of all
active epoch-step sets is exactly `N`.

Layer: Model | Gap: Level 1 (finite output-window epoch-partition cardinality)
Proof: specialize the active epoch-step partition reindexing theorem to the
  constant real weight `1`, then simplify finite sums of constants and the
  cardinality of the natural output interval.
Source: Mathlib finite sums over natural intervals and finset cardinality APIs
Used in: stochastic variance-reduced conditional-gradient variance-floor
  normalization over active epoch steps
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem sum_card_active_epoch_steps_eq_output_window_card_real
    (N S : ℕ)
    (activeEpochSteps : ℕ → Finset ℕ)
    (globalIndex : ℕ → ℕ → ℕ)
    (epochOfIndex stepOfIndex : ℕ → ℕ)
    (h_mem :
      ∀ k ∈ Finset.Icc 1 N,
        epochOfIndex k ∈ Finset.Icc 0 S ∧
          stepOfIndex k ∈ activeEpochSteps (epochOfIndex k))
    (h_left_inv :
      ∀ k ∈ Finset.Icc 1 N,
        globalIndex (epochOfIndex k) (stepOfIndex k) = k)
    (h_right_inv :
      ∀ {s j : ℕ}, s ∈ Finset.Icc 0 S → j ∈ activeEpochSteps s →
        globalIndex s j ∈ Finset.Icc 1 N ∧
          epochOfIndex (globalIndex s j) = s ∧
            stepOfIndex (globalIndex s j) = j) :
    Finset.sum (Finset.Icc 0 S)
        (fun s => ((activeEpochSteps s).card : ℝ)) =
      (N : ℝ) := by
  have hpart :=
    sum_outputWindow_eq_sum_activeEpochSteps
      (R := ℝ) (N := N) (S := S) (A := fun _k => (1 : ℝ))
      (activeEpochSteps := activeEpochSteps)
      (globalIndex := globalIndex)
      (epochOfIndex := epochOfIndex)
      (stepOfIndex := stepOfIndex)
      h_mem h_left_inv h_right_inv
  simpa [Finset.sum_const, nsmul_eq_mul] using hpart.symm

/-- Snake-case compatibility spelling for output-window active-epoch partition sums. -/
theorem sum_output_window_eq_sum_active_epoch_steps
    {R : Type*} [AddCommMonoid R]
    (N S : ℕ) (A : ℕ → R)
    (activeEpochSteps : ℕ → Finset ℕ)
    (globalIndex : ℕ → ℕ → ℕ)
    (epochOfIndex stepOfIndex : ℕ → ℕ)
    (h_mem :
      ∀ k ∈ Finset.Icc 1 N,
        epochOfIndex k ∈ Finset.Icc 0 S ∧
          stepOfIndex k ∈ activeEpochSteps (epochOfIndex k))
    (h_left_inv :
      ∀ k ∈ Finset.Icc 1 N,
        globalIndex (epochOfIndex k) (stepOfIndex k) = k)
    (h_right_inv :
      ∀ {s j : ℕ}, s ∈ Finset.Icc 0 S → j ∈ activeEpochSteps s →
        globalIndex s j ∈ Finset.Icc 1 N ∧
          epochOfIndex (globalIndex s j) = s ∧
            stepOfIndex (globalIndex s j) = j) :
    Finset.sum (Finset.Icc 1 N) A =
      Finset.sum (Finset.Icc 0 S)
        (fun s => Finset.sum (activeEpochSteps s)
          (fun j => A (globalIndex s j))) :=
  sum_outputWindow_eq_sum_activeEpochSteps
    (N := N) (S := S) (A := A) (activeEpochSteps := activeEpochSteps)
    (globalIndex := globalIndex) (epochOfIndex := epochOfIndex)
    (stepOfIndex := stepOfIndex) h_mem h_left_inv h_right_inv

/-- An active epoch coordinate maps to the one-based output window.

For any active-step family, if membership certifies that the coordinate lies in
the epoch window and the global-index encoder sends such certified coordinates
between `1` and `N`, then the encoded index belongs to `Finset.Icc 1 N`.

Layer: Model | Gap: Level 1 (active epoch output-window membership)
Proof: use the active-step membership proof to obtain an epoch-window
  certificate, feed that certificate to the encoder lower-bound hypothesis, and
  combine it with the active-step upper-bound hypothesis as `Finset.Icc`
  membership.
Source: Mathlib natural-number finite intervals and finset membership APIs
Used in: stochastic variance-reduced conditional-gradient active epoch
  reindexing into randomized-output windows
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem global_index_mem_output_window_of_mem_active_epoch_steps
    (N T : Nat)
    (globalIndex : Nat → Nat → Nat)
    (activeSteps : Nat → Finset Nat)
    (hactive_epoch :
      ∀ {s j : Nat}, j ∈ activeSteps s → 1 ≤ j ∧ j ≤ T)
    (hglobalIndex_pos_of_epoch :
      ∀ {s j : Nat}, 1 ≤ j ∧ j ≤ T → 1 ≤ globalIndex s j)
    (hglobalIndex_le_of_mem :
      ∀ {s j : Nat}, j ∈ activeSteps s → globalIndex s j ≤ N)
    {s j : Nat}
    (hj : j ∈ activeSteps s) :
    globalIndex s j ∈ Finset.Icc 1 N := by
  have hj_epoch : 1 ≤ j ∧ j ≤ T := hactive_epoch hj
  have hlow : 1 ≤ globalIndex s j := hglobalIndex_pos_of_epoch hj_epoch
  have hhigh : globalIndex s j ≤ N := hglobalIndex_le_of_mem hj
  exact Finset.mem_Icc.mpr ⟨hlow, hhigh⟩

/-- A decoded step coordinate from a global output index lies in its active epoch window.

For any active-step family characterized by valid within-epoch coordinates whose
global encoded index is within the run horizon, a decoded output-window index
belongs to the active window of its decoded epoch.

Layer: Model | Gap: Level 0 (decoded global-index active-window membership)
Proof: rewrite active-window membership by its characterization, use the
  decoded-step bound for the interval component, and rewrite the encoded global
  index by the decoder reconstruction law.
Source: Mathlib finite intervals, filtered finset membership, and natural-number
  quotient-remainder indexing APIs
Used in: stochastic variance-reduced conditional-gradient output-window
  reindexing by decoded epoch-step coordinates
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem stepOfGlobalIndex_mem_activeEpochSteps
    {T N : Nat}
    {globalIndex : Nat → Nat → Nat}
    {activeSteps : Nat → Finset Nat}
    {epochOfIndex stepOfIndex : Nat → Nat}
    (hactive :
      ∀ {s j : Nat}, j ∈ activeSteps s ↔
        j ∈ Finset.Icc 1 T ∧ globalIndex s j ≤ N)
    (hstep_mem_epoch :
      ∀ {k : Nat}, k ∈ Finset.Icc 1 N → stepOfIndex k ∈ Finset.Icc 1 T)
    (hglobalIndex_decode :
      ∀ {k : Nat}, k ∈ Finset.Icc 1 N →
        globalIndex (epochOfIndex k) (stepOfIndex k) = k)
    {k : Nat} (hk : k ∈ Finset.Icc 1 N) :
    stepOfIndex k ∈ activeSteps (epochOfIndex k) := by
  rw [hactive]
  exact ⟨hstep_mem_epoch hk, by
    rw [hglobalIndex_decode hk]
    exact (Finset.mem_Icc.mp hk).2⟩

/-- The epoch penalty formed by multiplying each active epoch weight mass by an
epochwise maximum.

For every epoch `s`, the inner finite sum gathers the weights attached to the
active epoch steps through a global index encoder, and the result is multiplied
by the supplied maximum bound `M s`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; nested active-epoch weight mass multiplied
  by an epochwise maximum sequence)
Source: finite epoch decompositions in stochastic variance-reduced first-order
  methods
Used in: stochastic conditional-gradient estimator-error absorption by an
  active epoch maximum
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
noncomputable def epochPenaltyWithMax
    (S : ℕ)
    (activeSteps : ℕ → Finset ℕ)
    (weight : ℕ → ℝ)
    (globalIndex : ℕ → ℕ → ℕ)
    (M : ℕ → ℝ) : ℝ :=
  Finset.sum (Finset.Icc 0 S)
    (fun s =>
      Finset.sum (activeSteps s)
        (fun j => weight (globalIndex s j)) * M s)

/-- The epoch penalty unfolds to the nested active-step sum times the supplied
epochwise maximum sequence.

Layer: Model | Gap: Level 0 (epoch penalty unfolding)
Proof: by rfl after unfolding `epochPenaltyWithMax`.
Source: Mathlib finite sums over natural intervals and active finite sets
Used in: stochastic conditional-gradient estimator-error absorption by an
  active epoch maximum
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
@[simp]
theorem epochPenaltyWithMax_def
    (S : ℕ)
    (activeSteps : ℕ → Finset ℕ)
    (weight : ℕ → ℝ)
    (globalIndex : ℕ → ℕ → ℕ)
    (M : ℕ → ℝ) :
    epochPenaltyWithMax S activeSteps weight globalIndex M =
      Finset.sum (Finset.Icc 0 S)
        (fun s =>
          Finset.sum (activeSteps s)
            (fun j => weight (globalIndex s j)) * M s) := by
  rfl


/-- Auxiliary accelerated point formed from a current search point and previous iterate.

At positive paper time `t`, the construction uses the regularized weights
`μ γ_t / (1 + μ γ_t)` and `1 / (1 + μ γ_t)` to blend the search point at `t`
with the raw iterate at predecessor index `t - 1`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; regularized two-point affine blend with
  positive-time predecessor indexing)
Source: accelerated stochastic approximation iterate notation and Mathlib
  module scalar multiplication APIs
Used in: accelerated stochastic gradient descent auxiliary plus-point before
  the one-step prox descent estimate
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/parameters/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
noncomputable def acceleratedAuxiliaryPoint
    {Ω E : Type*} [AddCommMonoid E] [SMul ℝ E]
    (mu : ℝ) (gamma : ℕ → ℝ)
    (xUnder : {n : ℕ // 1 ≤ n} → Ω → E)
    (xIter : ℕ → Ω → E)
    (t : {n : ℕ // 1 ≤ n}) (ω : Ω) : E :=
  (mu * gamma t.1 / (1 + mu * gamma t.1)) • xUnder t ω +
    (1 / (1 + mu * gamma t.1)) • xIter (t.1 - 1) ω

/-- The accelerated auxiliary point unfolds to its regularized affine blend.

Layer: Model | Gap: Level 0 (accelerated auxiliary point unfolding)
Proof: by rfl after unfolding `acceleratedAuxiliaryPoint`.
Source: accelerated stochastic approximation iterate notation and Mathlib
  module scalar multiplication APIs
Used in: accelerated stochastic gradient descent auxiliary plus-point formula
  for measurability and descent estimates
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/parameters/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
@[simp]
theorem acceleratedAuxiliaryPoint_def
    {Ω E : Type*} [AddCommMonoid E] [SMul ℝ E]
    (mu : ℝ) (gamma : ℕ → ℝ)
    (xUnder : {n : ℕ // 1 ≤ n} → Ω → E)
    (xIter : ℕ → Ω → E)
    (t : {n : ℕ // 1 ≤ n}) (ω : Ω) :
    acceleratedAuxiliaryPoint mu gamma xUnder xIter t ω =
      (mu * gamma t.1 / (1 + mu * gamma t.1)) • xUnder t ω +
        (1 / (1 + mu * gamma t.1)) • xIter (t.1 - 1) ω := by
  rfl

/-- The accelerated auxiliary point remains in any convex feasible set when
both component iterates are feasible and the two displayed weights are
nonnegative.

Layer: Model | Gap: Level 0 (convex feasibility of accelerated auxiliary point)
Proof: the two quotient weights add to one by the denominator witness, so
  convexity closes the displayed two-point blend.
Source: Mathlib convex-set API for nonnegative two-point affine combinations
Used in: accelerated stochastic gradient descent feasibility of the auxiliary
  plus-point before a prox descent estimate
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/parameters/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem acceleratedAuxiliaryPoint_mem_of_mem
    {Ω E : Type*} [AddCommMonoid E] [SMul ℝ E]
    {X : Set E} (hX : Convex ℝ X)
    (mu : ℝ) (gamma : ℕ → ℝ)
    (xUnder : {n : ℕ // 1 ≤ n} → Ω → E)
    (xIter : ℕ → Ω → E)
    (t : {n : ℕ // 1 ≤ n}) (ω : Ω)
    (hden_t : 1 + mu * gamma t.1 ≠ 0)
    (hleft_nonneg : 0 ≤ mu * gamma t.1 / (1 + mu * gamma t.1))
    (hright_nonneg : 0 ≤ 1 / (1 + mu * gamma t.1))
    (hxUnder : xUnder t ω ∈ X)
    (hxIter : xIter (t.1 - 1) ω ∈ X) :
    acceleratedAuxiliaryPoint mu gamma xUnder xIter t ω ∈ X := by
  have hweights_sum :
      mu * gamma t.1 / (1 + mu * gamma t.1) + 1 / (1 + mu * gamma t.1) = 1 := by
    field_simp [hden_t]
    ring
  simpa [acceleratedAuxiliaryPoint_def] using
    (convex_iff_add_mem.mp hX hxUnder hxIter hleft_nonneg hright_nonneg hweights_sum)

/-- Accelerated search point formed from the previous averaged iterate and
previous prox iterate.

At positive paper time `t`, this is the two-sequence extrapolated query
`(1 - q_t) • xBarPrev + q_t • xPrev`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; two-point affine blend for accelerated
  search queries)
Source: accelerated stochastic approximation iterate notation and Mathlib
  module scalar multiplication APIs
Used in: accelerated stochastic gradient descent search-query computation
  before the stochastic prox step
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
def acceleratedSearchPoint
    {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    (q : ℕ → ℝ) (t : {n : ℕ // 1 ≤ n})
    (xBarPrev xPrev : E) : E :=
  (1 - q t.1) • xBarPrev + q t.1 • xPrev

/-- The accelerated search point unfolds to its two-point affine blend.

Layer: Model | Gap: Level 0 (accelerated search-point unfolding)
Proof: by rfl after unfolding `acceleratedSearchPoint`.
Source: accelerated stochastic approximation iterate notation and Mathlib
  module scalar multiplication APIs
Used in: accelerated stochastic gradient descent search-query formula for
  feasibility, measurability, and descent estimates
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
@[simp]
theorem acceleratedSearchPoint_def
    {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    (q : ℕ → ℝ) (t : {n : ℕ // 1 ≤ n})
    (xBarPrev xPrev : E) :
    acceleratedSearchPoint q t xBarPrev xPrev =
      (1 - q t.1) • xBarPrev + q t.1 • xPrev := by
  rfl

/-- An accelerated search point stays in a convex feasible set.

If the previous averaged iterate and previous prox iterate are feasible, and
the search coefficient `q` lies in `[0,1]`, then the two-point affine blend
`(1 - q) • xBarPrev + q • xPrev` is feasible.

Layer: Model | Gap: Level 0 (accelerated search-point convex feasibility)
Proof: split `q ∈ [0,1]` into nonnegativity and upper-bound facts, build the
  two nonnegative convex weights, and close the affine blend by the two-point
  convex-combination membership characterization.
Source: Mathlib convex-set API for real affine combinations
Used in: accelerated stochastic gradient descent feasibility of the search
  query before stochastic oracle evaluation
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem acceleratedSearchPoint_mem
    {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    {X : Set E} (hX : Convex ℝ X)
    {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1)
    {xBarPrev xPrev : E}
    (hxBarPrev : xBarPrev ∈ X) (hxPrev : xPrev ∈ X) :
    (1 - q) • xBarPrev + q • xPrev ∈ X := by
  rcases Set.mem_Icc.mp hq with ⟨hq_nonneg, hq_le_one⟩
  exact convex_iff_add_mem.mp hX hxBarPrev hxPrev
    (sub_nonneg.mpr hq_le_one) hq_nonneg (by ring)

/-- The accelerated search point is measurable with respect to the strict-past
sigma-algebra when both previous iterates are.

This is the adaptedness closure for the two-sequence query
`(1 - q_t) • xBarPrev + q_t • xPrev` used by accelerated stochastic methods.

Layer: Model | Gap: Level 0 (accelerated search-point strict-past measurability)
Proof: unfold the named accelerated search point, then close measurability
  under deterministic scalar multiplication and addition.
Source: Mathlib measure-theory APIs for measurable addition and scalar
  multiplication in modules
Used in: accelerated stochastic gradient descent search-query adaptedness before
  stochastic-oracle martingale conditioning
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem acceleratedSearchPoint_strictPast_measurable
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [AddCommMonoid E] [SMul ℝ E] [MeasurableAdd₂ E] [MeasurableConstSMul ℝ E]
    (past : {n : ℕ // 1 ≤ n} → MeasurableSpace Ω)
    (q : ℕ → ℝ)
    (xBarPrev xPrev : {n : ℕ // 1 ≤ n} → Ω → E)
    (t : {n : ℕ // 1 ≤ n}) :
    Measurable[past t] (xBarPrev t) →
    Measurable[past t] (xPrev t) →
    Measurable[past t]
      (fun ω => acceleratedSearchPoint q t (xBarPrev t ω) (xPrev t ω)) := by
  intro hxBarPrev hxPrev
  simpa [acceleratedSearchPoint] using
    (hxBarPrev.const_smul (1 - q t.1)).add
      (hxPrev.const_smul (q t.1))

/-- The accelerated auxiliary point is strict-past measurable when its two
component iterates are.

This is the adaptedness closure for the regularized plus-point
`μ γ_t / (1 + μ γ_t) • xUnder_t + 1 / (1 + μ γ_t) • xIter_{t-1}` used by
accelerated stochastic methods.

Layer: Model | Gap: Level 0 (accelerated auxiliary-point strict-past measurability)
Proof: unfold the named accelerated auxiliary point, then close measurability
  under deterministic scalar multiplication and addition.
Source: Mathlib measure-theory APIs for measurable addition and scalar
  multiplication in modules
Used in: accelerated stochastic gradient descent auxiliary plus-point adaptedness
  before stochastic-oracle martingale conditioning
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/parameters/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem acceleratedAuxiliaryPoint_strictPast_measurable
    {Ω E : Type*} [MeasurableSpace E]
    [AddCommMonoid E] [SMul ℝ E] [MeasurableAdd₂ E] [MeasurableConstSMul ℝ E]
    (past : {n : ℕ // 1 ≤ n} → MeasurableSpace Ω)
    (mu : ℝ) (gamma : ℕ → ℝ)
    (xUnder : {n : ℕ // 1 ≤ n} → Ω → E)
    (xIter : ℕ → Ω → E)
    (t : {n : ℕ // 1 ≤ n}) :
    Measurable[past t] (xUnder t) →
    Measurable[past t] (xIter (t.1 - 1)) →
    Measurable[past t] (acceleratedAuxiliaryPoint mu gamma xUnder xIter t) := by
  intro hxUnder hxIter
  change Measurable[past t]
    (fun ω =>
      (mu * gamma t.1 / (1 + mu * gamma t.1)) • xUnder t ω +
        (1 / (1 + mu * gamma t.1)) • xIter (t.1 - 1) ω)
  simpa using
    (hxUnder.const_smul (mu * gamma t.1 / (1 + mu * gamma t.1))).add
      (hxIter.const_smul (1 / (1 + mu * gamma t.1)))

/-- Measurable sample-kernel execution interface for accelerated stochastic updates.

The structure records the schedule admissibility needed for accelerated
convex-combination updates together with a causal kernel
`(state, sample) ↦ next state` satisfying the chosen pointwise step predicate.

Layer: Model | Concept: Iterates
Proof: (definitional construction; bundled accelerated schedule admissibility
  plus measurable sample-indexed update kernel and pointwise step predicate)
Source: Stochastic approximation iterate kernels, Mathlib product
  measurability APIs, and accelerated first-order method schedules
Used in: stochastic accelerated gradient descent generated prox-step execution
  before composing the sample kernel with the realized sample stream
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
structure AcceleratedSampleKernelExecution
    {E Time State Sample : Type*}
    [MeasurableSpace E] [MeasurableSpace State] [MeasurableSpace Sample]
    (q alpha gamma : Time → ℝ)
    (stepPredicate : Time → State → Sample → E → Prop) where
  hq_mem_Icc :
    ∀ t : Time, q t ∈ Set.Icc (0 : ℝ) 1
  halpha_mem_Icc :
    ∀ t : Time, alpha t ∈ Set.Icc (0 : ℝ) 1
  hgamma_pos :
    ∀ t : Time, 0 < gamma t
  proxStepKernel :
    Time → State → Sample → E
  proxStepKernel_measurable :
    ∀ t : Time,
      Measurable (fun p : State × Sample => proxStepKernel t p.1 p.2)
  proxStepKernel_spec :
    ∀ (t : Time) (prev : State) (ξ : Sample),
      stepPredicate t prev ξ (proxStepKernel t prev ξ)

/-- Output-coordinate view of a recursive stochastic state process.

For a state-valued process `process` and a coordinate accessor `output`, this
names the random output at time `t` as the samplewise coordinate
`ω ↦ output (process t ω)`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; state-coordinate projection of a time-indexed
  stochastic process)
Source: stochastic approximation iterate-process notation and Mathlib
  Pi-function evaluation APIs
Used in: stochastic accelerated gradient descent generated averaged-output
  coordinate of the recursive state process
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
noncomputable def recursiveProcessOutput
    {Ω T State E : Type*}
    (process : T → Ω → State) (output : State → E) (t : T) (ω : Ω) : E :=
  output (process t ω)

/-- The output-coordinate view unfolds to applying the coordinate accessor to
the recursive state at the selected time and sample.

Layer: Model | Gap: Level 0 (recursive process output-coordinate unfolding)
Proof: by rfl after unfolding `recursiveProcessOutput`.
Source: Mathlib Pi-function application and definitional unfolding APIs
Used in: stochastic accelerated gradient descent rewriting generated output to
  the averaged-coordinate field of the recursive process
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
@[simp]
theorem recursiveProcessOutput_eq
    {Ω T State E : Type*}
    (process : T → Ω → State) (output : State → E) (t : T) (ω : Ω) :
    recursiveProcessOutput process output t ω = output (process t ω) := by
  rfl

/-- A measurable state-process slice has a measurable output coordinate.

If the selected process state `process t` is measurable with respect to a
source sigma-algebra `mSource`, that sigma-algebra is below a target
sigma-algebra `mTarget`, and `out` is a measurable state-output map, then the
public output `ω ↦ out (process t ω)` is measurable with respect to the target
sigma-algebra.

Layer: Model | Gap: Level 1 (process output-coordinate measurability)
Proof: first promote the selected process slice from the source sigma-algebra
  to ambient measurability using monotonicity, then compose with the measurable
  state-output map.
Source: Mathlib measure-theory APIs for measurable-space monotonicity and
  measurable function composition
Used in: stochastic accelerated gradient descent generated averaged-output
  measurability after recursive-state prefix measurability
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem processOutput_measurable_of_process_measurable
    {Ω State Output T : Type*} [MeasurableSpace State] [MeasurableSpace Output]
    (mSource mTarget : MeasurableSpace Ω)
    (process : T → Ω → State) (out : State → Output) (t : T)
    (hm_le : mSource ≤ mTarget)
    (hprocess : @Measurable Ω State mSource inferInstance (process t))
    (hout : Measurable out) :
    @Measurable Ω Output mTarget inferInstance (fun ω => out (process t ω)) := by
  exact hout.comp (hprocess.mono hm_le le_rfl)

end SOptLib

namespace SOptLib

/-- Coordinate gradient-memory agreement on a feasible carrier.

For each coordinate `i`, the stored memory value `yMem i` is the selected
component gradient at the feasible stored point `xMem i`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; pointwise table-gradient agreement on a
  carrier-valued memory table)
Source: Mathlib subtype, Set membership, and Pi-function equality APIs
Used in: randomized accelerated proximal-point and variance-reduced
  table-gradient memory initialization
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
def coordinateGradientMemoryMatches
    {ι E : Type*} {X : Set E}
    (grad : ι → {x : E // x ∈ X} → E)
    (xMem yMem : ι → E) (hxMem : ∀ i, xMem i ∈ X) : Prop :=
  ∀ i : ι, yMem i = grad i ⟨xMem i, hxMem i⟩

/-- Coordinate gradient-memory agreement unfolds to pointwise equality with
the component gradient evaluated at each feasible stored point.

Layer: Model | Gap: Level 0 (coordinate gradient-memory unfolding)
Proof: by rfl after unfolding `coordinateGradientMemoryMatches`.
Source: Mathlib subtype, Set membership, and Pi-function equality APIs
Used in: randomized accelerated proximal-point and variance-reduced
  table-gradient memory initialization
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
@[simp] theorem coordinateGradientMemoryMatches_def
    {ι E : Type*} {X : Set E}
    (grad : ι → {x : E // x ∈ X} → E)
    (xMem yMem : ι → E) (hxMem : ∀ i, xMem i ∈ X) :
    coordinateGradientMemoryMatches grad xMem yMem hxMem =
      (∀ i : ι, yMem i = grad i ⟨xMem i, hxMem i⟩) :=
  rfl

/-- Build coordinate gradient-memory agreement from the pointwise memory
equality.

Layer: Model | Gap: Level 0 (coordinate gradient-memory introduction)
Proof: direct use of the defining pointwise predicate.
Source: Mathlib subtype, Set membership, and Pi-function equality APIs
Used in: randomized accelerated proximal-point and variance-reduced
  table-gradient memory initialization -/
theorem coordinateGradientMemoryMatches_intro
    {ι E : Type*} {X : Set E}
    {grad : ι → {x : E // x ∈ X} → E}
    {xMem yMem : ι → E} {hxMem : ∀ i, xMem i ∈ X}
    (h : ∀ i : ι, yMem i = grad i ⟨xMem i, hxMem i⟩) :
    coordinateGradientMemoryMatches grad xMem yMem hxMem :=
  h

/-- Access the stored-gradient equality at a coordinate from coordinate
gradient-memory agreement.

Layer: Model | Gap: Level 0 (coordinate gradient-memory accessor)
Proof: direct application of the defining pointwise predicate.
Source: Mathlib subtype, Set membership, and Pi-function equality APIs
Used in: randomized accelerated proximal-point and variance-reduced
  table-gradient memory initialization -/
theorem coordinateGradientMemoryMatches_apply
    {ι E : Type*} {X : Set E}
    {grad : ι → {x : E // x ∈ X} → E}
    {xMem yMem : ι → E} {hxMem : ∀ i, xMem i ∈ X}
    (h : coordinateGradientMemoryMatches grad xMem yMem hxMem) (i : ι) :
    yMem i = grad i ⟨xMem i, hxMem i⟩ :=
  h i

/-- A total previous-iterate selector uses the initial point at time zero and the prior iterate at successors.

For a zero-based process `x`, `previousIterateOrInitial x0 x` is the time-indexed
center process whose zeroth value is the constant initial point and whose value
at `t + 1` is the iterate generated at time `t`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; natural-number predecessor dispatch with a constant initial value)
Source: Mathlib natural-number recursion and Pi-function APIs
Used in: randomized accelerated proximal-point generated subproblem centers from previous outer iterates
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  randomized accelerated proximal-point method -/
def previousIterateOrInitial {Ω E : Type*} (x0 : E) (x : ℕ → Ω → E) : ℕ → Ω → E
  | 0 => fun _ => x0
  | t + 1 => x t

/-- The total previous-iterate selector is the natural-number split between the
initial point and predecessor iterates.

Layer: Model | Gap: Level 0 (previous-iterate selector unfolding)
Proof: by rfl after unfolding previousIterateOrInitial
Source: Mathlib natural-number recursion and Pi-function APIs
Used in: randomized accelerated proximal-point generated subproblem centers from previous outer iterates -/
@[simp]
theorem previousIterateOrInitial_def {Ω E : Type*} (x0 : E) (x : ℕ → Ω → E) :
    previousIterateOrInitial x0 x =
      fun
        | 0 => fun _ : Ω => x0
        | t + 1 => x t := by
  rfl

/-- The total previous-iterate selector starts from the constant initial point.

Layer: Model | Gap: Level 0 (previous-iterate selector initialization)
Proof: by rfl after unfolding previousIterateOrInitial
Source: Mathlib natural-number recursion and Pi-function APIs
Used in: randomized accelerated proximal-point first generated subproblem center
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  randomized accelerated proximal-point method -/
@[simp]
theorem previousIterateOrInitial_zero {Ω E : Type*} (x0 : E) (x : ℕ → Ω → E) :
    previousIterateOrInitial x0 x 0 = fun _ : Ω => x0 := by
  rfl

/-- At successor time, the total previous-iterate selector returns the prior iterate.

Layer: Model | Gap: Level 0 (previous-iterate selector successor)
Proof: by rfl after unfolding previousIterateOrInitial
Source: Mathlib natural-number recursion and Pi-function APIs
Used in: randomized accelerated proximal-point generated subproblem center recursion
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  randomized accelerated proximal-point method -/
@[simp]
theorem previousIterateOrInitial_succ {Ω E : Type*} (x0 : E) (x : ℕ → Ω → E)
    (t : ℕ) :
    previousIterateOrInitial x0 x (t + 1) = x t := by
  rfl

/-- A previous-iterate selector preserves membership in a carrier set.

If the initial point and every generated iterate belong to `X`, then the selected
previous center belongs to `X` at every time and sample.

Layer: Model | Gap: Level 0 (previous-iterate selector carrier membership)
Proof: split on the natural time index; the zero case uses the initial-point
  membership and the successor case uses iterate membership at the predecessor.
Source: Mathlib natural-number recursion, Set membership, and simplifier APIs
Used in: proximal-point and Catalyst-style subproblem centers restricted to a
  feasible carrier -/
theorem previousIterateOrInitial_mem {Ω E : Type*} {X : Set E}
    (x0 : E) (x : ℕ → Ω → E)
    (hx0 : x0 ∈ X)
    (hx : ∀ t ω, x t ω ∈ X)
    (t : ℕ) (ω : Ω) :
    previousIterateOrInitial x0 x t ω ∈ X := by
  cases t with
  | zero =>
      simpa using hx0
  | succ t =>
      simpa using hx t ω

/-- Average squared distance of a finite memory table from a center.

This names the finite-population dispersion
`(card ι)⁻¹ * ∑ i, ‖mem i - center‖ ^ 2` used when component memories are
compared with a current iterate or reference point.

Layer: Model | Concept: Iterates
Proof: (definitional construction; inverse-cardinality scalar multiplying the
  finite sum of squared norm distances from a center)
Source: Mathlib finite sums and normed additive-group squared-distance calculus
Used in: randomized accelerated proximal-point outer component-memory dispersion
  and variance-reduced finite-sum memory-table estimates
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
noncomputable def finiteMemoryDispersion {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] (mem : ι → E) (center : E) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ *
    Finset.sum Finset.univ (fun i => ‖mem i - center‖ ^ 2)

/-- Finite memory dispersion unfolds to the inverse-cardinality average of squared
distances from the center.

Layer: Model | Gap: Level 0 (finite memory dispersion unfolding)
Proof: by rfl after unfolding `finiteMemoryDispersion`.
Source: Mathlib finite sums and normed additive-group squared-distance calculus
Used in: randomized accelerated proximal-point outer component-memory dispersion
  and variance-reduced finite-sum memory-table estimates
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
@[simp] theorem finiteMemoryDispersion_def {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] (mem : ι → E) (center : E) :
    finiteMemoryDispersion mem center =
      (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ (fun i => ‖mem i - center‖ ^ 2) :=
  rfl

/-- Finite memory dispersion is nonnegative.

Layer: Model | Gap: Level 0 (finite memory dispersion nonnegativity)
Proof: the inverse cardinality factor and each squared norm summand are
  nonnegative.
Source: Mathlib finite sums and ordered-ring nonnegativity
Used in: variance-reduced finite-sum memory-table estimates -/
theorem finiteMemoryDispersion_nonneg {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] (mem : ι → E) (center : E) :
    0 ≤ finiteMemoryDispersion mem center := by
  rw [finiteMemoryDispersion_def]
  exact mul_nonneg
    (inv_nonneg.mpr (by exact_mod_cast Nat.zero_le (Fintype.card ι)))
    (Finset.sum_nonneg fun i _ => sq_nonneg ‖mem i - center‖)

/-- If every memory entry equals the center, finite memory dispersion is zero.

Layer: Model | Gap: Level 0 (finite memory dispersion zero case)
Proof: all squared-distance summands vanish.
Source: Mathlib finite sums and normed additive-group simplification
Used in: variance-reduced finite-sum memory-table estimates -/
@[simp] theorem finiteMemoryDispersion_eq_zero_of_forall_eq {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] (mem : ι → E) (center : E)
    (hmem : ∀ i, mem i = center) :
    finiteMemoryDispersion mem center = 0 := by
  rw [finiteMemoryDispersion_def]
  simp [hmem]

/-- The relaxed refreshed point between a proposal and stale memory value.

This is the point `(1 + tau)⁻¹ • (proposal + tau • memory)` used before a
component memory table is updated or before a refreshed component model is
evaluated.

Layer: Model | Concept: Iterates
Proof: (definitional construction; regularized affine memory-refresh point)
Source: Mathlib module scalar multiplication and additive expression APIs
Used in: randomized accelerated proximal-point component-memory refresh and
  variance-reduced finite-sum memory updates
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
noncomputable def relaxedMemoryRefreshPoint {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    (tau : ℝ) (proposal memory : E) : E :=
  ((1 : ℝ) + tau)⁻¹ • (proposal + tau • memory)

/-- The relaxed refreshed point unfolds to its regularized affine formula.

Layer: Model | Gap: Level 0 (relaxed memory-refresh point unfolding)
Proof: by rfl after unfolding `relaxedMemoryRefreshPoint`.
Source: Mathlib module scalar multiplication and additive expression APIs
Used in: randomized accelerated proximal-point component-memory refresh and
  variance-reduced finite-sum memory updates
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
@[simp]
theorem relaxedMemoryRefreshPoint_def {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    (tau : ℝ) (proposal memory : E) :
    relaxedMemoryRefreshPoint tau proposal memory =
      ((1 : ℝ) + tau)⁻¹ • (proposal + tau • memory) := by
  rfl

/-- A relaxed memory refresh stays in a convex feasible set.

If the proposal and stale memory are feasible and the relaxation parameter is
nonnegative, then the refreshed point is feasible.  The proof rewrites the
regularized form as the convex combination with weights `(1 + tau)⁻¹` and
`(1 + tau)⁻¹ * tau`.

Layer: Model | Gap: Level 0 (relaxed memory-refresh convex feasibility)
Proof: express the refresh as a two-point convex combination and apply
  `convex_iff_add_mem`.
Source: Mathlib convex-set API for real affine combinations
Used in: randomized accelerated proximal-point and variance-reduced memory
  refreshes over convex feasible domains
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem relaxedMemoryRefreshPoint_mem_of_convex {E : Type*}
    [AddCommMonoid E] [Module ℝ E]
    {X : Set E} (hX : Convex ℝ X) {tau : ℝ} (htau : 0 ≤ tau)
    {proposal memory : E} (hproposal : proposal ∈ X) (hmemory : memory ∈ X) :
    relaxedMemoryRefreshPoint tau proposal memory ∈ X := by
  have hden_nonneg : 0 ≤ (1 : ℝ) + tau := add_nonneg zero_le_one htau
  have hden_pos : 0 < (1 : ℝ) + tau := by positivity
  have hleft_nonneg : 0 ≤ ((1 : ℝ) + tau)⁻¹ := inv_nonneg.mpr hden_nonneg
  have hright_nonneg : 0 ≤ ((1 : ℝ) + tau)⁻¹ * tau :=
    mul_nonneg hleft_nonneg htau
  have hweights_sum :
      ((1 : ℝ) + tau)⁻¹ + ((1 : ℝ) + tau)⁻¹ * tau = 1 := by
    field_simp [hden_pos.ne']
  simpa [relaxedMemoryRefreshPoint_def, smul_add, smul_smul, mul_assoc] using
    (convex_iff_add_mem.mp hX hproposal hmemory hleft_nonneg hright_nonneg hweights_sum)

/-- Refresh one sampled memory component by a regularized affine blend.

The selected coordinate is replaced by
`(1 + tau)⁻¹ • (center + tau • mem i)`, while every non-selected coordinate
keeps its previous memory value.

Layer: Model | Concept: Iterates
Proof: (definitional construction; Mathlib `Function.update` applied to the
  selected affine memory value)
Source: Mathlib coordinate-update API and module scalar multiplication
Used in: randomized accelerated proximal-point sampled component-memory update
  and variance-reduced finite-sum memory refreshes
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
noncomputable def sampledAffineMemoryRefresh {ι E : Type*} [DecidableEq ι]
    [AddCommMonoid E] [SMul ℝ E]
    (tau : ℝ) (center : E) (mem : ι → E) (sample i : ι) : E :=
  Function.update mem sample (((1 : ℝ) + tau)⁻¹ • (center + tau • mem sample)) i

/-- A sampled affine memory refresh unfolds to the selected/non-selected cases.

Layer: Model | Gap: Level 0 (sampled affine memory refresh unfolding)
Proof: unfold `sampledAffineMemoryRefresh`, split on whether the queried
  coordinate is sampled, and simplify `Function.update`.
Source: Mathlib `Function.update_apply` and module scalar multiplication
Used in: randomized accelerated proximal-point sampled component-memory update
  and variance-reduced finite-sum memory refreshes
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
@[simp]
theorem sampledAffineMemoryRefresh_def {ι E : Type*} [DecidableEq ι]
    [AddCommMonoid E] [SMul ℝ E]
    (tau : ℝ) (center : E) (mem : ι → E) (sample i : ι) :
    sampledAffineMemoryRefresh tau center mem sample i =
      if i = sample then
        ((1 : ℝ) + tau)⁻¹ • (center + tau • mem i)
      else mem i := by
  by_cases h : i = sample
  · subst i
    simp [sampledAffineMemoryRefresh]
  · simp [sampledAffineMemoryRefresh, h]

/-- The sampled coordinate of an affine memory refresh is the affine blend of the
center and the previous sampled memory.

Layer: Model | Gap: Level 0 (sampled affine memory selected coordinate)
Proof: unfold `sampledAffineMemoryRefresh` and simplify the selected coordinate
  of `Function.update`.
Source: Mathlib `Function.update` selected-coordinate simplification
Used in: randomized accelerated proximal-point sampled component-memory affine
  rearrangement
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
@[simp]
theorem sampledAffineMemoryRefresh_self {ι E : Type*} [DecidableEq ι]
    [AddCommMonoid E] [SMul ℝ E]
    (tau : ℝ) (center : E) (mem : ι → E) (sample : ι) :
    sampledAffineMemoryRefresh tau center mem sample sample =
      ((1 : ℝ) + tau)⁻¹ • (center + tau • mem sample) := by
  simp [sampledAffineMemoryRefresh]

/-- Non-sampled coordinates of an affine memory refresh are unchanged.

Layer: Model | Gap: Level 0 (sampled affine memory stale-coordinate preservation)
Proof: unfold `sampledAffineMemoryRefresh` and simplify `Function.update` at a
  coordinate different from the sampled one.
Source: Mathlib `Function.update_of_ne`
Used in: randomized accelerated proximal-point preservation of stale component
  memories after a sampled refresh
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem sampledAffineMemoryRefresh_of_ne {ι E : Type*} [DecidableEq ι]
    [AddCommMonoid E] [SMul ℝ E]
    (tau : ℝ) (center : E) (mem : ι → E) {sample i : ι}
    (hi : i ≠ sample) :
    sampledAffineMemoryRefresh tau center mem sample i = mem i := by
  simp [sampledAffineMemoryRefresh, hi]

/-- Momentum extrapolation from a current point and its previous point.

For a real coefficient `alpha`, `extrapolatedPoint alpha x xPrev` is the
accelerated query point `alpha • (x - xPrev) + x`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; real-scalar momentum displacement added to
  the current iterate)
Source: accelerated-method iterate notation and Mathlib module scalar
  multiplication APIs
Used in: randomized accelerated proximal-point extrapolated query before sampled
  component refreshes and Catalyst-style inner-loop oracle calls
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
def extrapolatedPoint {E : Type*} [AddCommGroup E] [Module ℝ E]
    (alpha : ℝ) (x xPrev : E) : E :=
  alpha • (x - xPrev) + x

/-- The extrapolated point unfolds to the momentum displacement formula.

Layer: Model | Gap: Level 0 (extrapolated-point unfolding)
Proof: by rfl after unfolding `extrapolatedPoint`.
Source: Mathlib module scalar multiplication and additive-group APIs
Used in: randomized accelerated proximal-point extrapolated query before sampled
  component refreshes and Catalyst-style inner-loop oracle calls
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
@[simp]
theorem extrapolatedPoint_def {E : Type*} [AddCommGroup E] [Module ℝ E]
    (alpha : ℝ) (x xPrev : E) :
    extrapolatedPoint alpha x xPrev = alpha • (x - xPrev) + x := by
  rfl

/-- The displacement from the current point to the extrapolated point is exactly
the scaled previous-step displacement.

Layer: Model | Gap: Level 0 (extrapolated-point displacement)
Proof: unfold `extrapolatedPoint` and cancel the current iterate.
Source: Mathlib additive-group and module APIs
Used in: converting accelerated extrapolation formulas into affine-relation
  hypotheses for one-step descent and estimator identities
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
@[simp]
theorem extrapolatedPoint_sub_current {E : Type*} [AddCommGroup E] [Module ℝ E]
    (alpha : ℝ) (x xPrev : E) :
    extrapolatedPoint alpha x xPrev - x = alpha • (x - xPrev) := by
  simp [extrapolatedPoint]

-- Generalization plan (G0):
-- concept/name: recursive process determinism from a finite driver prefix; orig was
--   ambientFixedInnerProcess_prefix_const, renamed away from ambient fixed-run and
--   paper setup terminology
-- generality used: arbitrary sample space, driver value type, state type,
--   Nat-indexed driver stream, bounded process, and successor congruence under
--   previous-state and current-driver equality; no measure, filtration,
--   topology, convexity, smoothness, or oracle assumptions
-- portable call pattern: recursive stochastic algorithms prove that a generated
--   state at time `t` factors through the first `t` driver samples; the state
--   type, sample type, transition rule, offset, and finite horizon change while
--   the prefix-determinism conclusion stays fixed
-- counterargument checked: not paper-local traceability and not a pure wrapper,
--   because the induction is the reusable factor-through-prefix step for any
--   bounded sample-driven recursion, including proof-dependent transitions;
--   existing recursive-process APIs cover
--   construction, successor unfolding, and measurability, but not equality from
--   equal finite driver windows
-- coverage search: searched SOptLib catalog/symbols for recursive process,
--   prefix const, driver prefix, factor through prefix, sampleWindow, and
--   process prefix equality; LeanSearch for "recursive process equal if driver
--   prefix equal" returned only generic Nat recursion congruence lemmas, so
--   coverage is partial and this statement is genuinely different
-- minimal hypotheses: all already minimal; the proof needs only constant
--   initialization, bounded successor congruence, and equality of the named
--   finite driver window

/-- A sample-driven recursive process is determined by its finite driver prefix.

If a process starts from a constant initial state and its successor map respects
equality of the previous state and current driver sample, then equal length-`t`
driver windows force equal time-`t` process states.

Layer: Layer1 | Gap: Level 1 (recursive process finite-prefix determinism)
Proof: induction on the recursion time. The successor case restricts the window
  equality to the previous prefix and reads the final coordinate, then rewrites
  both bounded successor equations.
Source: Mathlib natural-number induction, Fin-indexed Pi-function extensionality,
  and primitive recursive process APIs
Used in: randomized accelerated proximal-point fixed inner-loop finite-prefix
  state determinism for integrability and measurability reductions
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem recursive_process_eq_of_driver_prefix_eq
    {Ω S State : Type*}
    (ξ : ℕ → Ω → S)
    (process : ℕ → Ω → State)
    (offset R t : ℕ)
    (initial : State)
    (h_zero : ∀ ω : Ω, process 0 ω = initial)
    (h_succ_congr :
      ∀ n, n + 1 ≤ R → ∀ ⦃ω ω' : Ω⦄,
        process n ω = process n ω' →
        ξ (offset + n) ω = ξ (offset + n) ω' →
        process (n + 1) ω = process (n + 1) ω')
    (ht : t ≤ R) :
    ∀ ⦃ω ω' : Ω⦄,
      sampleWindow ξ offset t ω = sampleWindow ξ offset t ω' →
      process t ω = process t ω' := by
  induction t with
  | zero =>
      intro ω ω' _hprefix
      rw [h_zero ω, h_zero ω']
  | succ n ih =>
      intro ω ω' hprefix
      have hn : n ≤ R := Nat.le_of_succ_le ht
      have hprefix_prev :
          sampleWindow ξ offset n ω = sampleWindow ξ offset n ω' := by
        funext r
        exact congrFun hprefix ⟨r.1, Nat.lt_trans r.2 (Nat.lt_succ_self n)⟩
      have hprev : process n ω = process n ω' := ih hn hprefix_prev
      have hsample : ξ (offset + n) ω = ξ (offset + n) ω' := by
        exact congrFun hprefix ⟨n, Nat.lt_succ_self n⟩
      exact h_succ_congr n ht hprev hsample

-- Generalization plan (G0):
-- concept/name: recursive process terminal-state equality from equal finite
--   driver windows at possibly different stream offsets; orig was
--   ambientFixedInnerProcess_eq_of_samplePrefix_eq_offsets, renamed away from
--   ambient fixed-run and paper setup terminology
-- generality used: arbitrary sample space, driver value type, state type,
--   Nat-indexed driver stream, offset-indexed bounded process, and successor
--   congruence under previous-state and current-driver equality; no measure,
--   filtration, topology, convexity, smoothness, or oracle assumptions
-- portable call pattern: coupling and law-transport proofs instantiate two
--   offsets into an iid sample stream and reuse the same recursive transition;
--   the state type, sample type, horizon, offsets, and successor equations vary
--   while the conclusion remains equality of terminal states under equal
--   driver windows
-- counterargument checked: not paper-local traceability and not a pure wrapper,
--   because cross-offset equality is the reusable induction needed after
--   replacing one sample block by an equal block elsewhere in a stochastic
--   stream; the existing same-offset prefix theorem is related but cannot
--   compare two different offset-indexed runs
-- coverage search: searched CATALOG/SOptLib/project for recursive process,
--   driver prefix/window, offsets, sampleWindow, and prefix equality; top hits
--   were recursive_process_eq_of_driver_prefix_eq, sampleWindow laws, and
--   recursiveProcess_succ_eq_sample_update, which provide same-offset
--   determinism or successor bridges but not cross-offset terminal equality
-- minimal hypotheses: all already minimal for proof-dependent bounded
--   recursions; an explicit step-function formulation would not cover local
--   transitions whose Lean definitions carry state-dependent proof arguments

/-- Two offset-indexed runs of a sample-driven recursion agree when their driver windows agree.

If all runs start from the same initial state and the successor equation is
congruent under equality of the previous state and current driver sample, then
equal length-`t` driver windows at offsets `offset` and `offset'` force equality
of the two time-`t` states.

Layer: Layer1 | Gap: Level 1 (recursive process cross-offset window determinism)
Proof: induction on the recursion time. The successor case restricts the window
  equality to the previous prefix and reads the final coordinate, then applies
  the supplied successor congruence.
Source: Mathlib natural-number induction, Fin-indexed Pi-function extensionality,
  and primitive recursive process APIs
Used in: randomized accelerated proximal-point fixed inner-loop sample-block
  coupling for law transport between generated and reference runs
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem recursiveProcess_eq_of_driverWindow_eq_offsets
    {Ω S State : Type*}
    (ξ : ℕ → Ω → S)
    (process : ℕ → ℕ → Ω → State)
    (offset offset' R t : ℕ)
    (initial : State)
    (h_zero : ∀ offset ω, process offset 0 ω = initial)
    (h_succ_congr :
      ∀ offset offset' n, n + 1 ≤ R → ∀ ⦃ω ω' : Ω⦄,
        process offset n ω = process offset' n ω' →
        ξ (offset + n) ω = ξ (offset' + n) ω' →
        process offset (n + 1) ω = process offset' (n + 1) ω')
    (ht : t ≤ R) :
    ∀ ⦃ω ω' : Ω⦄,
      sampleWindow ξ offset t ω = sampleWindow ξ offset' t ω' →
      process offset t ω = process offset' t ω' := by
  induction t with
  | zero =>
      intro ω ω' _hprefix
      rw [h_zero offset ω, h_zero offset' ω']
  | succ n ih =>
      intro ω ω' hprefix
      have hn : n ≤ R := Nat.le_of_succ_le ht
      have hprefix_prev :
          sampleWindow ξ offset n ω = sampleWindow ξ offset' n ω' := by
        funext r
        exact congrFun hprefix ⟨r.1, Nat.lt_trans r.2 (Nat.lt_succ_self n)⟩
      have hprev : process offset n ω = process offset' n ω' := ih hn hprefix_prev
      have hsample : ξ (offset + n) ω = ξ (offset' + n) ω' := by
        exact congrFun hprefix ⟨n, Nat.lt_succ_self n⟩
      exact h_succ_congr offset offset' n ht hprev hsample

/-- A stochastic process satisfies a relation-valued recursion from a fixed initial state.

The predicate records a constant initial time slice and a time-indexed successor
relation for every sample.  The relation may be nondeterministic or partial,
which makes it suitable for algorithms whose update step is specified by a
selection relation rather than a total function.

Layer: Model | Concept: Iterates
Proof: (definitional construction; conjunction of the initial slice condition
  and the pointwise successor relation)
Source: Mathlib relation-valued transition systems and natural-number process
  indexing
Used in: stochastic conditional-gradient sliding generated outer-state process
  with a relation-valued conditional-gradient subroutine
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
def IsRelationalRecursiveProcess
    {Omega State : Type*}
    (initial : State)
    (rel : Nat -> State -> State -> Omega -> Prop)
    (state : Nat -> Omega -> State) : Prop :=
  (forall omega, state 0 omega = initial) /\
    forall k omega, rel k (state k omega) (state (k + 1) omega) omega

/-- The relational recursive-process predicate is the conjunction of the initial
slice equation and the step relation.

Layer: Model | Gap: Level 0 (relational recursive-process definition)
Proof: by rfl after unfolding `IsRelationalRecursiveProcess`.
Source: Mathlib propositional equality and natural-number process indexing APIs
Used in: stochastic conditional-gradient sliding generated outer-state process
  with a relation-valued conditional-gradient subroutine
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
@[simp]
theorem isRelationalRecursiveProcess_def
    {Omega State : Type*}
    (initial : State)
    (rel : Nat -> State -> State -> Omega -> Prop)
    (state : Nat -> Omega -> State) :
    IsRelationalRecursiveProcess initial rel state =
      ((forall omega, state 0 omega = initial) /\
        forall k omega, rel k (state k omega) (state (k + 1) omega) omega) := by
  rfl

/-- The relational recursive-process predicate unfolds to its initial and step clauses.

Layer: Model | Gap: Level 0 (relational recursive-process unfolding)
Proof: by rfl after unfolding `IsRelationalRecursiveProcess`.
Source: Mathlib propositional equivalence and natural-number process indexing APIs
Used in: stochastic conditional-gradient sliding generated outer-state process
  with a relation-valued conditional-gradient subroutine
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
@[simp]
theorem isRelationalRecursiveProcess_iff
    {Omega State : Type*}
    (initial : State)
    (rel : Nat -> State -> State -> Omega -> Prop)
    (state : Nat -> Omega -> State) :
    IsRelationalRecursiveProcess initial rel state <->
      (forall omega, state 0 omega = initial) /\
        forall k omega, rel k (state k omega) (state (k + 1) omega) omega := by
  rfl

/-- The initial time slice of a relational recursive process is constant.

Layer: Model | Gap: Level 0 (relational recursive-process initial projection)
Proof: projection from `IsRelationalRecursiveProcess`.
Source: Mathlib conjunction projection and natural-number process indexing APIs
Used in: stochastic conditional-gradient sliding generated outer-state process
  with a relation-valued conditional-gradient subroutine
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem IsRelationalRecursiveProcess.initial
    {Omega State : Type*}
    {initial : State}
    {rel : Nat -> State -> State -> Omega -> Prop}
    {state : Nat -> Omega -> State}
    (hstate : IsRelationalRecursiveProcess initial rel state) (omega : Omega) :
    state 0 omega = initial :=
  hstate.1 omega

/-- Each successor time slice of a relational recursive process satisfies its
step relation.

Layer: Model | Gap: Level 0 (relational recursive-process step projection)
Proof: projection from `IsRelationalRecursiveProcess`.
Source: Mathlib conjunction projection and natural-number process indexing APIs
Used in: stochastic conditional-gradient sliding generated outer-state process
  with a relation-valued conditional-gradient subroutine
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem IsRelationalRecursiveProcess.step
    {Omega State : Type*}
    {initial : State}
    {rel : Nat -> State -> State -> Omega -> Prop}
    {state : Nat -> Omega -> State}
    (hstate : IsRelationalRecursiveProcess initial rel state) (k : Nat) (omega : Omega) :
    rel k (state k omega) (state (k + 1) omega) omega :=
  hstate.2 k omega

/-- A functional recursive iterate process is a relational recursive process for
the graph of its step function.

Layer: Model | Gap: Level 1 (functional-to-relational recursive process bridge)
Proof: combine `recursiveIterateProcess_zero` and `recursiveIterateProcess_succ`.
Source: SOptLib functional recursive process API and Mathlib graph-relation idiom
Used in: stochastic conditional-gradient sliding generated outer-state process
  with a relation-valued conditional-gradient subroutine
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem isRelationalRecursiveProcess_of_recursiveIterateProcess
    {Omega State : Type*}
    (process : Nat -> Omega -> State)
    (initial : State)
    (step : Nat -> State -> Omega -> State)
    (h_process : process = recursiveIterateProcess initial step) :
    IsRelationalRecursiveProcess initial
      (fun k prev next omega => next = step k prev omega) process := by
  constructor
  · intro omega
    exact recursiveIterateProcess_zero process initial step h_process omega
  · intro k omega
    exact recursiveIterateProcess_succ process initial step h_process k omega

/-- A stopped recursion agrees with its raw always-step recursion before any
previous stopped state satisfies the stopping predicate.

The statement is relational: callers provide the two recurrence laws, so the
lemma applies to existing recursive definitions without forcing a particular
library definition of raw or stopped iterates.

Layer: Model | Gap: Level 1 (stopped-recursion prefix agreement)
Proof: induction on the natural-number counter; at successors, the no-stop
  hypothesis selects the stepping branch and the induction hypothesis rewrites
  the previous stopped state to the raw state.
Source: Mathlib natural-number recursion, decidable if-then-else, and equality
  rewriting APIs
Used in: stochastic conditional-gradient sliding CndG inner-loop transfer from
  the early-stopping implementation to the raw deterministic iteration analyzed
  by the inner-loop bound
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem stopped_iterate_eq_raw_of_no_stop_lt
    {State : Type*}
    (step : State → State)
    (stop : State → Prop) [DecidablePred stop]
    (stopped raw : ℕ → State)
    (h_zero : stopped 0 = raw 0)
    (h_stopped_succ :
      ∀ n : ℕ, stopped (n + 1) =
        if stop (stopped n) then stopped n else step (stopped n))
    (h_raw_succ :
      ∀ n : ℕ, raw (n + 1) = step (raw n)) :
    ∀ n : ℕ, (∀ m : ℕ, m < n → ¬ stop (stopped m)) →
      stopped n = raw n := by
  intro n
  induction n with
  | zero =>
      intro _hno
      exact h_zero
  | succ n ih =>
      intro hno
      have hno_n : ¬ stop (stopped n) := hno n (Nat.lt_succ_self n)
      have hprev : stopped n = raw n :=
        ih (fun m hm => hno m (Nat.lt_trans hm (Nat.lt_succ_self n)))
      calc
        stopped (n + 1) =
            (if stop (stopped n) then stopped n else step (stopped n)) :=
          h_stopped_succ n
        _ = step (stopped n) := by
          simp [hno_n]
        _ = step (raw n) := by
          rw [hprev]
        _ = raw (n + 1) :=
          (h_raw_succ n).symm

/-- A raw stopping witness transfers to a positive one-based witness for a
stopped recursion.

If every raw prefix with no stopped hit agrees with the stopped recursion at its
endpoint, then any raw index satisfying the stopping predicate yields a positive
one-based stopped index satisfying the same predicate.

Layer: Model | Level 1 (raw-to-stopped witness transfer)
Proof: split on whether a stopped hit occurs at or before the raw witness.  In
  the negative branch, prefix agreement transfers the raw witness to the stopped
  recursion, contradicting the assumed absence of such a stopped hit.
Source: Mathlib natural-number order and existential case analysis
Used in: stochastic conditional-gradient sliding CndG inner-loop termination
  transfer from the raw deterministic descent recursion to the early-stopped
  implementation
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem exists_stopped_witness_of_raw_witness
    {State : Type*} (stop : State → Prop)
    (raw stopped : ℕ → State)
    (h_prefix :
      ∀ n : ℕ,
        (∀ m : ℕ, m < n → ¬ stop (stopped m)) →
          stopped n = raw n) :
    (∃ n : ℕ, stop (raw n)) →
      ∃ t : ℕ, 1 ≤ t ∧ stop (stopped (t - 1)) := by
  classical
  rintro ⟨n, hn⟩
  by_cases hstop :
      ∃ m : ℕ, m ≤ n ∧ stop (stopped m)
  · rcases hstop with ⟨m, _hmn, hgap⟩
    refine ⟨m + 1, Nat.succ_pos m, ?_⟩
    simpa using hgap
  · have hno_lt :
        ∀ m : ℕ, m < n → ¬ stop (stopped m) := by
      intro m hm hgap
      exact hstop ⟨m, Nat.le_of_lt hm, hgap⟩
    have heq : stopped n = raw n :=
      h_prefix n hno_lt
    have hgap_stopped : stop (stopped n) := by
      simpa [heq] using hn
    exact False.elim (hstop ⟨n, le_rfl, hgap_stopped⟩)

/-- A relational recursive process preserves a projected carrier invariant.

If the initial state's projected value lies in `X`, and every realized relation
step maps projected values in `X` back into `X`, then every time slice of the
process has projected value in `X`.

Layer: Model | Gap: Level 1 (relational recursive-process invariant propagation)
Proof: induction on the natural-number process time. The zero case uses the
  constant initial slice, and the successor case applies the step relation plus
  the pointwise invariant-preservation hypothesis.
Source: Mathlib natural-number induction, set membership, and relation-valued
  transition-system APIs
Used in: stochastic conditional-gradient sliding outer-state feasibility
  propagation from a relation-valued update specification
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem IsRelationalRecursiveProcess.invariant_mem
    {Omega State E : Type*} {X : Set E}
    {initial : State}
    {rel : Nat -> State -> State -> Omega -> Prop}
    {state : Nat -> Omega -> State}
    (value : State -> E)
    (hstate : IsRelationalRecursiveProcess initial rel state)
    (h_initial : value initial ∈ X)
    (h_step_mem :
      forall k prev next omega,
        rel k prev next omega -> value prev ∈ X -> value next ∈ X) :
    forall n omega, value (state n omega) ∈ X := by
  intro n
  induction n with
  | zero =>
      intro omega
      simpa [hstate.initial omega] using h_initial
  | succ n ih =>
      intro omega
      exact h_step_mem n (state n omega) (state (n + 1) omega) omega
        (hstate.step n omega) (ih omega)

/-- A relation-valued recursive process is determined by its finite driver prefix.

If the initial slice is constant, every successor step satisfies a transition
relation driven by the current driver sample, and that relation is single-valued
for fixed time, driver, and previous state, then equal driver prefixes through
time `n` force equal states at time `n`.

Layer: Model | Gap: Level 1 (relational recursive-process finite-prefix determinism)
Proof: induction on the natural-number process time. The successor case applies
  the induction hypothesis to the previous prefix, rewrites the second step to
  the first previous state and driver, and uses pointwise single-valuedness of
  the relation.
Source: Mathlib natural-number induction, equality rewriting, and relation-valued
  transition-system APIs
Used in: stochastic conditional-gradient sliding outer-state process
  finite-prefix determinism for mini-batch measurability and integrability
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem relational_recursive_process_eq_of_driver_prefix_eq
    {Omega State Driver : Type*}
    (initial : State)
    (driver : Nat -> Omega -> Driver)
    (rel : Nat -> Driver -> State -> State -> Prop)
    (run : Nat -> Omega -> State)
    (h_initial : forall omega : Omega, run 0 omega = initial)
    (h_step : forall k omega,
      rel (k + 1) (driver (k + 1) omega) (run k omega) (run (k + 1) omega))
    (h_single :
      forall k d prev next next',
        rel k d prev next -> rel k d prev next' -> next = next') :
    forall n : Nat, forall omega omega' : Omega,
      (forall j : Nat, j <= n -> driver j omega = driver j omega') ->
        run n omega = run n omega' := by
  intro n
  induction n with
  | zero =>
      intro omega omega' _hprefix
      rw [h_initial omega, h_initial omega']
  | succ n ih =>
      intro omega omega' hprefix
      have hprev : run n omega = run n omega' := by
        exact ih omega omega'
          (fun j hj => hprefix j (Nat.le_trans hj (Nat.le_succ n)))
      have hdriver :
          driver (n + 1) omega = driver (n + 1) omega' :=
        hprefix (n + 1) (Nat.le_refl (n + 1))
      have hstep_left :
          rel (n + 1) (driver (n + 1) omega)
            (run n omega) (run (n + 1) omega) :=
        h_step n omega
      have hstep_right :
          rel (n + 1) (driver (n + 1) omega)
            (run n omega) (run (n + 1) omega') := by
        simpa [hprev, hdriver] using h_step n omega'
      exact h_single (n + 1) (driver (n + 1) omega) (run n omega)
        (run (n + 1) omega) (run (n + 1) omega') hstep_left hstep_right

/-- A two-coordinate stochastic state process is ambient measurable and
past-measurable at every time.

For a raw process `state k : Omega -> State` with public coordinates `xCoord`
and `yCoord`, this predicate records both ordinary measurability and
measurability with respect to the selected strict-past sigma-algebra `past k`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; conjunction of ambient and past
  measurability for two projected state coordinates)
Source: Mathlib measure-theory APIs for measurable stochastic processes and
  filtration-style adaptedness predicates
Used in: stochastic conditional-gradient sliding outer-state adaptedness before
  martingale cancellation and mini-batch variance bounds
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
def TwoCoordinateProcessAdapted
    {Omega State E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    (past : Nat -> MeasurableSpace Omega)
    (xCoord yCoord : State -> E)
    (state : Nat -> Omega -> State) : Prop :=
  forall k : Nat,
    Measurable (fun omega => xCoord (state k omega)) /\
      Measurable (fun omega => yCoord (state k omega)) /\
        Measurable[past k] (fun omega => xCoord (state k omega)) /\
          Measurable[past k] (fun omega => yCoord (state k omega))

/-- The two-coordinate process adaptedness predicate unfolds to the four
coordinate measurability obligations at every time.

Layer: Model | Gap: Level 0 (two-coordinate process adaptedness definition)
Proof: by rfl after unfolding `TwoCoordinateProcessAdapted`.
Source: Mathlib measure-theory APIs for measurable stochastic processes and
  filtration-style adaptedness predicates
Used in: stochastic conditional-gradient sliding outer-state adaptedness before
  martingale cancellation and mini-batch variance bounds
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
@[simp]
theorem TwoCoordinateProcessAdapted_iff
    {Omega State E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    (past : Nat -> MeasurableSpace Omega)
    (xCoord yCoord : State -> E)
    (state : Nat -> Omega -> State) :
    TwoCoordinateProcessAdapted past xCoord yCoord state <->
      forall k : Nat,
        Measurable (fun omega => xCoord (state k omega)) /\
          Measurable (fun omega => yCoord (state k omega)) /\
            Measurable[past k] (fun omega => xCoord (state k omega)) /\
              Measurable[past k] (fun omega => yCoord (state k omega)) := by
  rfl

/-- A recursively generated stochastic process satisfies any relation realized by
its selected step.

If each selected update `step k prev omega` satisfies a time-indexed relation
from `prev`, then the canonical process generated by `recursiveIterateProcess`
is an `IsRelationalRecursiveProcess` for that relation.

Layer: Model | Gap: Level 1 (recursive iterate relation-realization bridge)
Proof: combine the zero and successor equations for `recursiveIterateProcess`;
  the successor equation rewrites the generated next state to the selected step,
  where the supplied relation-realization hypothesis applies.
Source: Mathlib natural-number primitive recursion and relation-valued transition APIs
Used in: stochastic conditional-gradient sliding generated outer-state process
  after proving each selected outer update realizes the relational transition
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem recursiveIterateProcess_isRelationalRecursiveProcess
    {Omega State : Type*}
    (initial : State)
    (step : Nat -> State -> Omega -> State)
    (rel : Nat -> State -> State -> Omega -> Prop)
    (h_step : forall k prev omega, rel k prev (step k prev omega) omega) :
    IsRelationalRecursiveProcess initial rel (recursiveIterateProcess initial step) := by
  constructor
  · intro omega
    exact recursiveIterateProcess_zero
      (recursiveIterateProcess initial step) initial step rfl omega
  · intro k omega
    rw [recursiveIterateProcess_succ
      (recursiveIterateProcess initial step) initial step rfl k omega]
    exact h_step k (recursiveIterateProcess initial step k omega) omega

/-- A one-based recursive iterate stays in a carrier set when its update maps the
carrier to itself.

Every index `t` with `1 ≤ t` is feasible, starting from `u` at time `1` and
using the update invariance for later successors.

Layer: Model | Gap: Level 1 (one-based iterate carrier invariance)
Proof: induction on natural time, with separate impossible zero, initial one,
  and successor-update cases; the successor case applies `Set.MapsTo`.
Source: Mathlib set maps-to and natural-number induction APIs
Used in: stochastic conditional-gradient sliding inner solver feasibility before
  Wolfe-gap stopping
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem oneBasedIterate_mem_of_update_mem
    {E : Type*} {X : Set E} (iterate : Nat -> E) (u : E) (update : E -> E)
    (hone : iterate 1 = u)
    (hsucc : ∀ ⦃t : Nat⦄, 1 <= t -> iterate (t + 1) = update (iterate t))
    (hu : u ∈ X) (hupdate : Set.MapsTo update X X) :
    ∀ t : Nat, 1 <= t -> iterate t ∈ X := by
  intro t ht
  induction t with
  | zero =>
      omega
  | succ t ih =>
      cases t with
      | zero =>
          simpa [hone] using hu
      | succ t =>
          rw [hsucc (t := t + 1) (by omega)]
          exact hupdate (ih (by omega))

-- Generalization plan (G0):
-- concept/name: accelerated snapshot averaged iterate; orig was averagedInnerIterate, renamed away
--   from the paper-local inner-loop label to expose the three-source average.
-- generality used: any type with addition and real scalar multiplication; no measure,
--   convexity, smoothness, or oracle hypotheses are needed for the definitional formula.
-- portable call pattern: variance-reduced accelerated or loopless accelerated methods
--   call this after computing the new prox point, changing schedules, state type,
--   previous average, new point, and snapshot while preserving the three-term formula.
-- counterargument checked: this is a formula definition and close to caller-side syntax,
--   but it is the canonical named averaged-coordinate update paired with an unfolding API,
--   not a paper theorem label or final traceability boundary.
-- coverage search: checked SOptLib acceleratedAveragePoint, acceleratedSearchPoint, and
--   Mathlib Finset.affineCombination; existing SOptLib entries cover two-point accelerated
--   averages, while Mathlib covers generic finite affine combinations but not this named
--   accelerated snapshot update.
-- minimal hypotheses: all already minimal for the displayed expression; no finite
--   dimensionality, topology, norm, or module laws are required.

/-- Accelerated averaged iterate with a persistent snapshot term.

At schedule index `s`, the new averaged point combines the previous average,
the newly produced iterate, and the epoch snapshot with weights
`1 - alpha s - p s`, `alpha s`, and `p s`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; three-source affine averaged-iterate update)
Source: accelerated variance-reduced finite-sum method iterate recurrences and
  Mathlib module scalar multiplication notation
Used in: variance-reduced accelerated gradient descent averaged inner iterate
  after the prox update
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec/steps/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
def acceleratedSnapshotAveragePoint
    {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    (alpha p : ℕ → ℝ) (s : ℕ)
    (xBarPrev xNext snapshot : E) : E :=
  (1 - alpha s - p s) • xBarPrev + alpha s • xNext + p s • snapshot

/-- The accelerated snapshot average unfolds to its three-source affine formula.

Layer: Model | Gap: Level 0 (accelerated snapshot average-point unfolding)
Proof: by rfl after unfolding `acceleratedSnapshotAveragePoint`.
Source: accelerated variance-reduced finite-sum method iterate recurrences and
  Mathlib module scalar multiplication notation
Used in: variance-reduced accelerated gradient descent averaged inner iterate
  after the prox update
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec/steps/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp]
theorem acceleratedSnapshotAveragePoint_def
    {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    (alpha p : ℕ → ℝ) (s : ℕ)
    (xBarPrev xNext snapshot : E) :
    acceleratedSnapshotAveragePoint alpha p s xBarPrev xNext snapshot =
      (1 - alpha s - p s) • xBarPrev + alpha s • xNext + p s • snapshot := by
  rfl

/-- The accelerated snapshot average stays in a convex feasible set.

If the three source points are feasible and the printed coefficients are
nonnegative, then their normalized three-term average is feasible.

Layer: Model | Gap: Level 0 (accelerated snapshot average-point convex feasibility)
Proof: instantiate `Convex.sum_mem` on the finite three-point family and
  simplify the finite sum back to the displayed update.
Source: Mathlib convex-set API for finite convex combinations
Used in: variance-reduced accelerated gradient descent feasible averaged inner
  iterate after the prox update
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec/steps/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem acceleratedSnapshotAveragePoint_mem
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {X : Set E} (hX : Convex ℝ X)
    (alpha p : ℕ → ℝ) (s : ℕ)
    (hprevWeight : 0 ≤ 1 - alpha s - p s)
    (halpha : 0 ≤ alpha s) (hp : 0 ≤ p s)
    {xBarPrev xNext snapshot : E}
    (hxBarPrev : xBarPrev ∈ X) (hxNext : xNext ∈ X)
    (hsnapshot : snapshot ∈ X) :
    acceleratedSnapshotAveragePoint alpha p s xBarPrev xNext snapshot ∈ X := by
  classical
  let w : Fin 3 → ℝ := ![1 - alpha s - p s, alpha s, p s]
  let z : Fin 3 → E := ![xBarPrev, xNext, snapshot]
  have hweights_nonneg :
      ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w i := by
    intro i _hi
    fin_cases i <;> simp [w, hprevWeight, halpha, hp]
  have hweights_sum : Finset.sum (Finset.univ : Finset (Fin 3)) w = 1 := by
    simp [w, Fin.sum_univ_three]
    ring
  have hpoints_mem : ∀ i ∈ (Finset.univ : Finset (Fin 3)), z i ∈ X := by
    intro i _hi
    fin_cases i <;> simp [z, hxBarPrev, hxNext, hsnapshot]
  have hconv :
      Finset.sum (Finset.univ : Finset (Fin 3)) (fun i => w i • z i) ∈ X :=
    hX.sum_mem hweights_nonneg hweights_sum hpoints_mem
  simpa [acceleratedSnapshotAveragePoint, w, z, Fin.sum_univ_three] using hconv


-- Generalization plan (G0):
-- concept/name: accelerated snapshot-average convex-combination weights; orig was
--   `averagedInnerWeightsAdmissible`, renamed away from the paper-local inner-loop
--   label to expose the three-source residual/alpha/snapshot weight predicate.
-- generality used: arbitrary schedule index type `T` with two real-valued
--   schedules `alpha` and `p`; no carrier, measure, independence, integrability,
--   topology, norm, inner product, convexity, smoothness, oracle, or
--   finite-dimensional hypotheses are used by the predicate.
-- portable call pattern: variance-reduced accelerated, loopless accelerated,
--   and snapshot/memory methods call this before convex feasibility or Jensen
--   for a three-source affine recursive average, changing only the schedule
--   index type and the two scalar schedules.
-- counterargument checked: Mathlib has generic `Convex.sum_mem` and
--   `StdSimplex`, and SOptLib has finite-window normalized weights and
--   two-point accelerated averages, but none names this recurring residual
--   three-source schedule predicate; the definition is paired with projection
--   and constructor API rather than retained as paper traceability.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   `FiniteWindowWeightsAdmissible`, `acceleratedAveragePoint`,
--   `acceleratedSnapshotAveragePoint`, `convex combination weights`, and
--   exact `1 - alpha - p` shapes; LeanSearch for "three nonnegative real
--   weights sum to one convex combination" returned Mathlib
--   `Convex.sum_mem`, `StdSimplex.mk`, and `affineCombination_mem_convexHull`,
--   which are primitives but not this schedule-level predicate.
-- minimal hypotheses: all already minimal; even `Nat` indexing was generalized
--   to an arbitrary index type because the formula only evaluates schedules at
--   one index.

/-- Admissible weights for a three-source accelerated snapshot average.

At schedule index `t`, the previous average, new point, and snapshot weights
are `1 - alpha t - p t`, `alpha t`, and `p t`; admissibility means all three
are nonnegative.

Layer: Model | Concept: Iterates
Proof: (definitional construction; residual/alpha/snapshot nonnegativity
  predicate for a three-source affine average)
Source: accelerated variance-reduced finite-sum method iterate recurrences and
  Mathlib ordered real arithmetic
Used in: variance-reduced accelerated gradient descent averaged inner iterate
  feasibility and Jensen steps after the prox update
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec/steps/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
def AcceleratedSnapshotAverageWeightsAdmissible
    {T : Type*} (alpha p : T → ℝ) (t : T) : Prop :=
  0 ≤ 1 - alpha t - p t ∧ 0 ≤ alpha t ∧ 0 ≤ p t

/-- The accelerated snapshot-average admissibility predicate unfolds to the
three scalar nonnegativity conditions.

Layer: Model | Gap: Level 0 (accelerated snapshot-average weight unfolding)
Proof: by rfl after unfolding `AcceleratedSnapshotAverageWeightsAdmissible`.
Source: accelerated variance-reduced finite-sum method iterate recurrences and
  Mathlib ordered real arithmetic
Used in: variance-reduced accelerated gradient descent averaged inner iterate
  feasibility and Jensen steps after the prox update
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec/steps/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp]
theorem AcceleratedSnapshotAverageWeightsAdmissible_def
    {T : Type*} (alpha p : T → ℝ) (t : T) :
    AcceleratedSnapshotAverageWeightsAdmissible alpha p t ↔
      0 ≤ 1 - alpha t - p t ∧ 0 ≤ alpha t ∧ 0 ≤ p t := by
  rfl

namespace AcceleratedSnapshotAverageWeightsAdmissible

/-- Build accelerated snapshot-average admissibility from the three
nonnegativity conditions.

Layer: Model | Gap: Level 0 (accelerated snapshot-average weight constructor)
Proof: package the three scalar inequalities into the definitional conjunction.
Source: accelerated variance-reduced finite-sum method iterate recurrences and
  Mathlib conjunction APIs
Used in: variance-reduced accelerated gradient descent schedule
  specialization before averaged-iterate feasibility
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec/steps/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem of_nonneg
    {T : Type*} {alpha p : T → ℝ} {t : T}
    (hbar : 0 ≤ 1 - alpha t - p t)
    (halpha : 0 ≤ alpha t)
    (hp : 0 ≤ p t) :
    AcceleratedSnapshotAverageWeightsAdmissible alpha p t :=
  ⟨hbar, halpha, hp⟩

/-- The residual previous-average coefficient in an admissible accelerated
snapshot average is nonnegative.

Layer: Model | Gap: Level 0 (accelerated snapshot-average residual weight bound)
Proof: unfold the admissibility predicate and take the first conjunct.
Source: accelerated variance-reduced finite-sum method iterate recurrences and
  Mathlib conjunction APIs
Used in: variance-reduced accelerated gradient descent convex-combination
  feasibility for the averaged inner iterate
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec/steps/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem bar_nonneg
    {T : Type*} {alpha p : T → ℝ} {t : T}
    (h : AcceleratedSnapshotAverageWeightsAdmissible alpha p t) :
    0 ≤ 1 - alpha t - p t :=
  h.1

/-- The new-point coefficient in an admissible accelerated snapshot average is
nonnegative.

Layer: Model | Gap: Level 0 (accelerated snapshot-average alpha weight bound)
Proof: unfold the admissibility predicate and take the second conjunct.
Source: accelerated variance-reduced finite-sum method iterate recurrences and
  Mathlib conjunction APIs
Used in: variance-reduced accelerated gradient descent convex-combination
  feasibility for the averaged inner iterate
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec/steps/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem alpha_nonneg
    {T : Type*} {alpha p : T → ℝ} {t : T}
    (h : AcceleratedSnapshotAverageWeightsAdmissible alpha p t) :
    0 ≤ alpha t :=
  h.2.1

/-- The snapshot coefficient in an admissible accelerated snapshot average is
nonnegative.

Layer: Model | Gap: Level 0 (accelerated snapshot-average snapshot weight bound)
Proof: unfold the admissibility predicate and take the third conjunct.
Source: accelerated variance-reduced finite-sum method iterate recurrences and
  Mathlib conjunction APIs
Used in: variance-reduced accelerated gradient descent convex-combination
  feasibility for the averaged inner iterate
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec/steps/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem snapshot_nonneg
    {T : Type*} {alpha p : T → ℝ} {t : T}
    (h : AcceleratedSnapshotAverageWeightsAdmissible alpha p t) :
    0 ≤ p t :=
  h.2.2

/-- The three accelerated snapshot-average coefficients sum to one.

Layer: Model | Gap: Level 0 (accelerated snapshot-average weight normalization)
Proof: normalize the residual/alpha/snapshot scalar expression by ring
  arithmetic; admissibility is carried as the named call-site contract.
Source: accelerated variance-reduced finite-sum method iterate recurrences and
  Mathlib ordered-ring normalization
Used in: variance-reduced accelerated gradient descent convex-combination
  feasibility and Jensen steps for the averaged inner iterate
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec/steps/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem sum_eq_one
    {T : Type*} {alpha p : T → ℝ} {t : T}
    (_h : AcceleratedSnapshotAverageWeightsAdmissible alpha p t) :
    (1 - alpha t - p t) + alpha t + p t = 1 := by
  ring

end AcceleratedSnapshotAverageWeightsAdmissible

-- Generalization plan (G0):
-- concept/name: accelerated three-source search-point weight admissibility;
--   orig was `lemma516_searchPointWeightsAdmissible`, renamed away from the
--   paper lemma number and local setup name while retaining the accelerated
--   search-point weight concept.
-- generality used: real scalar parameters `mu`, `gamma`, `alpha`, and `p`,
--   plus pointwise order hypotheses; no carrier, measure, independence,
--   integrability, topology, norm, inner product, convexity, smoothness
--   function, oracle, schedule, or finite-dimensional hypotheses are used.
-- portable call pattern: accelerated variance-reduced and snapshot/memory
--   methods call this when proving that a rational three-source search query
--   is a convex combination; schedules and smoothness constants vary, while
--   `mu`, `gamma`, `alpha`, `p`, and the bar-coefficient guard instantiate
--   the same admissibility conclusion.
-- counterargument checked: this is not just paper traceability because the
--   theorem packages the reusable scalar normalization for a three-source
--   accelerated search point; it is not a pure wrapper around Mathlib's
--   convex-combination APIs, which consume already-admissible weights rather
--   than proving this rational weight triple admissible.
-- coverage search: searched CATALOG.md, SOptLib, Staging, and the algorithm
--   sources for `acceleratedSearchPoint`, `searchPointWeightsAdmissible`,
--   `search denominator`, `1 + mu * gamma * (1 - alpha)`, and
--   `AcceleratedVRScalarSideConditions`; top hits were partial:
--   `SOptLib.acceleratedSearchPoint_mem` covers a two-source search point,
--   staged `AcceleratedVRScalarSideConditions` bundles a larger scalar
--   contract without proving weight admissibility, and Mathlib LeanSearch
--   returned `Convex.sum_mem`/`StdSimplex.mk`, which start from nonnegative
--   weights summing to one.
-- minimal hypotheses: strengthened from setup-local fields to pointwise
--   scalar facts and dropped unused curvature/noise hypotheses; `mu ≥ 0`,
--   `alpha ≥ 0`, `gamma ≥ 0`, `p ≥ 0`, and `0 ≤ 1 - alpha - p` are the
--   facts used to prove denominator positivity and coefficient
--   nonnegativity.

/-- The rational three-source accelerated search-point weights are admissible.

If `mu`, `gamma`, `alpha`, and `p` are nonnegative, and the residual
bar coefficient `1 - alpha - p` is nonnegative,
then the three displayed weights normalized by
`1 + mu * gamma * (1 - alpha)` are nonnegative and sum to one.

Layer: Model | Gap: Level 1 (accelerated three-source search-point weights)
Proof: prove positivity of the rational denominator from the scalar side
  conditions, then use ordered-field quotient nonnegativity and field
  normalization to show the three weights sum to one.
Source: accelerated finite-sum variance-reduction search-point recurrences
  and Mathlib ordered real-field arithmetic APIs
Used in: variance-reduced accelerated gradient descent search-query
  convex-combination admissibility before constructing the feasible query point
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/2/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem accelerated_search_point_weights_admissible_of_side_conditions
    (mu gamma alpha p : ℝ)
    (hmu_nonneg : 0 ≤ mu)
    (halpha_nonneg : 0 ≤ alpha)
    (hgamma_nonneg : 0 ≤ gamma)
    (hp_nonneg : 0 ≤ p)
    (hbar : 0 ≤ 1 - alpha - p) :
    let searchDenominator : ℝ := 1 + mu * gamma * (1 - alpha)
    0 ≤ ((1 + mu * gamma) * (1 - alpha - p)) / searchDenominator ∧
      0 ≤ alpha / searchDenominator ∧
      0 ≤ ((1 + mu * gamma) * p) / searchDenominator ∧
      ((1 + mu * gamma) * (1 - alpha - p)) / searchDenominator +
          alpha / searchDenominator +
          ((1 + mu * gamma) * p) / searchDenominator = 1 := by
  have hone_sub_alpha_nonneg : 0 ≤ 1 - alpha := by
    nlinarith
  have hmu_gamma_nonneg : 0 ≤ mu * gamma :=
    mul_nonneg hmu_nonneg hgamma_nonneg
  have hden_pos : 0 < 1 + mu * gamma * (1 - alpha) := by
    have hprod_nonneg : 0 ≤ mu * gamma * (1 - alpha) :=
      mul_nonneg hmu_gamma_nonneg hone_sub_alpha_nonneg
    nlinarith
  have hden_nonneg : 0 ≤ 1 + mu * gamma * (1 - alpha) := le_of_lt hden_pos
  have hone_mu_gamma_nonneg : 0 ≤ 1 + mu * gamma := by
    nlinarith
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg hone_mu_gamma_nonneg hbar) hden_nonneg
  · exact div_nonneg halpha_nonneg hden_nonneg
  · exact div_nonneg (mul_nonneg hone_mu_gamma_nonneg hp_nonneg) hden_nonneg
  · field_simp [ne_of_gt hden_pos]
    ring

-- Generalization plan (G0):
-- concept/name: accelerated snapshot-average displacement identity; orig was
--   lemma516_bar_minus_search_eq_alpha_sub_auxiliary, renamed away from the
--   paper lemma number and local bar/search labels while retaining the
--   accelerated snapshot-average and auxiliary-point concepts.
-- generality used: arbitrary real module with scalar parameters and the two
--   denominator nonzero hypotheses needed for rational normalization; no
--   measure, filtration, independence, integrability, convexity, smoothness,
--   oracle, norm, inner-product, schedule, or finite-dimensional assumptions
--   are used.
-- portable call pattern: accelerated variance-reduced, loopless accelerated,
--   and snapshot/memory methods call this after substituting the three-source
--   search point, snapshot average, and regularized auxiliary point; `mu`,
--   schedules, previous average, previous prox point, new prox point, and
--   snapshot vary while the displacement conclusion is unchanged.
-- counterargument checked: wrapper risk is real because the proof is affine
--   algebra, but Mathlib and SOptLib only cover generic affine combinations or
--   two-point accelerated search identities; this three-source rational
--   snapshot-search normalization is the reusable proof step.
-- coverage search: searched CATALOG.md, SOptLib, Staging, and the algorithm
--   file for `average_sub_search`, `acceleratedSearchPoint`,
--   `acceleratedSnapshotAveragePoint`, `auxiliaryPoint`, and exact
--   `1 + mu * gamma * (1 - alpha)` shapes; top hits were partial:
--   `SOptLib.average_sub_search_eq_alpha_smul_step_sub_weighted_center`
--   covers a two-point search with a q/alpha coupling, and staged
--   `acceleratedSnapshotAveragePoint` names the three-source average but does
--   not prove this displacement identity. LeanSearch returned Mathlib
--   `Finset.affineCombination` and weighted-vsub lemmas, which are generic
--   affine primitives rather than this scalar normalization.
-- minimal hypotheses: only the two denominator nonzero facts are needed; no
--   global schedule, positivity, topology, norm, or finite-dimensional
--   assumptions are needed.

/-- A three-source accelerated snapshot average minus its rational search point
is the alpha-scaled displacement from the regularized auxiliary point.

The search point has weights normalized by
`1 + mu * gamma * (1 - alpha)`, while the auxiliary point blends the
previous prox point and that search point with denominator `1 + mu * gamma`.

Layer: Model | Gap: Level 1 (accelerated snapshot-search affine displacement)
Proof: use the two denominator nonzero hypotheses, then close the real-module
  equality by scalar field normalization and module arithmetic.
Source: accelerated variance-reduced finite-sum method iterate recurrences and
  Mathlib real module arithmetic APIs
Used in: variance-reduced accelerated gradient descent conversion of the
  averaged inner-iterate displacement into the prox-auxiliary displacement
  before the one-step descent estimate
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec/steps/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem acceleratedSnapshotAverage_sub_search_eq_alpha_smul_sub_auxiliary
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (mu gamma alpha p : ℝ)
    (hsearch_den_ne : 1 + mu * gamma * (1 - alpha) ≠ 0)
    (haux_den_ne : 1 + mu * gamma ≠ 0)
    (xBarPrev xPrev xNext snapshot : E) :
    let searchDenominator : ℝ := 1 + mu * gamma * (1 - alpha)
    let searchPoint : E :=
      ((1 + mu * gamma) * (1 - alpha - p) / searchDenominator) • xBarPrev +
        (alpha / searchDenominator) • xPrev +
          (((1 + mu * gamma) * p) / searchDenominator) • snapshot
    let auxiliaryPoint : E :=
      (1 / (1 + mu * gamma)) • xPrev +
        (mu * gamma / (1 + mu * gamma)) • searchPoint
    let snapshotAverage : E :=
      (1 - alpha - p) • xBarPrev + alpha • xNext + p • snapshot
    snapshotAverage - searchPoint =
      alpha • (xNext - auxiliaryPoint) := by
  have hsearch_den_ne' : 1 - alpha * mu * gamma + mu * gamma ≠ 0 := by
    convert hsearch_den_ne using 1
    ring
  have hsearch_den_ne'' : 1 + mu * gamma - mu * gamma * alpha ≠ 0 := by
    convert hsearch_den_ne using 1
    ring
  dsimp only
  match_scalars
  all_goals
    ring_nf
    try field_simp [hsearch_den_ne, hsearch_den_ne', hsearch_den_ne'', haux_den_ne]
    try ring


-- Generalization plan (G0):
-- concept/name: finite-range recursive-process measurability from a fixed
--   history sigma-algebra; orig was
--   `lemma518_recursive_process_measurable_finite_range_wrt_history`, renamed
--   away from theorem numbering and Lan-specific strict-past state language.
-- generality used: arbitrary source type `Omega`, state type `X`, driver type
--   `U`, explicit history measurable space `mHist`, measurable singleton
--   codomains, finite-range initial state and finite-range drivers; no measure,
--   probability, independence, integrability, topology, convexity, smoothness,
--   oracle, norm, inner-product, or finite-dimensional hypotheses are used.
-- portable call pattern: generated stochastic-optimization recursions with
--   nonmeasurable global selectors instantiate `process`, `driver`, and
--   `step`; finite key determinism replaces a global measurable step-kernel
--   hypothesis while preserving measurability of each fixed adapted state.
-- counterargument checked: not paper-local traceability because the same
--   finite-key adaptedness induction appears whenever a generated update is
--   only known as a function of the previous finite-range state and current
--   finite-range sample; not a wrapper around the existing prefix lemma, whose
--   hypothesis is a globally measurable update kernel.
-- coverage search: searched SOptLib catalog/sources for `recursive process
--   measurable`, `finite range`, `sample prefix`, and
--   `measurable_of_finite_range_fiber_const`; top partial hits were
--   `SOptLib.recursive_process_measurable_wrt_sample_prefix` and
--   `SOptLib.recursive_process_measurable_of_measurable_update`, both requiring
--   measurable update kernels, plus the Glue finite-fiber measurability lemma
--   used in this proof. LeanSearch for finite-range recursive-process
--   measurability returned only generic update/simple-function APIs.
-- minimal hypotheses: the global measurable update hypothesis is weakened to
--   the pointwise recursion equation and finite-range driver slices; all
--   remaining hypotheses are used by the induction and finite-fiber
--   measurability step.

/-- A finite-range recursive process is measurable from a fixed history sigma-algebra.

If the initial state and every required driver coordinate are measurable from
the same history, the initial state and all drivers have finite range, and the
successor state is pointwise determined by the previous state and current
driver, then every state up to the horizon is measurable from that history and
has finite range.

Layer: Model | Gap: Level 1 (finite-range recursive process adaptedness)
Proof: induction on the time index. At each successor step the key
  `(previous state, current driver)` is measurable and finite-range, so the
  pointwise successor factors through a finite measurable key by
  `measurable_of_finite_range_fiber_const`.
Source: Mathlib measurable product APIs, finite range set APIs, and measurable
  singleton finite-fiber factorization
Used in: generated variance-reduced accelerated inner-loop adaptedness with a
  nonmeasurable global prox selector
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem recursive_process_measurable_finite_range_wrt_history
    {Omega X U : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    (mHist : MeasurableSpace Omega)
    (process : Nat -> Omega -> X)
    (driver : Nat -> Omega -> U)
    (step : Nat -> X -> U -> X)
    (N n : Nat)
    (h_init_meas : @Measurable Omega X mHist (by infer_instance) (process 0))
    (h_init_finite : (Set.range (process 0)).Finite)
    (h_driver_meas :
      forall j, j + 1 <= N ->
        @Measurable Omega U mHist (by infer_instance) (driver j))
    (h_driver_finite : forall j, j + 1 <= N -> (Set.range (driver j)).Finite)
    (h_update :
      forall j, j + 1 <= N ->
        forall omega : Omega, process (j + 1) omega =
          step j (process j omega) (driver j omega))
    (hn : n <= N) :
    @Measurable Omega X mHist (by infer_instance) (process n) ∧
      (Set.range (process n)).Finite := by
  classical
  induction n with
  | zero =>
      exact ⟨h_init_meas, h_init_finite⟩
  | succ n ih =>
      have hn_le : n <= N := Nat.le_of_succ_le hn
      rcases ih hn_le with ⟨hprev_meas, hprev_finite⟩
      have hstep_bound : n + 1 <= N := hn
      have hdriver_meas :
          @Measurable Omega U mHist (by infer_instance) (driver n) :=
        h_driver_meas n hstep_bound
      let Y : Omega -> X × U := fun omega => (process n omega, driver n omega)
      have hY_meas :
          @Measurable Omega (X × U) mHist (by infer_instance) Y := by
        exact hprev_meas.prodMk hdriver_meas
      have hY_finite : (Set.range Y).Finite := by
        have hsubset :
            Set.range Y <= Set.range (process n) ×ˢ Set.range (driver n) := by
          intro yu hyu
          rcases hyu with ⟨omega, rfl⟩
          exact ⟨⟨omega, rfl⟩, ⟨omega, rfl⟩⟩
        exact (hprev_finite.prod (h_driver_finite n hstep_bound)).subset hsubset
      have hnext_meas :
          @Measurable Omega X mHist (by infer_instance) (process (n + 1)) := by
        letI : MeasurableSpace Omega := mHist
        have hY_meas' : Measurable Y := by
          simpa using hY_meas
        have hmeas_step :
            Measurable (fun omega : Omega => step n (process n omega) (driver n omega)) := by
          let Z : Omega -> X := fun omega => step n (process n omega) (driver n omega)
          haveI : Fintype {y : X × U // y ∈ Set.range Y} := hY_finite.fintype
          let Yrange : Omega -> {y : X × U // y ∈ Set.range Y} :=
            fun omega => ⟨Y omega, ⟨omega, rfl⟩⟩
          let G : {y : X × U // y ∈ Set.range Y} -> X := fun y =>
            Z (Classical.choose y.2)
          have hYrange : Measurable Yrange := by
            refine measurable_to_countable ?_
            intro omega
            have hset : MeasurableSet (Y ⁻¹' {Y omega}) :=
              hY_meas' (measurableSet_singleton (Y omega))
            convert hset using 1
            ext omega'
            simp [Yrange]
          have hG : Measurable G := measurable_of_finite G
          have hZG : Z = G ∘ Yrange := by
            funext omega
            dsimp [Function.comp, G, Yrange, Z]
            have hkey :
                Y (Classical.choose (show Y omega ∈ Set.range Y from ⟨omega, rfl⟩)) =
                  Y omega :=
              Classical.choose_spec (show Y omega ∈ Set.range Y from ⟨omega, rfl⟩)
            have hprocess_eq :
                process n (Classical.choose (show Y omega ∈ Set.range Y from ⟨omega, rfl⟩)) =
                  process n omega :=
              congrArg Prod.fst hkey
            have hdriver_eq :
                driver n (Classical.choose (show Y omega ∈ Set.range Y from ⟨omega, rfl⟩)) =
                  driver n omega :=
              congrArg Prod.snd hkey
            simp [hprocess_eq, hdriver_eq]
          change Measurable Z
          rw [hZG]
          exact hG.comp hYrange
        have hprocess_eq :
            process (n + 1) =
              fun omega : Omega => step n (process n omega) (driver n omega) :=
          funext (h_update n hstep_bound)
        simpa [hprocess_eq] using hmeas_step
      have hnext_finite : (Set.range (process (n + 1))).Finite := by
        have hsubset :
            Set.range (process (n + 1)) <=
              (fun yu : X × U => step n yu.1 yu.2) '' Set.range Y := by
          rintro x ⟨omega, rfl⟩
          refine ⟨Y omega, ⟨omega, rfl⟩, ?_⟩
          exact (h_update n hstep_bound omega).symm
        exact (hY_finite.image (fun yu : X × U => step n yu.1 yu.2)).subset hsubset
      exact ⟨hnext_meas, hnext_finite⟩

-- Generalization plan (G0):
-- concept/name: finite-range recursive-process measurability over a containing
--   sample-prefix filtration; orig was
--   `recursive_process_measurable_finite_range_wrt_sample_prefix`, already a
--   paper-free concept name except for the domain phrase "sample-prefix".
-- generality used: arbitrary source type `Omega`, state type `X`, driver type
--   `U`, monotone natural-indexed measurable-space family `past`, measurable
--   singleton codomains, finite-range initial state and finite-range drivers;
--   no measure, probability, independence, integrability, topology,
--   convexity, smoothness, oracle, norm, inner-product, or finite-dimensional
--   hypotheses are used.
-- portable call pattern: prefix-adapted generated stochastic-optimization
--   recursions instantiate `past`, `process`, `driver`, and `step`; only the
--   concrete filtration, finite driver alphabet, horizon, and recurrence change
--   while the conclusion remains measurability and finite range of the state at
--   a containing prefix.
-- counterargument checked: not paper-local traceability because the statement
--   is the reusable finite-key substitute for a globally measurable update
--   kernel; not a duplicate of the existing sample-prefix lemma, which assumes
--   a measurable state-driver update, and not a duplicate of the fixed-history
--   staged lemma, which lacks the monotone prefix-lifting interface.
-- coverage search: searched SOptLib catalog/sources for `recursive process
--   measurable`, `finite range`, `sample prefix`, and
--   `measurable_of_finite_range_fiber_const`; partial hits were
--   `SOptLib.recursive_process_measurable_wrt_sample_prefix`,
--   `SOptLib.recursive_process_measurable_of_measurable_update`, and staged
--   `SOptLib.recursive_process_measurable_finite_range_wrt_history`.
--   LeanSearch for finite-range recursive-process prefix measurability returned
--   filtration/adaptedness primitives but no finite-key recursion theorem.
-- minimal hypotheses: the driver finite-range hypothesis is bounded to the
--   indices used by the recursion, and the global measurable update hypothesis
--   is replaced by a pointwise recurrence plus finite-range fiber constancy.

/-- A finite-range recursive process is measurable from any containing sample prefix.

If each driver coordinate is measurable from its own sample prefix, the prefix
family is monotone, and the successor state is pointwise determined by the
previous state and current finite-range driver, then every state up to the
horizon is measurable from the containing prefix `N + 1` and has finite range.

Layer: Model | Gap: Level 1 (finite-range recursive process sample-prefix adaptedness)
Proof: specialize the fixed-history finite-range recursion lemma to
  `past (N + 1)`. Driver measurability is lifted from each local prefix to the
  containing prefix by monotonicity.
Source: Mathlib measurable-space monotonicity APIs, finite range set APIs, and
  measurable singleton finite-fiber factorization
Used in: generated variance-reduced accelerated inner-loop adaptedness with a
  nonmeasurable global prox selector and finite sample prefixes
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem recursive_process_measurable_finite_range_wrt_sample_prefix
    {Omega X U : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    (past : Nat -> MeasurableSpace Omega)
    (process : Nat -> Omega -> X)
    (driver : Nat -> Omega -> U)
    (step : Nat -> X -> U -> X)
    (N n : Nat)
    (h_past_mono : forall {a b : Nat}, a <= b -> past a <= past b)
    (h_init_meas : @Measurable Omega X (past (N + 1)) (by infer_instance) (process 0))
    (h_init_finite : (Set.range (process 0)).Finite)
    (h_driver_prefix :
      forall j, j + 1 <= N ->
        @Measurable Omega U (past ((j + 1) + 1)) (by infer_instance) (driver j))
    (h_driver_finite : forall j, j + 1 <= N -> (Set.range (driver j)).Finite)
    (h_update :
      forall j, j + 1 <= N ->
        forall omega : Omega, process (j + 1) omega =
          step j (process j omega) (driver j omega))
    (hn : n <= N) :
    @Measurable Omega X (past (N + 1)) (by infer_instance) (process n) ∧
      (Set.range (process n)).Finite := by
  refine
    recursive_process_measurable_finite_range_wrt_history
      (mHist := past (N + 1))
      (process := process)
      (driver := driver)
      (step := step)
      (N := N)
      (n := n)
      h_init_meas
      h_init_finite
      ?_
      h_driver_finite
      h_update
      hn
  intro j hj
  have hle : (j + 1) + 1 <= N + 1 := Nat.succ_le_succ hj
  exact (h_driver_prefix j hj).mono (h_past_mono hle) le_rfl


-- Generalization plan (G0):
-- concept/name: accelerated snapshot search point; orig was `searchPoint`,
--   renamed away from the paper-local declaration while retaining the
--   accelerated three-source query concept.
-- generality used: arbitrary schedule index type `T`, real scalar schedules
--   `gamma`, `alpha`, and `p`, and any type with addition and real scalar
--   multiplication for the definitional formula; the convex-membership API
--   only adds the module and convex-set hypotheses needed by `Convex.sum_mem`.
--   No measure, filtration, smoothness, oracle, norm, inner product, or
--   finite-dimensional hypotheses are used.
-- portable call pattern: variance-reduced accelerated, loopless accelerated,
--   and snapshot/memory methods call this before stochastic-oracle evaluation
--   to build a query from the previous average, previous prox point, and
--   snapshot; schedules, regularization coefficient, index type, and state
--   space vary while the rational three-source construction remains fixed.
-- counterargument checked: the body is a displayed formula, but it is the
--   canonical named search-query object paired with feasibility API; it is not
--   paper-local traceability, a pure theorem label, or a one-line wrapper
--   around the existing two-source `acceleratedSearchPoint`.
-- coverage search: searched CATALOG.md, SOptLib, Staging, and the algorithm
--   file for `acceleratedSearchPoint`, `searchPoint`, `snapshot search`,
--   `1 + mu * gamma * (1 - alpha)`, and three-source weights. Full signatures
--   showed `SOptLib.acceleratedSearchPoint` covers only a two-source query,
--   staged `acceleratedSnapshotAveragePoint` covers the post-update average,
--   and staged search-weight admissibility proves scalar side conditions but
--   does not name the query point itself; no full duplicate was found.
-- minimal hypotheses: the definition needs only `AddCommMonoid` and `SMul`;
--   the membership theorem takes pointwise nonnegativity and normalization of
--   the displayed weights rather than global schedule assumptions.


/-- Accelerated search point with a persistent snapshot term.

At schedule index `t`, this query combines the previous averaged iterate, the
previous prox iterate, and the epoch snapshot using the rational weights
normalized by `1 + mu * gamma t * (1 - alpha t)`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; three-source rational affine search query)
Source: accelerated variance-reduced finite-sum method iterate recurrences and
  Mathlib module scalar multiplication notation
Used in: variance-reduced accelerated gradient descent search-query computation
  before stochastic oracle evaluation and the prox update
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec/steps/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
noncomputable def acceleratedSnapshotSearchPoint
    {E T : Type*} [AddCommMonoid E] [SMul ℝ E]
    (mu : ℝ) (gamma alpha p : T → ℝ) (t : T)
    (xBarPrev xPrev snapshot : E) : E :=
  (((1 + mu * gamma t) * (1 - alpha t - p t)) /
      (1 + mu * gamma t * (1 - alpha t))) • xBarPrev +
    (alpha t / (1 + mu * gamma t * (1 - alpha t))) • xPrev +
      (((1 + mu * gamma t) * p t) /
        (1 + mu * gamma t * (1 - alpha t))) • snapshot

/-- The accelerated snapshot search point unfolds to its rational three-source
affine formula.

Layer: Model | Gap: Level 0 (accelerated snapshot search-point unfolding)
Proof: by rfl after unfolding `acceleratedSnapshotSearchPoint`.
Source: accelerated variance-reduced finite-sum method iterate recurrences and
  Mathlib module scalar multiplication notation
Used in: variance-reduced accelerated gradient descent search-query computation
  before stochastic oracle evaluation and the prox update
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec/steps/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp]
theorem acceleratedSnapshotSearchPoint_def
    {E T : Type*} [AddCommMonoid E] [SMul ℝ E]
    (mu : ℝ) (gamma alpha p : T → ℝ) (t : T)
    (xBarPrev xPrev snapshot : E) :
    acceleratedSnapshotSearchPoint mu gamma alpha p t xBarPrev xPrev snapshot =
      (((1 + mu * gamma t) * (1 - alpha t - p t)) /
          (1 + mu * gamma t * (1 - alpha t))) • xBarPrev +
        (alpha t / (1 + mu * gamma t * (1 - alpha t))) • xPrev +
          (((1 + mu * gamma t) * p t) /
            (1 + mu * gamma t * (1 - alpha t))) • snapshot := by
  rfl

/-- The accelerated snapshot search point stays in a convex feasible set.

If the displayed rational weights are nonnegative and normalized, then the
three-source query formed from feasible points is feasible.

Layer: Model | Gap: Level 0 (accelerated snapshot search-point convex feasibility)
Proof: instantiate `Convex.sum_mem` on the finite three-point family and
  simplify the finite sum back to the displayed query.
Source: Mathlib convex-set API for finite convex combinations
Used in: variance-reduced accelerated gradient descent feasible search-query
  construction before stochastic oracle evaluation
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec/steps/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem acceleratedSnapshotSearchPoint_mem
    {E T : Type*} [AddCommGroup E] [Module ℝ E]
    {X : Set E} (hX : Convex ℝ X)
    (mu : ℝ) (gamma alpha p : T → ℝ) (t : T)
    (hbar :
      0 ≤ (((1 + mu * gamma t) * (1 - alpha t - p t)) /
        (1 + mu * gamma t * (1 - alpha t))))
    (hprev :
      0 ≤ alpha t / (1 + mu * gamma t * (1 - alpha t)))
    (hsnapshot :
      0 ≤ (((1 + mu * gamma t) * p t) /
        (1 + mu * gamma t * (1 - alpha t))))
    (hsum :
      (((1 + mu * gamma t) * (1 - alpha t - p t)) /
          (1 + mu * gamma t * (1 - alpha t))) +
        alpha t / (1 + mu * gamma t * (1 - alpha t)) +
          (((1 + mu * gamma t) * p t) /
            (1 + mu * gamma t * (1 - alpha t))) = 1)
    {xBarPrev xPrev snapshot : E}
    (hxBarPrev : xBarPrev ∈ X) (hxPrev : xPrev ∈ X)
    (hsnapshot_mem : snapshot ∈ X) :
    acceleratedSnapshotSearchPoint mu gamma alpha p t xBarPrev xPrev snapshot ∈ X := by
  classical
  let w : Fin 3 → ℝ :=
    ![(((1 + mu * gamma t) * (1 - alpha t - p t)) /
        (1 + mu * gamma t * (1 - alpha t))),
      alpha t / (1 + mu * gamma t * (1 - alpha t)),
      (((1 + mu * gamma t) * p t) /
        (1 + mu * gamma t * (1 - alpha t)))]
  let z : Fin 3 → E := ![xBarPrev, xPrev, snapshot]
  have hweights_nonneg :
      ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w i := by
    intro i _hi
    fin_cases i <;> simp [w, hbar, hprev, hsnapshot]
  have hweights_sum : Finset.sum (Finset.univ : Finset (Fin 3)) w = 1 := by
    simpa [w, Fin.sum_univ_three] using hsum
  have hpoints_mem : ∀ i ∈ (Finset.univ : Finset (Fin 3)), z i ∈ X := by
    intro i _hi
    fin_cases i <;> simp [z, hxBarPrev, hxPrev, hsnapshot_mem]
  have hconv :
      Finset.sum (Finset.univ : Finset (Fin 3)) (fun i => w i • z i) ∈ X :=
    hX.sum_mem hweights_nonneg hweights_sum hpoints_mem
  simpa [acceleratedSnapshotSearchPoint, w, z, Fin.sum_univ_three] using hconv


-- Generalization plan (G0):
-- concept/name: nested epoch process previous-state adaptedness and finite
--   range from finite current block keys; orig was
--   `smooth_prev_epoch_state_strictPast_measurable_and_finite_range`, renamed
--   away from the smooth Algorithm 5.7 local state terminology.
-- generality used: arbitrary sample space `Omega`, state type `X`, epoch-indexed
--   block type family `U`, indexed strict-past measurable spaces, finite-range
--   initial state and finite-range epoch blocks; no measure, probability, independence,
--   integrability, topology, convexity, smoothness, norm, inner-product, or
--   finite-dimensional hypotheses are used.
-- portable call pattern: nested-loop stochastic optimization recursions whose
--   next epoch state is determined by the previous epoch state and the finite
--   block of current samples call this to recover strict-past measurability and
--   finite range of the previous epoch state; only the past family, block
--   extractor, and epoch update change.
-- counterargument checked: not paper-local traceability because the induction
--   is the reusable adaptedness proof for finite-block epoch recursions; not
--   a wrapper around Mathlib, which has finite-range/simple-function facts but
--   no nested epoch recursion with monotone strict-past spaces; overlaps with
--   recursive-process measurability lemmas, but those require either a fixed
--   history or a globally measurable update kernel rather than finite-key
--   determinism at changing epoch pasts.
-- coverage search: searched SOptLib catalog/sources for `recursive process
--   measurable finite range history`, `strict past epoch block measurable
--   finite range`, and `finite range measurable function constant on fibers`;
--   partial hits were `SOptLib.recursiveProcess_measurable_wrt_strictPast`,
--   `SOptLib.recursive_process_measurable_wrt_sample_prefix`,
--   `SOptLib.recursive_process_measurable_of_measurable_update`, staged
--   `recursive_process_measurable_finite_range_wrt_history`, and
--   `measurable_of_finite_range_fiber_const`; LeanSearch returned
--   `MeasureTheory.SimpleFunc.finite_range` and range-factorization APIs, none
--   covering the indexed finite-block recursion.
-- minimal hypotheses: the update is stated as the pointwise epoch recursion,
--   while measurability of the update kernel is replaced by finite range of the
--   previous-state/current-block key; the only monotonicity needed is from the
--   previous epoch's strict-past space at substep zero into the current target
--   strict-past space.

/-- A nested epoch process has a measurable finite-range previous state.

If the initial epoch state is finite-range and measurable from every target
past, each current epoch block is finite-range and measurable from the next
target past, strict-past sigma-algebras are monotone across epoch boundaries,
and the next state is a deterministic function of the previous state and the
current block, then the state at epoch `s - 1` is measurable from `past s k`
and has finite range.

Layer: Model | Gap: Level 1 (finite-block nested epoch adaptedness)
Proof: induction on the epoch index. At a successor epoch, the key made from
  the previous state and current block is measurable and finite-range; the
  update factors through this finite key, so finite-fiber measurability and a
  finite image argument give the next state.
Source: Mathlib measurable product APIs, finite range set APIs, and measurable
  singleton finite-fiber factorization
Used in: variance-reduced accelerated gradient epoch-state adaptedness before
  conditioning on the next finite sample block
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem nested_epoch_process_prev_state_measurable_finite_range_of_finite_block_key
    {Omega X : Type*} {U : Nat -> Type*}
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [forall e, MeasurableSpace (U e)] [forall e, MeasurableSingletonClass (U e)]
    (past : Nat -> Nat -> MeasurableSpace Omega)
    (state : Nat -> Omega -> X)
    (block : forall e, Omega -> U e)
    (stepEpoch : forall r, X -> U (r + 1) -> X)
    (s : Nat) (hs : 1 <= s) (k : Nat)
    (h_init_meas :
      forall k,
        @Measurable Omega X (past 1 k) (by infer_instance) (state 0))
    (h_init_finite : (Set.range (state 0)).Finite)
    (hprev_mono :
      forall r k, past (r + 1) 0 <= past (r + 1 + 1) k)
    (hblock_meas :
      forall r k,
        @Measurable Omega (U (r + 1)) (past (r + 1 + 1) k) (by infer_instance)
          (block (r + 1)))
    (hblock_finite :
      forall r, (Set.range (block (r + 1))).Finite)
    (h_update :
      forall r,
        state (r + 1) =
          fun omega : Omega => stepEpoch r (state r omega) (block (r + 1) omega)) :
    @Measurable Omega X (past s k) (by infer_instance) (state (s - 1)) ∧
      (Set.range (state (s - 1))).Finite := by
  classical
  induction s generalizing k with
  | zero =>
      omega
  | succ s ih =>
      cases s with
      | zero =>
          exact ⟨h_init_meas k, h_init_finite⟩
      | succ r =>
          have hprev_raw := ih (k := 0) (Nat.succ_pos r)
          have hprev_meas :
              @Measurable Omega X (past (r + 1 + 1) k) (by infer_instance)
                (state r) := by
            have hmono := hprev_mono r k
            have hprev_r_meas :
                @Measurable Omega X (past (r + 1) 0) (by infer_instance)
                  (state r) := by
              simpa using hprev_raw.1
            exact hprev_r_meas.mono hmono le_rfl
          have hcur_block_meas :
              @Measurable Omega (U (r + 1)) (past (r + 1 + 1) k) (by infer_instance)
                (block (r + 1)) :=
            hblock_meas r k
          let key : Omega -> X × U (r + 1) :=
            fun omega => (state r omega, block (r + 1) omega)
          have hkey_meas :
              @Measurable Omega (X × U (r + 1)) (past (r + 1 + 1) k) (by infer_instance)
                key := by
            exact hprev_meas.prodMk hcur_block_meas
          have hkey_finite : (Set.range key).Finite := by
            have hsubset :
                Set.range key <= Set.range (state r) ×ˢ Set.range (block (r + 1)) := by
              intro y hy
              rcases hy with ⟨omega, rfl⟩
              exact ⟨⟨omega, rfl⟩, ⟨omega, rfl⟩⟩
            exact (hprev_raw.2.prod (hblock_finite r)).subset hsubset
          have hnext_meas :
              @Measurable Omega X (past (r + 1 + 1) k) (by infer_instance)
                (state (r + 1)) := by
            letI : MeasurableSpace Omega := past (r + 1 + 1) k
            have hkey_meas' : Measurable key := by
              simpa using hkey_meas
            have hfactor_meas :
                Measurable
                  (fun omega : Omega =>
                    stepEpoch r (state r omega) (block (r + 1) omega)) := by
              let Z : Omega -> X :=
                fun omega : Omega =>
                  stepEpoch r (state r omega) (block (r + 1) omega)
              haveI : Fintype {y : X × U (r + 1) // y ∈ Set.range key} :=
                hkey_finite.fintype
              let keyRange : Omega -> {y : X × U (r + 1) // y ∈ Set.range key} :=
                fun omega => ⟨key omega, ⟨omega, rfl⟩⟩
              let G : {y : X × U (r + 1) // y ∈ Set.range key} -> X :=
                fun y => Z (Classical.choose y.2)
              have hkeyRange : Measurable keyRange := by
                refine measurable_to_countable ?_
                intro omega
                have hset : MeasurableSet (key ⁻¹' {key omega}) :=
                  hkey_meas' (measurableSet_singleton (key omega))
                convert hset using 1
                ext omega'
                simp [keyRange]
              have hG : Measurable G := measurable_of_finite G
              have hZG : Z = G ∘ keyRange := by
                funext omega
                dsimp [Function.comp, G, keyRange, Z]
                have hkey :
                    key (Classical.choose (show key omega ∈ Set.range key from ⟨omega, rfl⟩)) =
                      key omega :=
                  Classical.choose_spec (show key omega ∈ Set.range key from ⟨omega, rfl⟩)
                have hstate_eq :
                    state r (Classical.choose (show key omega ∈ Set.range key from ⟨omega, rfl⟩)) =
                      state r omega :=
                  congrArg Prod.fst hkey
                have hblock_eq :
                    block (r + 1)
                        (Classical.choose (show key omega ∈ Set.range key from ⟨omega, rfl⟩)) =
                      block (r + 1) omega :=
                  congrArg Prod.snd hkey
                simp [hstate_eq, hblock_eq]
              change Measurable Z
              rw [hZG]
              exact hG.comp hkeyRange
            simpa [h_update r] using hfactor_meas
          have hnext_finite : (Set.range (state (r + 1))).Finite := by
            have hsubset :
                Set.range (state (r + 1)) <=
                  (fun xu : X × U (r + 1) => stepEpoch r xu.1 xu.2) '' Set.range key := by
              rintro x ⟨omega, rfl⟩
              refine ⟨key omega, ⟨omega, rfl⟩, ?_⟩
              exact (congrFun (h_update r) omega).symm
            exact (hkey_finite.image (fun xu : X × U (r + 1) => stepEpoch r xu.1 xu.2)).subset hsubset
          exact ⟨by simpa using hnext_meas, by simpa using hnext_finite⟩

/-- Assemble a dependent subtype-valued family after one selected-coordinate update.

At the sampled coordinate this returns the supplied candidate certificate. At
every other coordinate it reuses the previous certificate, transporting its
proof across the stated off-coordinate equality of the new and previous data.

Layer: Model | Concept: Iterates
Proof: (definitional construction; selected coordinate branch plus dependent
  proof transport for unchanged off coordinates)
Source: Mathlib subtype APIs and coordinate-update case splits
Used in: random primal-dual gradient sampled dual subgradient-certificate update
  after the sampled dual prox step
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
noncomputable def selectedCoordinateSubtypeUpdate
    {ι V : Type*} [DecidableEq ι] {Y : ι → Type*}
    (P : (i : ι) → Y i → V → Prop)
    (yPrev yNext : (i : ι) → Y i)
    (base : (i : ι) → {v : V // P i (yPrev i) v})
    (sampled : ι)
    (candidate : {v : V // P sampled (yNext sampled) v})
    (h_off : ∀ {i : ι}, i ≠ sampled → yNext i = yPrev i) :
    (i : ι) → {v : V // P i (yNext i) v} :=
  fun i => by
    by_cases h : i = sampled
    · subst i
      exact candidate
    · exact
        ⟨(base i).1, by
          simpa [h_off h] using (base i).2⟩

@[simp]
theorem selectedCoordinateSubtypeUpdate_def
    {ι V : Type*} [DecidableEq ι] {Y : ι → Type*}
    (P : (i : ι) → Y i → V → Prop)
    (yPrev yNext : (i : ι) → Y i)
    (base : (i : ι) → {v : V // P i (yPrev i) v})
    (sampled : ι)
    (candidate : {v : V // P sampled (yNext sampled) v})
    (h_off : ∀ {i : ι}, i ≠ sampled → yNext i = yPrev i) :
    selectedCoordinateSubtypeUpdate P yPrev yNext base sampled candidate h_off =
      fun i => by
        by_cases h : i = sampled
        · subst i
          exact candidate
        · exact
            ⟨(base i).1, by
              simpa [h_off h] using (base i).2⟩ := rfl

/-- The selected coordinate of `selectedCoordinateSubtypeUpdate` has the
candidate's stored value.

Layer: Model | Gap: Level 0 (selected-coordinate subtype update selected value)
Proof: unfold `selectedCoordinateSubtypeUpdate` and simplify the selected
  equality branch.
Source: Mathlib subtype projection and coordinate-update case splits
Used in: random primal-dual gradient sampled dual subgradient-certificate
  selected-block equation
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
@[simp]
theorem selectedCoordinateSubtypeUpdate_sampled_coe
    {ι V : Type*} [DecidableEq ι] {Y : ι → Type*}
    (P : (i : ι) → Y i → V → Prop)
    (yPrev yNext : (i : ι) → Y i)
    (base : (i : ι) → {v : V // P i (yPrev i) v})
    (sampled : ι)
    (candidate : {v : V // P sampled (yNext sampled) v})
    (h_off : ∀ {i : ι}, i ≠ sampled → yNext i = yPrev i) :
    (selectedCoordinateSubtypeUpdate P yPrev yNext base sampled candidate h_off
        sampled).1 =
      candidate.1 := by
  simp [selectedCoordinateSubtypeUpdate]

/-- A non-selected coordinate of `selectedCoordinateSubtypeUpdate` keeps the
previous certificate's stored value.

Layer: Model | Gap: Level 0 (selected-coordinate subtype update off value)
Proof: unfold `selectedCoordinateSubtypeUpdate`, take the non-selected branch,
  and simplify the stored subtype projection.
Source: Mathlib subtype projection and coordinate-update case splits
Used in: random primal-dual gradient sampled dual subgradient-certificate
  off-block equation
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
@[simp]
theorem selectedCoordinateSubtypeUpdate_of_ne_coe
    {ι V : Type*} [DecidableEq ι] {Y : ι → Type*}
    (P : (i : ι) → Y i → V → Prop)
    (yPrev yNext : (i : ι) → Y i)
    (base : (i : ι) → {v : V // P i (yPrev i) v})
    {sampled i : ι}
    (candidate : {v : V // P sampled (yNext sampled) v})
    (h_off : ∀ {i : ι}, i ≠ sampled → yNext i = yPrev i)
    (hi : i ≠ sampled) :
    (selectedCoordinateSubtypeUpdate P yPrev yNext base sampled candidate h_off
        i).1 =
      (base i).1 := by
  simp [selectedCoordinateSubtypeUpdate, hi]

/-- Coordinatewise finite normalized weighted output average in a dependent product.

For coordinate carriers `Y i`, a common finite output window, nonnegative
weights, and subtype-valued coordinate iterates, this constructs the product
point whose `i`th coordinate is the normalized weighted average in `Y i`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; dependent product of the existing
  single-carrier weighted-output constructor)
Source: Mathlib finite sums, real module scalar multiplication, subtype
  projection, and convex finite-combination APIs
Used in: random primal-dual gradient coordinatewise dual weighted output before
  applying finite Jensen bounds to the dual product
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
noncomputable def piWeightedOutputAverage
    {Ω T W ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (Y : ∀ i, Set (E i))
    (times : W → Finset T)
    (weight : T → ℝ)
    (y : T → Ω → (i : ι) → {v : E i // v ∈ Y i})
    (Wsum : W → ℝ)
    (hY_convex : ∀ i, Convex ℝ (Y i))
    (hweight_nonneg : ∀ w t, t ∈ times w → 0 ≤ weight t)
    (hW_pos : ∀ w, 0 < Wsum w)
    (hW_eq : ∀ w, Wsum w = Finset.sum (times w) weight)
    (w : W) : Ω → (i : ι) → {v : E i // v ∈ Y i} :=
  fun ω i =>
    weightedOutputAverage
      (Y i)
      times
      weight
      (fun t ω => (y t ω i).1)
      Wsum
      (hY_convex i)
      hweight_nonneg
      (fun _ t _ ω => (y t ω i).2)
      hW_pos
      hW_eq
      w
      ω

/-- Coordinatewise characterization of the dependent product weighted output average.

At each sample and coordinate, `piWeightedOutputAverage` is the corresponding
single-carrier `weightedOutputAverage`.

Layer: Model | Gap: Level 0 (dependent product weighted-output definition)
Proof: by rfl after unfolding `piWeightedOutputAverage`.
Source: Mathlib function application and subtype APIs
Used in: simplifying dependent product weighted outputs to their coordinatewise
  weighted averages
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
@[simp]
theorem piWeightedOutputAverage_def
    {Ω T W ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (Y : ∀ i, Set (E i))
    (times : W → Finset T)
    (weight : T → ℝ)
    (y : T → Ω → (i : ι) → {v : E i // v ∈ Y i})
    (Wsum : W → ℝ)
    (hY_convex : ∀ i, Convex ℝ (Y i))
    (hweight_nonneg : ∀ w t, t ∈ times w → 0 ≤ weight t)
    (hW_pos : ∀ w, 0 < Wsum w)
    (hW_eq : ∀ w, Wsum w = Finset.sum (times w) weight)
    (w : W) (ω : Ω) (i : ι) :
    piWeightedOutputAverage Y times weight y Wsum hY_convex hweight_nonneg
        hW_pos hW_eq w ω i =
      weightedOutputAverage
        (Y i)
        times
        weight
        (fun t ω => (y t ω i).1)
        Wsum
        (hY_convex i)
        hweight_nonneg
        (fun _ t _ ω => (y t ω i).2)
        hW_pos
        hW_eq
        w
        ω := by
  rfl

/-- A coordinate of the dependent product weighted output average remains in
its coordinate carrier.

Layer: Model | Gap: Level 0 (dependent product weighted-output feasibility)
Proof: the coordinate output is subtype-valued, so its second projection is the
  carrier-membership witness.
Source: Mathlib subtype and Set membership APIs
Used in: coordinatewise feasibility goals for product-valued weighted outputs
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem piWeightedOutputAverage_mem
    {Ω T W ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (Y : ∀ i, Set (E i))
    (times : W → Finset T)
    (weight : T → ℝ)
    (y : T → Ω → (i : ι) → {v : E i // v ∈ Y i})
    (Wsum : W → ℝ)
    (hY_convex : ∀ i, Convex ℝ (Y i))
    (hweight_nonneg : ∀ w t, t ∈ times w → 0 ≤ weight t)
    (hW_pos : ∀ w, 0 < Wsum w)
    (hW_eq : ∀ w, Wsum w = Finset.sum (times w) weight)
    (w : W) (ω : Ω) (i : ι) :
    (piWeightedOutputAverage Y times weight y Wsum hY_convex hweight_nonneg
        hW_pos hW_eq w ω i).1 ∈ Y i := by
  exact (piWeightedOutputAverage Y times weight y Wsum hY_convex
    hweight_nonneg hW_pos hW_eq w ω i).2

/-- A coordinate projection of the dependent product weighted output is the
normalized weighted average of that coordinate process.

Layer: Model | Gap: Level 0 (dependent product weighted-output projection)
Proof: by rfl after unfolding `piWeightedOutputAverage` and the underlying
  single-carrier `weightedOutputAverage`.
Source: Mathlib finite sums, real module scalar actions, and subtype projection
  APIs
Used in: random primal-dual gradient rewriting the product dual output to the
  coordinate weighted sum needed by Jensen and saddle-gap estimates
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
@[simp]
theorem piWeightedOutputAverage_val
    {Ω T W ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (Y : ∀ i, Set (E i))
    (times : W → Finset T)
    (weight : T → ℝ)
    (y : T → Ω → (i : ι) → {v : E i // v ∈ Y i})
    (Wsum : W → ℝ)
    (hY_convex : ∀ i, Convex ℝ (Y i))
    (hweight_nonneg : ∀ w t, t ∈ times w → 0 ≤ weight t)
    (hW_pos : ∀ w, 0 < Wsum w)
    (hW_eq : ∀ w, Wsum w = Finset.sum (times w) weight)
    (w : W) (ω : Ω) (i : ι) :
    (piWeightedOutputAverage Y times weight y Wsum hY_convex hweight_nonneg
        hW_pos hW_eq w ω i).1 =
      (Wsum w)⁻¹ • Finset.sum (times w) (fun t => weight t • (y t ω i).1) := by
  rfl

end SOptLib

-- Merged from Staging/relaxedMemoryRefreshPoint_solve.lean
namespace SOptLib

-- Generalization plan (G0):
-- concept/name: relaxed memory-refresh point solved for the proposal; orig was
--   `auxiliaryPoint_solve`, renamed away from the RGEM auxiliary-point notation
--   and attached to the existing Model definition `relaxedMemoryRefreshPoint`.
-- generality used: arbitrary real module over an additive commutative group;
--   no measure, filtration, finite-dimensionality, convexity, smoothness, oracle,
--   or algorithm-state assumptions are used.
-- portable call pattern: accelerated finite-sum and memory-refresh proofs rewrite
--   a refreshed point `(1 + tau)⁻¹ • (proposal + tau • memory)` back into the
--   proposal while changing `tau`, `proposal`, and `memory`.
-- counterargument checked: this is a one-line algebraic solve, but it is not
--   paper-local traceability because it targets the reusable Model object already
--   used by randomized accelerated proximal-point and variance-reduced memory
--   refreshes; it is not a pure rename of Mathlib or SOptLib API.
-- coverage search: searched CATALOG/SOptLib/Staging for
--   `relaxedMemoryRefreshPoint`, `memory refresh solve`, and `auxiliaryPoint_solve`;
--   existing hits provide only the forward definition and convex feasibility.
--   LeanSearch for solving this affine formula returned no Mathlib lemma tied to
--   the named memory-refresh point.
-- minimal hypotheses: the original nonnegativity hypothesis is weakened to the
--   exact algebraic requirement `(1 + tau) ≠ 0`.

/-- A relaxed memory-refresh point can be rearranged to recover its proposal.

If `relaxedMemoryRefreshPoint tau proposal memory` is the weighted average
`(1 + tau)⁻¹ • (proposal + tau • memory)` and the denominator is nonzero, then
the proposal equals `(1 + tau)` times the refreshed point minus `tau` times the
stale memory.

Layer: Model | Gap: Level 0 (relaxed memory-refresh proposal solve)
Proof: unfold `relaxedMemoryRefreshPoint`, cancel `(1 + tau) * (1 + tau)⁻¹`,
  and normalize the additive group expression.
Source: Mathlib module scalar multiplication, inverse cancellation, and additive
  commutative-group normalization APIs
Used in: randomized gradient extrapolation auxiliary-point expansion for
  component-memory refreshes
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/parameters/1/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem relaxedMemoryRefreshPoint_solve
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {tau : ℝ} (hden : (1 : ℝ) + tau ≠ 0) (proposal memory : E) :
    proposal =
      ((1 : ℝ) + tau) • relaxedMemoryRefreshPoint tau proposal memory -
        tau • memory := by
  rw [relaxedMemoryRefreshPoint_def]
  rw [smul_smul, mul_inv_cancel₀ hden]
  simp [sub_eq_add_neg, add_assoc]

-- Generalization plan (G0):
-- concept/name: recursive-momentum iterate state; orig was `State`
-- generality used: arbitrary iterate/direction carrier `E` and accumulator carrier `R`;
--   no algebraic, measurable, measure, convexity, smoothness, or oracle assumptions
-- portable call pattern: recursive-momentum and adaptive-gradient transitions that update
--   an iterate, a same-carrier direction estimate, and an accumulated statistic; both the
--   vector carrier and accumulator representation may change
-- counterargument checked: this is not paper-only bookkeeping or a product rename because
--   the named coordinates form the public interface used by initialization, transitions,
--   generated processes, and measurability proofs; nearby SOptLib records have different
--   invariants or fixed counter shapes
-- coverage search: queries "recursive momentum state iterate direction accumulated statistic
--   structure" and "state with iterate direction accumulator"; closest SOptLib hits were
--   `ConditionalGradientState`, `FeasibleAcceleratedState`, and `BlockIterateState`, all partial;
--   Mathlib semantic search returned only unrelated estimator and map-accumulator APIs
-- minimal hypotheses: all already minimal after removing the unused normed-group and
--   normed-space typeclasses from the original declaration

/-- State of a recursive-momentum iteration, carrying its iterate, direction estimate,
and accumulated statistic.

Layer: Model | Concept: recursive-momentum iterate state
Proof: (definitional construction; bundled iterate, same-carrier recursive direction estimate,
  and independently typed accumulated statistic)
Source: recursive-momentum and adaptive-gradient algorithm-state notation
Used in: recursive-momentum initialization and sample-driven transitions that jointly update
  the iterate, direction estimate, and cumulative gradient statistic
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD,
  STOchastic Recursive Momentum (STORM) -/
@[ext]
structure RecursiveMomentumState (E R : Type*) where
  x : E
  direction : E
  gradNormSqSum : R

namespace RecursiveMomentumState

/-- The iterate projection of a state built from coordinates is the supplied iterate. -/
@[simp]
theorem mk_x {E R : Type*} (x direction : E) (gradNormSqSum : R) :
    (RecursiveMomentumState.mk x direction gradNormSqSum).x = x := by
  rfl

/-- The direction projection of a state built from coordinates is the supplied direction. -/
@[simp]
theorem mk_direction {E R : Type*} (x direction : E) (gradNormSqSum : R) :
    (RecursiveMomentumState.mk x direction gradNormSqSum).direction = direction := by
  rfl

/-- The accumulator projection of a state built from coordinates is the supplied accumulator. -/
@[simp]
theorem mk_gradNormSqSum {E R : Type*} (x direction : E) (gradNormSqSum : R) :
    (RecursiveMomentumState.mk x direction gradNormSqSum).gradNormSqSum = gradNormSqSum := by
  rfl

end RecursiveMomentumState

/-- The measurable space on a recursive-momentum state generated by its three coordinates.

Layer: Model | Concept: recursive-momentum iterate state
Proof: (definitional construction; supremum of the three coordinate-comap
  measurable spaces)
Source: Mathlib measure-theory measurable-space comap APIs
Used in: measurability of recursive-momentum and adaptive-gradient state processes -/
@[reducible]
def recursiveMomentumStateMeasurableSpace
    {E R : Type*} [MeasurableSpace E] [MeasurableSpace R] :
    MeasurableSpace (RecursiveMomentumState E R) :=
  MeasurableSpace.comap (fun s : RecursiveMomentumState E R => s.x) inferInstance ⊔
    MeasurableSpace.comap (fun s : RecursiveMomentumState E R => s.direction) inferInstance ⊔
      MeasurableSpace.comap
        (fun s : RecursiveMomentumState E R => s.gradNormSqSum) inferInstance

/-- The recursive-momentum state measurable space unfolds to the supremum of its
three coordinate-comap measurable spaces. -/
@[simp]
theorem recursiveMomentumStateMeasurableSpace_def
    {E R : Type*} [MeasurableSpace E] [MeasurableSpace R] :
    (recursiveMomentumStateMeasurableSpace :
      MeasurableSpace (RecursiveMomentumState E R)) =
      MeasurableSpace.comap (fun s : RecursiveMomentumState E R => s.x) inferInstance ⊔
        MeasurableSpace.comap
            (fun s : RecursiveMomentumState E R => s.direction) inferInstance ⊔
          MeasurableSpace.comap
            (fun s : RecursiveMomentumState E R => s.gradNormSqSum) inferInstance := by
  rfl

/-- The iterate coordinate is measurable for the coordinate-generated state
measurable space. -/
theorem recursiveMomentumState_x_measurable
    {E R : Type*} [MeasurableSpace E] [MeasurableSpace R] :
    @Measurable (RecursiveMomentumState E R) E
      recursiveMomentumStateMeasurableSpace inferInstance
      (fun s => s.x) := by
  exact Measurable.of_comap_le (le_sup_left.trans le_sup_left)

/-- The recursive direction coordinate is measurable for the coordinate-generated
state measurable space. -/
theorem recursiveMomentumState_direction_measurable
    {E R : Type*} [MeasurableSpace E] [MeasurableSpace R] :
    @Measurable (RecursiveMomentumState E R) E
      recursiveMomentumStateMeasurableSpace inferInstance
      (fun s => s.direction) := by
  exact Measurable.of_comap_le (le_sup_right.trans le_sup_left)

/-- The accumulated-statistic coordinate is measurable for the coordinate-generated
state measurable space. -/
theorem recursiveMomentumState_gradNormSqSum_measurable
    {E R : Type*} [MeasurableSpace E] [MeasurableSpace R] :
    @Measurable (RecursiveMomentumState E R) R
      recursiveMomentumStateMeasurableSpace inferInstance
      (fun s => s.gradNormSqSum) := by
  exact Measurable.of_comap_le le_sup_right

/-- Measurable coordinate processes assemble into a measurable recursive-momentum
state process for the coordinate-generated state measurable space. -/
theorem recursiveMomentumState_mk_measurable
    {Ω E R : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace R]
    {x direction : Ω → E} {gradNormSqSum : Ω → R}
    (hx : Measurable x) (hdirection : Measurable direction)
    (hgradNormSqSum : Measurable gradNormSqSum) :
    @Measurable Ω (RecursiveMomentumState E R) inferInstance
      recursiveMomentumStateMeasurableSpace
      (fun ω => RecursiveMomentumState.mk (x ω) (direction ω) (gradNormSqSum ω)) := by
  apply Measurable.of_comap_le
  simp only [recursiveMomentumStateMeasurableSpace_def, MeasurableSpace.comap_sup,
    MeasurableSpace.comap_comp]
  exact sup_le (sup_le hx.comap_le hdirection.comap_le) hgradNormSqSum.comap_le

-- Generalization plan (G0):
-- concept/name: sample-path recursive process with a random initial slice;
--   orig was stateProcess
-- generality used: arbitrary sample-path type Ω and state type State; no
--   topology, algebra, measurable space, measure, or probability assumptions
-- portable call pattern: stochastic-gradient, recursive-momentum, and
--   variance-reduced algorithms whose first oracle sample initializes the state;
--   the state type, initial random variable, and pathwise transition may vary
-- counterargument checked: this is not only a paper wrapper: unlike
--   SOptLib.recursiveIterateProcess, its initial slice may depend on ω, and the
--   zero/successor API avoids encoding that difference through a lifted state
--   space and a dummy outer sample type
-- coverage search: queries “recursive stochastic process random initial state
--   omega dependent transition zero successor equations” and “natural number
--   recursive process from initial function and transition”; the closest hit is
--   SOptLib.recursiveIterateProcess in SOptLib/Model/Iterates.lean, whose full
--   signature requires a constant initial state, so coverage is partial
-- minimal hypotheses: all already minimal; primitive recursion needs only the
--   two carrier types, an Ω-indexed initial value, and a time-indexed transition

/-- The canonical natural-number process generated from a path-dependent initial
state and a path-dependent transition.

Layer: Model | Concept: recursive stochastic process with random initialization
Proof: (definitional construction; primitive recursion over natural time with an Ω-indexed base case)
Source: Mathlib natural-number primitive recursion and Pi-function APIs
Used in: pathwise stochastic algorithms whose first oracle sample initializes the state before recursive updates
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STORM -/
def recursive_process_from_random_initial
    {Ω State : Type*}
    (initial : Ω → State)
    (step : ℕ → State → Ω → State) :
    ℕ → Ω → State
  | 0 => initial
  | n + 1 => fun ω =>
      step n (recursive_process_from_random_initial initial step n ω) ω

/-- A process from a random initial slice unfolds to its initial slice at zero.

Layer: Model | Gap: Level 0 (random-initial recursive process definition)
Proof: by rfl after unfolding recursive_process_from_random_initial.
Source: Mathlib natural-number primitive recursion and Pi-function APIs
Used in: controlled simplification of pathwise stochastic recursive processes
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STORM -/
@[simp]
theorem recursive_process_from_random_initial_def
    {Ω State : Type*}
    (initial : Ω → State)
    (step : ℕ → State → Ω → State) :
    recursive_process_from_random_initial initial step 0 = initial := by
  rfl

/-- A process generated from a random initial slice equals that slice at time zero.

Layer: Model | Gap: Level 0 (random-initial recursive process base equation)
Proof: by rfl after unfolding recursive_process_from_random_initial.
Source: Mathlib natural-number primitive recursion and Pi-function extensionality APIs
Used in: identifying the first-sample initialization of a pathwise stochastic algorithm
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/initialization
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STORM -/
@[simp]
theorem recursive_process_from_random_initial_zero
    {Ω State : Type*}
    (initial : Ω → State)
    (step : ℕ → State → Ω → State) :
    recursive_process_from_random_initial initial step 0 = initial := by
  rfl

/-- A process generated from a random initial slice applies its transition
pointwise at successor time.

Layer: Model | Gap: Level 0 (random-initial recursive process successor equation)
Proof: by rfl after unfolding recursive_process_from_random_initial.
Source: Mathlib natural-number primitive recursion and Pi-function APIs
Used in: unfolding one recursive update of a sample-path stochastic state process
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STORM -/
@[simp]
theorem recursive_process_from_random_initial_succ
    {Ω State : Type*}
    (initial : Ω → State)
    (step : ℕ → State → Ω → State)
    (n : ℕ) :
    recursive_process_from_random_initial initial step (n + 1) =
      fun ω => step n (recursive_process_from_random_initial initial step n ω) ω := by
  rfl

/-- A set invariant that contains every random initial state and is preserved by
the transition contains every state of the generated process.

Layer: Model | Gap: Level 1 (random-initial recursive process invariant propagation)
Proof: by induction on time, using initial membership at zero and transition preservation at successors.
Source: Mathlib natural-number induction and set-membership APIs
Used in: feasibility and state-validity proofs for pathwise stochastic algorithms with random initialization
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STORM -/
theorem recursive_process_from_random_initial_invariant_mem
    {Ω State : Type*}
    {s : Set State}
    (initial : Ω → State)
    (step : ℕ → State → Ω → State)
    (h_initial : ∀ ω, initial ω ∈ s)
    (h_step : ∀ n state ω, state ∈ s → step n state ω ∈ s) :
    ∀ n ω, recursive_process_from_random_initial initial step n ω ∈ s := by
  intro n
  induction n with
  | zero =>
      exact h_initial
  | succ n ih =>
      intro ω
      exact h_step n _ ω (ih ω)

-- Generalization plan (G0):
-- concept/name: recursive-momentum initial state; orig was `initialState`
-- generality used: arbitrary sample-path type `Ω`, sample type `Sample`, and
--   carrier `E` equipped only with a norm; no additive, measure, probability, inner-product,
--   completeness, convexity, smoothness, or oracle-regularity assumptions
-- portable call pattern: recursive-momentum and adaptive-gradient methods initialize
--   an iterate at `x0`, set the direction to a first sampled oracle value, and seed
--   a cumulative second-moment statistic with its squared norm; the point, oracle,
--   and first-sample map may all change while the state contract remains unchanged
-- counterargument checked: although the construction is definitional, it is not a
--   caller-side composition or record-constructor rename: it names the coupled
--   first-oracle initialization invariant used by later direction and accumulator
--   proofs, and ships a characterizing simplification theorem
-- coverage search: searched "recursive momentum initial state first oracle direction
--   squared norm accumulator" and "state initialization direction equals oracle value
--   accumulator squared norm"; the closest project hit was `RecursiveMomentumState`,
--   which provides the result record but no initialization, while Mathlib semantic
--   search returned norm-square identities and no state constructor
-- minimal hypotheses: `Norm E` supplies exactly the real-valued norm used in the
--   squared-norm accumulator; all additive, Hilbert, and completeness assumptions
--   from the source are unnecessary

/-- Initialize a recursive-momentum state from the first sampled oracle value.

The iterate is `x0`, the initial direction is the oracle value at `x0` and the
first sample, and the accumulated gradient statistic is that value's squared norm.

Layer: Model | Concept: recursive-momentum first-oracle state initialization
Proof: (definitional construction; evaluate the first sampled oracle once and store
  the point, oracle value, and its squared norm in `RecursiveMomentumState`)
Source: stochastic recursive-momentum and adaptive-gradient initialization notation
Used in: recursive-momentum and adaptive-gradient base states before pathwise sampled
  transitions update the iterate, direction estimate, and cumulative second moment
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/initialization
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex
  SGD, STOchastic Recursive Momentum (STORM) -/
def recursiveMomentumInitialState
    {Ω Sample E : Type*} [Norm E]
    (x0 : E) (oracle : E → Sample → E) (sample0 : Ω → Sample) :
    Ω → RecursiveMomentumState E ℝ :=
  fun ω =>
    let g := oracle x0 (sample0 ω)
    { x := x0
      direction := g
      gradNormSqSum := ‖g‖ ^ 2 }

/-- A recursive-momentum initial state has the initial point, first sampled oracle
value, and squared norm of that same value as its three coordinates.

Layer: Model | Gap: Level 0 (recursive-momentum initialization unfolding)
Proof: by rfl after unfolding `recursiveMomentumInitialState` and reducing its local
  first-oracle binding
Source: Mathlib norm notation and `RecursiveMomentumState` constructor projections
Used in: base-case proofs identifying the initial iterate, direction estimate, and
  cumulative gradient-square statistic of recursive-momentum state processes
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/initialization
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex
  SGD, STOchastic Recursive Momentum (STORM) -/
@[simp]
theorem recursiveMomentumInitialState_def
    {Ω Sample E : Type*} [Norm E]
    (x0 : E) (oracle : E → Sample → E) (sample0 : Ω → Sample) (ω : Ω) :
    recursiveMomentumInitialState x0 oracle sample0 ω =
      { x := x0
        direction := oracle x0 (sample0 ω)
        gradNormSqSum := ‖oracle x0 (sample0 ω)‖ ^ 2 } := by
  rfl

/-- The cumulative squared-norm statistic of an initialized recursive-momentum
state is nonnegative.

Layer: Model | Gap: Level 0 (recursive-momentum initial accumulator nonnegativity)
Proof: unfold the initialized accumulator and apply nonnegativity of a real square
Source: Mathlib `sq_nonneg` for the squared norm stored by the initializer
Used in: base cases for nonnegative cumulative second-moment statistics in
  recursive-momentum and adaptive-gradient state processes -/
theorem recursiveMomentumInitialState_gradNormSqSum_nonneg
    {Ω Sample E : Type*} [Norm E]
    (x0 : E) (oracle : E → Sample → E) (sample0 : Ω → Sample) (ω : Ω) :
    0 ≤ (recursiveMomentumInitialState x0 oracle sample0 ω).gradNormSqSum := by
  rw [recursiveMomentumInitialState_def]
  exact sq_nonneg _

-- Generalization plan (G0):
-- concept/name: sample-driven recursive-momentum state transition; orig was
--   `stateStepFromSample`
-- generality used: arbitrary sample type and carrier with an additive group, real scalar
--   action, and norm; the oracle,
--   accumulator-to-step schedule, and step-to-momentum-weight schedule are explicit;
--   no measure, probability, finite-dimensionality, inner-product, completeness,
--   convexity, smoothness, or oracle-regularity assumptions are used
-- portable call pattern: recursive-momentum, STORM-family, and same-sample
--   variance-reduced methods update an iterate, correct a direction estimator using
--   one sample at the old and new points, and extend a cumulative squared-norm
--   statistic; the oracle and both scalar schedules may change while the state
--   transition contract remains the same
-- counterargument checked: although definitional, this is not a caller-side record
--   constructor or paper traceability wrapper: it names a coupled four-stage update
--   used as a sample kernel by recursive processes and ships both a characterizing
--   equation and preservation of accumulator nonnegativity
-- coverage search: queries "recursive momentum state transition same sample correction
--   accumulated squared oracle norm" and "state update direction estimator accumulator
--   oracle sample step size momentum weight" found only `RecursiveMomentumState`,
--   its initializer, generic recursive-process APIs, and a structurally different
--   accelerated-state sample bridge; Mathlib semantic search returned no matching
--   stochastic recursive-momentum transition
-- minimal hypotheses: weakened the source's Hilbert and complete-space assumptions to
--   `AddGroup E`, `SMul ℝ E`, and `Norm E`, exactly supporting subtraction, real scalar
--   multiplication, and the squared norm

/-- Advance a recursive-momentum state using one newly supplied oracle sample.

The step schedule is evaluated on the stored accumulator. The same sample is
then used for oracle values at the updated and previous iterates, producing the
recursive direction correction and the next cumulative squared-norm statistic.

Layer: Model | Concept: sample-driven recursive-momentum state transition
Proof: (definitional construction; compute the adaptive primal step, two same-sample oracle values, recursive direction correction, and squared-norm accumulator update)
Source: stochastic recursive-momentum and same-sample variance-reduction update equations over Mathlib real normed spaces
Used in: recursive-momentum and STORM-family sample kernels that generate pathwise states from an oracle and adaptive scalar schedules
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum (STORM) -/
def recursive_momentum_step_from_sample
    {Sample E : Type*} [AddGroup E] [SMul ℝ E] [Norm E]
    (oracle : E → Sample → E)
    (stepSize : ℝ → ℝ)
    (momentumWeight : ℝ → ℝ)
    (state : RecursiveMomentumState E ℝ)
    (sampleNext : Sample) : RecursiveMomentumState E ℝ :=
  let η := stepSize state.gradNormSqSum
  let xNext := state.x - η • state.direction
  let gNext := oracle xNext sampleNext
  let correction := oracle state.x sampleNext
  let aNext := momentumWeight η
  { x := xNext
    direction := gNext + (1 - aNext) • (state.direction - correction)
    gradNormSqSum := state.gradNormSqSum + ‖gNext‖ ^ 2 }

/-- The sample-driven recursive-momentum transition unfolds to its primal,
same-sample direction-correction, and cumulative squared-norm coordinates.

Layer: Model | Gap: Level 0 (recursive-momentum sample-step unfolding)
Proof: by rfl after unfolding `recursive_momentum_step_from_sample` and reducing its local bindings
Source: Mathlib normed-space subtraction, real scalar multiplication, and norm notation together with `RecursiveMomentumState` constructor projections
Used in: coordinate proofs for generated recursive-momentum iterates, direction estimators, and accumulated sampled-gradient squares
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum (STORM) -/
@[simp]
theorem recursive_momentum_step_from_sample_def
    {Sample E : Type*} [AddGroup E] [SMul ℝ E] [Norm E]
    (oracle : E → Sample → E)
    (stepSize momentumWeight : ℝ → ℝ)
    (state : RecursiveMomentumState E ℝ)
    (sampleNext : Sample) :
    recursive_momentum_step_from_sample oracle stepSize momentumWeight state sampleNext =
      let η := stepSize state.gradNormSqSum
      let xNext := state.x - η • state.direction
      let gNext := oracle xNext sampleNext
      let correction := oracle state.x sampleNext
      let aNext := momentumWeight η
      { x := xNext
        direction := gNext + (1 - aNext) • (state.direction - correction)
        gradNormSqSum := state.gradNormSqSum + ‖gNext‖ ^ 2 } := by
  rfl

/-- A sample-driven recursive-momentum step preserves nonnegativity of the
cumulative squared-norm statistic.

Layer: Model | Gap: Level 1 (recursive-momentum accumulator nonnegativity preservation)
Proof: unfold the transition and add the assumed nonnegative accumulator to the nonnegative square of the new oracle norm
Source: Mathlib ordered-ring lemmas `add_nonneg` and `sq_nonneg` for real-valued squared norms
Used in: inductive invariants for adaptive step schedules driven by cumulative sampled-gradient squares
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum (STORM) -/
theorem recursive_momentum_step_from_sample_grad_norm_sq_sum_nonneg
    {Sample E : Type*} [AddGroup E] [SMul ℝ E] [Norm E]
    (oracle : E → Sample → E)
    (stepSize momentumWeight : ℝ → ℝ)
    (state : RecursiveMomentumState E ℝ)
    (sampleNext : Sample)
    (hstate : 0 ≤ state.gradNormSqSum) :
    0 ≤ (recursive_momentum_step_from_sample oracle stepSize momentumWeight state sampleNext).gradNormSqSum := by
  rw [recursive_momentum_step_from_sample_def]
  exact add_nonneg hstate (sq_nonneg _)

/-- The iterate coordinate of a generated recursive-momentum process advances
by subtracting the scheduled multiple of its current direction.

Layer: Model | Gap: Level 1 (generated recursive-momentum iterate-coordinate successor equation)
Proof: unfold the random-initial process at successor time, reduce the sample-driven recursive-momentum transition, and project its iterate coordinate
Source: Mathlib natural-number primitive recursion, additive-group subtraction, and real scalar-action APIs together with `recursive_process_from_random_initial_succ` and `recursive_momentum_step_from_sample_def`
Used in: STORM-family recursive-momentum proofs that expose the primal update before descent, adaptedness, or integrability arguments
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps/2/math
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum (STORM) -/
theorem recursive_momentum_iterate_succ
    {Ω Sample E : Type*} [AddGroup E] [SMul ℝ E] [Norm E]
    (oracle : E → Sample → E)
    (sample : ℕ → Ω → Sample)
    (step_size weight : ℝ → ℝ)
    (initial : Ω → RecursiveMomentumState E ℝ)
    (n : ℕ) (ω : Ω) :
    let process :=
      recursive_process_from_random_initial initial
        (fun n state ω =>
          recursive_momentum_step_from_sample oracle step_size weight state
            (sample (n + 1) ω))
    (process (n + 1) ω).x =
      (process n ω).x - step_size (process n ω).gradNormSqSum •
        (process n ω).direction := by
  rfl

-- Generalization plan (G0):
-- concept/name: totality of an Option-valued recursive process from successful
--   step simulation; orig was sourceStateProcess_eq_some_stateProcess_of_generated_boundary
-- generality used: arbitrary sample-path and state types with no topology,
--   algebra, measurable-space, measure, probability, or finiteness assumptions
-- portable call pattern: checked stochastic-gradient, adaptive-momentum, and
--   variance-reduced recursions prove that their partial source process shadows
--   a total process; the initial state, transitions, and success proof vary
--   while the pointwise `partial = some total` conclusion stays unchanged
-- counterargument checked: the result is not paper-local traceability or a
--   one-line wrapper; it packages the reusable induction that propagates
--   successful checked transitions through an Option-valued recursion
-- coverage search: searched “partial recursive process equals some total
--   recursive process when every step succeeds”, “Option recursion equality
--   some successor step”, and Mathlib semantic search for the same contract;
--   SOptLib recursive-process hits provide successor or determinism lemmas,
--   while Mathlib Stream'.Seq corec lemmas concern a different coinductive API,
--   so coverage is partial and no existing theorem has this signature
-- minimal hypotheses: all already minimal; only the two base equations, two
--   successor equations, and pointwise successful-step simulation are used

/-- An Option-valued recursive process equals `some` of a total recursive process
when every checked transition along the total process succeeds with the same step.

Layer: Model | Gap: Level 1 (partial recursive-process totality by step simulation)
Proof: induction on natural time; the base equations identify the initial slice, and the successor equations reduce the claim to the successful-step hypothesis.
Source: Mathlib natural-number induction and Option bind reduction APIs
Used in: proving checked adaptive stochastic-optimization state recursions agree pointwise with their total arithmetic realizations
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STORM -/
theorem partialRecursiveProcess_eq_some_of_step_eq_some
    {Ω State : Type*}
    (partialProcess : ℕ → Ω → Option State)
    (total : ℕ → Ω → State)
    (partialStep : ℕ → State → Ω → Option State)
    (totalStep : ℕ → State → Ω → State)
    (initial : Ω → State)
    (h_partial_zero : ∀ ω, partialProcess 0 ω = some (initial ω))
    (h_total_zero : ∀ ω, total 0 ω = initial ω)
    (h_partial_succ : ∀ n ω,
      partialProcess (n + 1) ω =
        (partialProcess n ω).bind (fun state => partialStep n state ω))
    (h_total_succ : ∀ n ω, total (n + 1) ω = totalStep n (total n ω) ω)
    (h_step : ∀ n ω,
      partialStep n (total n ω) ω = some (totalStep n (total n ω) ω)) :
    ∀ n ω, partialProcess n ω = some (total n ω) := by
  intro n
  induction n with
  | zero =>
      intro ω
      rw [h_partial_zero ω, h_total_zero ω]
  | succ n ih =>
      intro ω
      rw [h_partial_succ n ω, ih ω, h_total_succ n ω]
      exact h_step n ω

end SOptLib

/- Compatibility syntax for algorithm proofs staged before the snake_case API
rename. This does not introduce a second declaration. -/
macro "SOptLib.recursiveProcessFromRandomInitial" : term =>
  `(SOptLib.recursive_process_from_random_initial)

-- Phase 4 merged from focused staging declarations.

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: accelerated stochastic-gradient two-coordinate state process;
--   orig was the paper-local `State`/`stateAfter`/`x`/`xBar`/`xUnder` block,
--   exposed here as `AcceleratedGradientState` and `acceleratedGradientState`.
-- generality used: arbitrary additive real module state space, arbitrary sample
--   type, scalar schedules `alpha`, `beta`, and `lam`, sampled oracle kernel,
--   initial point, and a sample-coordinate reader from streams; no objective,
--   measure, filtration, convexity, smoothness, probability, independence,
--   integrability, or finite-dimensional assumption is needed by the process
--   construction itself.
-- portable call pattern: accelerated stochastic-gradient, accelerated
--   stochastic approximation, and two-sequence stochastic methods can supply
--   their schedules, oracle kernel, sample stream, and initial point while
--   reusing the same state recursion and `x`, `xBar`, `xUnder` projections.
-- counterargument checked: this is not merely paper traceability because the
--   generated process and projections are the stable modeling boundary used
--   before adaptedness, martingale-noise, update-identity, and telescope
--   arguments; it is not the feasible-subtype accelerated-state API already in
--   SOptLib because this statement is unconstrained and stores the two raw
--   oracle-step coordinates without carrier membership proofs.
-- coverage search: searched `accelerated stochastic gradient state process
--   coordinate projections`, `two sequence accelerated gradient state search
--   point sampled oracle step`, `raw accelerated gradient process state x xBar
--   xUnder coordinate projections`, and `recursive iterate process sample
--   update initial state projections`; relevant hits were
--   `recursiveIterateProcess`, `acceleratedSearchPoint`,
--   `FeasibleAcceleratedState`, `accelerated_step_from_state`, and
--   `accelerated_step_from_sample`, which cover generic recursion and feasible
--   constrained variants but not this raw unconstrained two-coordinate sampled
--   gradient process with public projections.
-- minimal hypotheses: all already minimal at the construction level except
--   using `[AddCommGroup E] [Module ℝ E]` as the Mathlib-grade module interface
--   for subtraction and real scalar multiplication in the two update formulas.

/-- Raw two-coordinate state for an accelerated stochastic-gradient recursion.

The state stores the current update iterate `x` and the averaged/output iterate
`xBar`, without imposing a feasible-carrier invariant.

Layer: Model | Concept: accelerated stochastic-gradient state
Proof: (definitional construction; bundled raw update and averaged-output
  coordinates for a two-sequence accelerated process)
Source: accelerated stochastic approximation state recurrences and Mathlib
  structure-field APIs
Used in: randomized stochastic accelerated-gradient generated process before
  search-point projection, sampled oracle updates, and telescope identities
Book citation: book/book/FOML/NonconvexStochasticAcceleratedGD.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
structure AcceleratedGradientState (E : Type*) where
  x : E
  xBar : E

/-- Initial raw accelerated state with both coordinates equal to the initial point.

Layer: Model | Concept: accelerated stochastic-gradient initial state
Proof: (definitional construction; duplicate the initial point into the update
  and averaged-output coordinates)
Source: accelerated stochastic approximation initialization notation and
  Mathlib structure constructor APIs
Used in: randomized stochastic accelerated-gradient base state before the first
  sampled oracle update
Book citation: book/book/FOML/NonconvexStochasticAcceleratedGD.json#/algorithm_spec/initialization
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
def acceleratedGradientInitialState {E : Type*} (x0 : E) : AcceleratedGradientState E :=
  { x := x0, xBar := x0 }

@[simp]
theorem acceleratedGradientInitialState_x {E : Type*} (x0 : E) :
    (acceleratedGradientInitialState x0).x = x0 := by
  rfl

@[simp]
theorem acceleratedGradientInitialState_xBar {E : Type*} (x0 : E) :
    (acceleratedGradientInitialState x0).xBar = x0 := by
  rfl

/-- One sampled accelerated stochastic-gradient step from a raw two-coordinate state.

The step forms the accelerated search point from the previous `xBar` and `x`,
evaluates the oracle at the provided sample, and updates both stored coordinates
with the `lam` and `beta` schedules.

Layer: Model | Concept: accelerated stochastic-gradient sampled state step
Proof: (definitional construction; accelerated search-point evaluation followed
  by the two sampled oracle update formulas)
Source: accelerated stochastic approximation state recurrences, sampled oracle
  notation, and Mathlib module subtraction/scalar multiplication APIs
Used in: randomized stochastic accelerated-gradient pathwise state transition
  at a positive paper time before deriving coordinate update identities
Book citation: book/book/FOML/NonconvexStochasticAcceleratedGD.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
def acceleratedGradientStepState
    {E Sample : Type*} [AddCommGroup E] [Module ℝ E]
    (alpha beta lam : ℕ → ℝ) (oracle : E → Sample → E)
    (k : {n : ℕ // 1 ≤ n}) (st : AcceleratedGradientState E) (sample : Sample) :
    AcceleratedGradientState E :=
  let xUnder := acceleratedSearchPoint alpha k st.xBar st.x
  let gk := oracle xUnder sample
  { x := st.x - lam k.1 • gk
    xBar := xUnder - beta k.1 • gk }

@[simp]
theorem acceleratedGradientStepState_def
    {E Sample : Type*} [AddCommGroup E] [Module ℝ E]
    (alpha beta lam : ℕ → ℝ) (oracle : E → Sample → E)
    (k : {n : ℕ // 1 ≤ n}) (st : AcceleratedGradientState E) (sample : Sample) :
    acceleratedGradientStepState alpha beta lam oracle k st sample =
      let xUnder := acceleratedSearchPoint alpha k st.xBar st.x
      let gk := oracle xUnder sample
      { x := st.x - lam k.1 • gk
        xBar := xUnder - beta k.1 • gk } := by
  rfl

@[simp]
theorem acceleratedGradientStepState_x
    {E Sample : Type*} [AddCommGroup E] [Module ℝ E]
    (alpha beta lam : ℕ → ℝ) (oracle : E → Sample → E)
    (k : {n : ℕ // 1 ≤ n}) (st : AcceleratedGradientState E) (sample : Sample) :
    (acceleratedGradientStepState alpha beta lam oracle k st sample).x =
      st.x - lam k.1 •
        oracle (acceleratedSearchPoint alpha k st.xBar st.x) sample := by
  rfl

@[simp]
theorem acceleratedGradientStepState_xBar
    {E Sample : Type*} [AddCommGroup E] [Module ℝ E]
    (alpha beta lam : ℕ → ℝ) (oracle : E → Sample → E)
    (k : {n : ℕ // 1 ≤ n}) (st : AcceleratedGradientState E) (sample : Sample) :
    (acceleratedGradientStepState alpha beta lam oracle k st sample).xBar =
      acceleratedSearchPoint alpha k st.xBar st.x -
        beta k.1 • oracle (acceleratedSearchPoint alpha k st.xBar st.x) sample := by
  rfl

/-- One sampled accelerated stochastic-gradient step reading its sample from a stream.

Layer: Model | Concept: accelerated stochastic-gradient stream state step
Proof: (definitional construction; read the positive-time sample coordinate
  and apply `acceleratedGradientStepState`)
Source: accelerated stochastic approximation sampled-process notation and
  Mathlib function application APIs
Used in: randomized stochastic accelerated-gradient sample-stream recursion
  before exposing generated `x`, `xBar`, and `xUnder` processes
Book citation: book/book/FOML/NonconvexStochasticAcceleratedGD.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
def acceleratedGradientStepStateAt
    {E Sample : Type*} [AddCommGroup E] [Module ℝ E]
    (alpha beta lam : ℕ → ℝ) (oracle : E → Sample → E)
    (sampleAt : {n : ℕ // 1 ≤ n} → (ℕ → Sample) → Sample)
    (k : {n : ℕ // 1 ≤ n}) (st : AcceleratedGradientState E) (ξ : ℕ → Sample) :
    AcceleratedGradientState E :=
  acceleratedGradientStepState alpha beta lam oracle k st (sampleAt k ξ)

@[simp]
theorem acceleratedGradientStepStateAt_def
    {E Sample : Type*} [AddCommGroup E] [Module ℝ E]
    (alpha beta lam : ℕ → ℝ) (oracle : E → Sample → E)
    (sampleAt : {n : ℕ // 1 ≤ n} → (ℕ → Sample) → Sample)
    (k : {n : ℕ // 1 ≤ n}) (st : AcceleratedGradientState E) (ξ : ℕ → Sample) :
    acceleratedGradientStepStateAt alpha beta lam oracle sampleAt k st ξ =
      acceleratedGradientStepState alpha beta lam oracle k st (sampleAt k ξ) := by
  rfl

/-- Sample-stream accelerated stochastic-gradient state process.

Starting from `x0`, the zero-based process performs at successor time `t + 1`
the positive-time sampled accelerated step indexed by `t + 1`.

Layer: Model | Concept: accelerated stochastic-gradient state process
Proof: (definitional construction; primitive recursion over natural time with
  positive-time sample-coordinate updates)
Source: accelerated stochastic approximation recursive process notation and
  Mathlib natural-number primitive recursion APIs
Used in: randomized stochastic accelerated-gradient generated process that
  supplies the raw iterate, averaged iterate, and search point for later
  martingale and telescope estimates
Book citation: book/book/FOML/NonconvexStochasticAcceleratedGD.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
def acceleratedGradientState
    {E Sample : Type*} [AddCommGroup E] [Module ℝ E]
    (alpha beta lam : ℕ → ℝ) (oracle : E → Sample → E) (x0 : E)
    (sampleAt : {n : ℕ // 1 ≤ n} → (ℕ → Sample) → Sample :=
      fun k ξ => ξ k.1) :
    ℕ → (ℕ → Sample) → AcceleratedGradientState E
  | 0 => fun _ => acceleratedGradientInitialState x0
  | t + 1 => fun ξ =>
      acceleratedGradientStepStateAt alpha beta lam oracle sampleAt
        ⟨t + 1, Nat.succ_le_succ (Nat.zero_le t)⟩
        (acceleratedGradientState alpha beta lam oracle x0 sampleAt t ξ)
        ξ

@[simp]
theorem acceleratedGradientState_zero
    {E Sample : Type*} [AddCommGroup E] [Module ℝ E]
    (alpha beta lam : ℕ → ℝ) (oracle : E → Sample → E) (x0 : E)
    (sampleAt : {n : ℕ // 1 ≤ n} → (ℕ → Sample) → Sample :=
      fun k ξ => ξ k.1)
    (ξ : ℕ → Sample) :
    acceleratedGradientState alpha beta lam oracle x0 sampleAt 0 ξ =
      acceleratedGradientInitialState x0 := by
  rfl

@[simp]
theorem acceleratedGradientState_succ
    {E Sample : Type*} [AddCommGroup E] [Module ℝ E]
    (alpha beta lam : ℕ → ℝ) (oracle : E → Sample → E) (x0 : E)
    (sampleAt : {n : ℕ // 1 ≤ n} → (ℕ → Sample) → Sample :=
      fun k ξ => ξ k.1)
    (t : ℕ) (ξ : ℕ → Sample) :
    acceleratedGradientState alpha beta lam oracle x0 sampleAt (t + 1) ξ =
      acceleratedGradientStepStateAt alpha beta lam oracle sampleAt
        ⟨t + 1, Nat.succ_le_succ (Nat.zero_le t)⟩
        (acceleratedGradientState alpha beta lam oracle x0 sampleAt t ξ)
        ξ := by
  rfl

/-- Raw iterate projection of a sample-stream accelerated stochastic-gradient process.

Layer: Model | Concept: accelerated stochastic-gradient raw iterate projection
Proof: (definitional construction; project the `x` field from
  `acceleratedGradientState`)
Source: accelerated stochastic approximation iterate notation and Mathlib
  structure-field projection APIs
Used in: randomized stochastic accelerated-gradient coordinate update identity
  and smoothness descent estimates for the generated raw iterate
Book citation: book/book/FOML/NonconvexStochasticAcceleratedGD.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
def acceleratedGradientX
    {E Sample : Type*} [AddCommGroup E] [Module ℝ E]
    (alpha beta lam : ℕ → ℝ) (oracle : E → Sample → E) (x0 : E)
    (sampleAt : {n : ℕ // 1 ≤ n} → (ℕ → Sample) → Sample :=
      fun k ξ => ξ k.1)
    (ξ : ℕ → Sample) (t : ℕ) : E :=
  (acceleratedGradientState alpha beta lam oracle x0 sampleAt t ξ).x

@[simp]
theorem acceleratedGradientX_def
    {E Sample : Type*} [AddCommGroup E] [Module ℝ E]
    (alpha beta lam : ℕ → ℝ) (oracle : E → Sample → E) (x0 : E)
    (sampleAt : {n : ℕ // 1 ≤ n} → (ℕ → Sample) → Sample :=
      fun k ξ => ξ k.1)
    (ξ : ℕ → Sample) (t : ℕ) :
    acceleratedGradientX alpha beta lam oracle x0 sampleAt ξ t =
      (acceleratedGradientState alpha beta lam oracle x0 sampleAt t ξ).x := by
  rfl

/-- Averaged iterate projection of a sample-stream accelerated stochastic-gradient process.

Layer: Model | Concept: accelerated stochastic-gradient averaged iterate projection
Proof: (definitional construction; project the `xBar` field from
  `acceleratedGradientState`)
Source: accelerated stochastic approximation averaged-iterate notation and
  Mathlib structure-field projection APIs
Used in: randomized stochastic accelerated-gradient coordinate update identity,
  output randomization, and function-gap estimates for the generated averaged
  iterate
Book citation: book/book/FOML/NonconvexStochasticAcceleratedGD.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
def acceleratedGradientXBar
    {E Sample : Type*} [AddCommGroup E] [Module ℝ E]
    (alpha beta lam : ℕ → ℝ) (oracle : E → Sample → E) (x0 : E)
    (sampleAt : {n : ℕ // 1 ≤ n} → (ℕ → Sample) → Sample :=
      fun k ξ => ξ k.1)
    (ξ : ℕ → Sample) (t : ℕ) : E :=
  (acceleratedGradientState alpha beta lam oracle x0 sampleAt t ξ).xBar

@[simp]
theorem acceleratedGradientXBar_def
    {E Sample : Type*} [AddCommGroup E] [Module ℝ E]
    (alpha beta lam : ℕ → ℝ) (oracle : E → Sample → E) (x0 : E)
    (sampleAt : {n : ℕ // 1 ≤ n} → (ℕ → Sample) → Sample :=
      fun k ξ => ξ k.1)
    (ξ : ℕ → Sample) (t : ℕ) :
    acceleratedGradientXBar alpha beta lam oracle x0 sampleAt ξ t =
      (acceleratedGradientState alpha beta lam oracle x0 sampleAt t ξ).xBar := by
  rfl

/-- Accelerated search-point projection of a sample-stream accelerated process.

At positive time `k`, the query is the affine search point formed from the
previous averaged iterate and previous raw iterate.

Layer: Model | Concept: accelerated stochastic-gradient search-point projection
Proof: (definitional construction; apply `acceleratedSearchPoint` to the
  previous `xBar` and `x` projections)
Source: accelerated stochastic approximation search-point notation and Mathlib
  natural-number predecessor APIs
Used in: randomized stochastic accelerated-gradient sampled oracle query before
  generated oracle-noise and descent estimates
Book citation: book/book/FOML/NonconvexStochasticAcceleratedGD.json#/algorithm_spec/steps/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
def acceleratedGradientXUnder
    {E Sample : Type*} [AddCommGroup E] [Module ℝ E]
    (alpha beta lam : ℕ → ℝ) (oracle : E → Sample → E) (x0 : E)
    (sampleAt : {n : ℕ // 1 ≤ n} → (ℕ → Sample) → Sample :=
      fun k ξ => ξ k.1)
    (ξ : ℕ → Sample) (k : {n : ℕ // 1 ≤ n}) : E :=
  acceleratedSearchPoint alpha k
    (acceleratedGradientXBar alpha beta lam oracle x0 sampleAt ξ (k.1 - 1))
    (acceleratedGradientX alpha beta lam oracle x0 sampleAt ξ (k.1 - 1))

@[simp]
theorem acceleratedGradientXUnder_def
    {E Sample : Type*} [AddCommGroup E] [Module ℝ E]
    (alpha beta lam : ℕ → ℝ) (oracle : E → Sample → E) (x0 : E)
    (sampleAt : {n : ℕ // 1 ≤ n} → (ℕ → Sample) → Sample :=
      fun k ξ => ξ k.1)
    (ξ : ℕ → Sample) (k : {n : ℕ // 1 ≤ n}) :
    acceleratedGradientXUnder alpha beta lam oracle x0 sampleAt ξ k =
      acceleratedSearchPoint alpha k
        (acceleratedGradientXBar alpha beta lam oracle x0 sampleAt ξ (k.1 - 1))
        (acceleratedGradientX alpha beta lam oracle x0 sampleAt ξ (k.1 - 1)) := by
  rfl

end SOptLib

-- Phase 4 batch 1 merge from Staging/minBlockDescentFactor.lean
namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite block descent factor minimum
-- generality used: arbitrary nonempty finite block index type, real sampling weights,
--   real block smoothness constants, and a scalar stepsize; no measure,
--   convexity, oracle, normed-space, or finite-dimensional assumptions are used.
-- portable call pattern: randomized block methods use the same factor when normalizing
--   output probabilities and when lower-bounding sampled block descent by a full block
--   norm; only the block index type, probabilities, smoothness constants, and stepsize vary.
-- counterargument checked: the body is one finite minimum, but the named quantity is reused
--   across output-law and descent-factor bounds; it is not merely paper traceability because
--   future block-coordinate proofs can instantiate the same formula without setup fields.
-- coverage search: queried "minimum finite block descent factor probability smoothness
--   stepsize" and "Finset univ image nonempty min block factor"; hits covered generic
--   finite-image extrema (`finset_univ_image_nonempty`, `finiteRunMinValue_le`) but no
--   probability-smoothness block descent factor definition, so this specializes a real
--   stochastic-optimization model concept rather than duplicating an existing name.
-- minimal hypotheses: all already minimal for this formula; `[Fintype I] [Nonempty I]`
--   are exactly needed to take a nonempty finite minimum.

/-- The finite minimum of probability-weighted block descent factors.

For a finite block family, this is `min_i p_i * (1 - (L_i / 2) * gamma)`,
the descent factor that appears in randomized block output weights.

Layer: Model | Concept: finite block descent factor
Proof: (definitional construction; nonempty finite real-image minimum of the probability-weighted descent factor)
Source: Mathlib finite-set image minima and SOptLib finite-image nonemptiness
Used in: stochastic randomized block methods, output normalization, and block-factor lower bounds -/
noncomputable def min_block_descent_factor
    {I : Type*} [Fintype I] [Nonempty I]
    (p L : I → ℝ) (gamma : ℝ) : ℝ :=
  (Finset.univ.image (fun i => p i * (1 - (L i / 2) * gamma))).min'
    (finset_univ_image_nonempty
      (fun i => p i * (1 - (L i / 2) * gamma)))

/-- The finite block descent factor unfolds to the corresponding finite image minimum.

Layer: Model | Gap: Level 0 (finite block descent factor unfolding)
Proof: by rfl after unfolding `min_block_descent_factor`.
Source: Mathlib finite-set image minima and SOptLib finite-image nonemptiness
Used in: stochastic randomized block methods, output normalization, and block-factor lower bounds -/
@[simp]
theorem min_block_descent_factor_def
    {I : Type*} [Fintype I] [Nonempty I]
    (p L : I → ℝ) (gamma : ℝ) :
    min_block_descent_factor p L gamma =
      (Finset.univ.image (fun i => p i * (1 - (L i / 2) * gamma))).min'
        (finset_univ_image_nonempty
          (fun i => p i * (1 - (L i / 2) * gamma))) := by
  rfl

/-- The minimum block descent factor is bounded above by every block factor. -/
theorem min_block_descent_factor_le
    {I : Type*} [Fintype I] [Nonempty I]
    (p L : I → ℝ) (gamma : ℝ) (i : I) :
    min_block_descent_factor p L gamma ≤ p i * (1 - (L i / 2) * gamma) := by
  classical
  rw [min_block_descent_factor_def]
  exact Finset.min'_le _ _ (by simp)

/-- The minimum block descent factor is nonnegative under nonnegative sampling
weights and a stepsize no larger than each block smoothness reciprocal scale. -/
theorem min_block_descent_factor_nonneg
    {I : Type*} [Fintype I] [Nonempty I]
    (p L : I → ℝ) (gamma : ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hL_pos : ∀ i, 0 < L i)
    (hgamma_le : ∀ i, gamma ≤ 2 / L i) :
    0 ≤ min_block_descent_factor p L gamma := by
  classical
  rw [min_block_descent_factor_def]
  refine Finset.le_min' (x := (0 : ℝ))
    (s := Finset.univ.image (fun i : I => p i * (1 - (L i / 2) * gamma)))
    (H := finset_univ_image_nonempty
      (fun i : I => p i * (1 - (L i / 2) * gamma))) ?_
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨i, _hi, rfl⟩
  have hhalf_nonneg : 0 ≤ L i / 2 :=
    div_nonneg (le_of_lt (hL_pos i)) (by norm_num)
  have hscaled_le : (L i / 2) * gamma ≤ (L i / 2) * (2 / L i) :=
    mul_le_mul_of_nonneg_left (hgamma_le i) hhalf_nonneg
  have hscale : (L i / 2) * (2 / L i) = 1 := by
    field_simp [(hL_pos i).ne']
  have hfactor_nonneg : 0 ≤ 1 - (L i / 2) * gamma := by
    linarith
  exact mul_nonneg (hp_nonneg i) hfactor_nonneg

/-- The minimum block descent factor lower-bounds the corresponding weighted
sum for arbitrary nonnegative real weights. -/
theorem min_block_descent_factor_mul_sum_le_weighted_sum
    {I : Type*} [Fintype I] [Nonempty I]
    (p L : I → ℝ) (gamma : ℝ) (w : I → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i) :
    min_block_descent_factor p L gamma * (∑ i, w i) ≤
      ∑ i, p i * (1 - (L i / 2) * gamma) * w i := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro i _hi
  exact mul_le_mul_of_nonneg_right
    (min_block_descent_factor_le p L gamma i) (hw_nonneg i)

end SOptLib

-- Phase 4 batch 1 merge from Staging/minBlockDescentFactor_nonneg_of_lt_two_div.lean
namespace SOptLib

-- Generalization plan (G0):
-- concept/name: strict-bound nonnegativity for the finite block descent factor;
--   orig was outputBlockFactor_nonneg.
-- generality used: arbitrary finite nonempty block index type, real sampling
--   weights, real block smoothness constants, and one real stepsize; no measure,
--   convexity, oracle, normed-space, or finite-dimensional assumptions are used.
-- portable call pattern: randomized block-coordinate and block mirror-descent
--   proofs use a positive stepsize with the blockwise restriction gamma < 2/L_i
--   to certify nonnegative minimum block factors before constructing an output
--   law; the probabilities, smoothness constants, and stepsize vary.
-- counterargument checked: an existing theorem handles the weaker API once
--   positivity of every L_i and gamma <= 2/L_i are supplied, but future callers
--   should not rederive those facts from the strict source stepsize restriction.
-- coverage search: queried "minimum block descent factor nonnegative step size
--   less than two divided Lipschitz", "min block descent factor nonneg", and
--   "positive gamma less than two divided L implies L positive"; hits included
--   SOptLib.min_block_descent_factor_nonneg as a partial theorem requiring
--   explicit L-positivity, with no complete strict-bound wrapper.
-- minimal hypotheses: the pointwise hypotheses `0 <= p i`, `0 < gamma`, and
--   `gamma < 2 / L i` are exactly what the proof consumes.

/-- The finite minimum block descent factor is nonnegative under strict
stepsize bounds `gamma < 2 / L_i`.

Layer: Model | Gap: Level 1 (strict block stepsize descent-factor nonnegativity)
Proof: derive `0 < L_i` from `0 < gamma < 2 / L_i`, weaken the strict stepsize
  bound to `gamma <= 2 / L_i`, and apply the finite minimum block factor API.
Source: Mathlib ordered real division and SOptLib finite minimum block descent factors
Used in: randomized block mirror descent output-law admissibility, where positive
  source stepsizes satisfy a strict blockwise reciprocal smoothness bound
Book citation: book/FOML/NonconvexStochasticBlockMirrorDescent.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic block mirror descent -/
theorem min_block_descent_factor_nonneg_of_pos_of_lt_two_div
    {I : Type*} [Fintype I] [Nonempty I]
    (p L : I → ℝ) (gamma : ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hgamma_pos : 0 < gamma)
    (hgamma_lt : ∀ i, gamma < 2 / L i) :
    0 ≤ min_block_descent_factor p L gamma := by
  classical
  refine min_block_descent_factor_nonneg p L gamma hp_nonneg ?_ ?_
  · intro i
    have hdivpos : 0 < 2 / L i := lt_trans hgamma_pos (hgamma_lt i)
    have htwo : ¬ ((2 : ℝ) < 0) := by norm_num
    rw [div_pos_iff] at hdivpos
    rcases hdivpos with hsame | hsame
    · exact hsame.2
    · exact (htwo hsame.1).elim
  · intro i
    exact le_of_lt (hgamma_lt i)

end SOptLib

-- Phase 4 batch 1 merge from Staging/minBlockDescentOutputWeight.lean
namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite block descent output weight; orig was outputWeight.
-- generality used: arbitrary finite nonempty block index type, arbitrary output
--   index type, real sampling weights, real block smoothness constants, and a
--   real stepsize schedule; no measure, convexity, oracle, normed-space, or
--   finite-dimensional assumptions are used.
-- portable call pattern: randomized block algorithms normalize output laws and
--   aggregate descent estimates with the same weight gamma_k times the minimum
--   block descent factor; the block probabilities, smoothness constants,
--   stepsize schedule, and output index type vary while the formula stays fixed.
-- counterargument checked: the body is a product, but it names the canonical
--   stopping weight that travels with denominator, nonnegativity, and weighted
--   descent APIs; it is not merely paper traceability because future randomized
--   block-coordinate proofs can instantiate it without setup fields.
-- coverage search: queried "minimum block descent factor output weight gamma
--   product equality", "min block descent factor gamma output weight", the
--   catalog for output-weight/min-block terms, and Mathlib LeanSearch for
--   "define output weight as step size times minimum finite block descent
--   factor"; hits covered min_block_descent_factor, generic finite output
--   denominators, and unrelated Mathlib weight APIs, but no definition or API
--   for this block-descent output weight.
-- minimal hypotheses: all already minimal for this formula and its API; the
--   finite nonempty block assumptions come from the minimum factor, and the
--   output index type is unconstrained.

/-- The randomized-output weight formed from a stepsize and the minimum block descent factor.

For a finite block family, this is
`gamma k * min_i p_i * (1 - (L_i / 2) * gamma k)`, the numerator weight used
in randomized block-method output laws.

Layer: Model | Concept: finite block descent output weight
Proof: (definitional construction; pointwise product of a stepsize and the finite minimum block descent factor)
Source: Mathlib real multiplication and SOptLib finite-image minimum block descent factors
Used in: randomized block mirror descent output normalization and descent aggregation
Book citation: book/FOML/NonconvexStochasticBlockMirrorDescent.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic block mirror descent -/
noncomputable def min_block_descent_output_weight
    {I T : Type*} [Fintype I] [Nonempty I]
    (p L : I → ℝ) (gamma : T → ℝ) (k : T) : ℝ :=
  gamma k * min_block_descent_factor p L (gamma k)

/-- The finite block descent output weight unfolds to stepsize times minimum block factor.

Layer: Model | Gap: Level 0 (finite block descent output-weight unfolding)
Proof: by rfl after unfolding `min_block_descent_output_weight`.
Source: Mathlib real multiplication and SOptLib finite-image minimum block descent factors
Used in: randomized block mirror descent output normalization and descent aggregation
Book citation: book/FOML/NonconvexStochasticBlockMirrorDescent.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic block mirror descent -/
@[simp]
theorem min_block_descent_output_weight_def
    {I T : Type*} [Fintype I] [Nonempty I]
    (p L : I → ℝ) (gamma : T → ℝ) (k : T) :
    min_block_descent_output_weight p L gamma k =
      gamma k * min_block_descent_factor p L (gamma k) := by
  rfl

/-- The finite block descent output weight is nonnegative under the standard
block-probability and stepsize upper-bound conditions.

Layer: Model | Gap: Level 1 (finite block descent output-weight nonnegativity)
Proof: combine nonnegativity of the stepsize with nonnegativity of the minimum
  block descent factor under nonnegative probabilities and the blockwise
  stepsize upper bound.
Source: Mathlib ordered real multiplication and SOptLib minimum block descent factor nonnegativity
Used in: randomized block mirror descent output-law admissibility on positive output windows
Book citation: book/FOML/NonconvexStochasticBlockMirrorDescent.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic block mirror descent -/
theorem min_block_descent_output_weight_nonneg
    {I T : Type*} [Fintype I] [Nonempty I]
    (p L : I → ℝ) (gamma : T → ℝ) (k : T)
    (hgamma_nonneg : 0 ≤ gamma k)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hL_pos : ∀ i, 0 < L i)
    (hgamma_le : ∀ i, gamma k ≤ 2 / L i) :
    0 ≤ min_block_descent_output_weight p L gamma k := by
  exact mul_nonneg hgamma_nonneg
    (min_block_descent_factor_nonneg p L (gamma k) hp_nonneg hL_pos hgamma_le)

/-- The finite block descent output weight transports the minimum-factor
weighted-sum bound through multiplication by the current stepsize.

Layer: Model | Gap: Level 1 (finite block descent output-weight weighted-sum bound)
Proof: unfold the output weight and multiply the minimum block descent factor
  weighted-sum bound by the nonnegative stepsize.
Source: Mathlib ordered real multiplication and SOptLib minimum block descent factor weighted-sum bound
Used in: randomized block mirror descent conversion from full block norm to sampled-block expected descent
Book citation: book/FOML/NonconvexStochasticBlockMirrorDescent.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic block mirror descent -/
theorem min_block_descent_output_weight_mul_sum_le_gamma_weighted_sum
    {I T : Type*} [Fintype I] [Nonempty I]
    (p L : I → ℝ) (gamma : T → ℝ) (k : T) (w : I → ℝ)
    (hgamma_nonneg : 0 ≤ gamma k)
    (hw_nonneg : ∀ i, 0 ≤ w i) :
    min_block_descent_output_weight p L gamma k * (∑ i, w i) ≤
      gamma k * ∑ i, p i * (1 - (L i / 2) * gamma k) * w i := by
  rw [min_block_descent_output_weight_def]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (min_block_descent_factor_mul_sum_le_weighted_sum
      p L (gamma k) w hw_nonneg)
    hgamma_nonneg

end SOptLib

