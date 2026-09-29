import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Tactic

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: AdaptiveMomentState exposes the algorithm-independent state
--   carried by Adam-family adaptive-moment methods; orig was AMSGrad `State`
-- generality used: arbitrary carrier `E` with only the operations needed by each
--   construction: `Zero E` for initialization, `Add E` and `SMul Real E` for
--   exponential moving averages, and explicit square/max operations for
--   coordinatewise second-moment and memory updates
-- portable call pattern: Adam, AMSGrad, AdaMax-style, and related adaptive-gradient
--   algorithms instantiate the iterate and gradient carrier, beta schedules,
--   coordinate square, and coordinatewise memory combiner while reusing the same
--   state fields and update-shape definitions
-- counterargument checked: this is not a pure record rename or paper-local trace:
--   the coupled `(x,m,v,vhat)` interface is the stable public state for a family
--   of adaptive-moment algorithms; the closest SOptLib state, `RecursiveMomentumState`,
--   stores a direction and scalar accumulator and cannot represent first/second/max
--   moment recurrences without changing the statement shape
-- coverage search: searched `adaptive moment state first second maximum memory update
--   zero initial moments`, `Adam optimizer state moment update beta coordinatewise
--   maximum`, and catalog tokens for `AdaptiveMoment`, `firstMoment`, `secondMoment`,
--   `vhat`, and `coordMax`; closest hits were `RecursiveMomentumState`,
--   `recursiveMomentumInitialState`, and local AMSGrad declarations, all partial
-- minimal hypotheses: all already minimal after replacing finite Euclidean spaces
--   and AMSGrad setup fields by the exact carrier operations each definition uses

/-- State of an adaptive-moment iteration, carrying an iterate, first moment,
second moment, and long-term maximum-memory moment.

Layer: Model | Concept: adaptive-moment optimizer state
Proof: (definitional construction; bundled iterate, first moment, second moment, and maximum-memory moment)
Source: Adam-family adaptive-gradient algorithm state notation and Mathlib structure APIs
Used in: adaptive-gradient and Adam-family state recurrences that update first and second moments before a coordinatewise memory step
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
@[ext]
structure AdaptiveMomentState (E : Type*) where
  x : E
  m : E
  v : E
  vhat : E

namespace AdaptiveMomentState

/-- The iterate projection of a state built from coordinates is the supplied iterate. -/
@[simp]
theorem mk_x {E : Type*} (x m v vhat : E) :
    (AdaptiveMomentState.mk x m v vhat).x = x := by
  rfl

/-- The first-moment projection of a state built from coordinates is the supplied
first moment. -/
@[simp]
theorem mk_m {E : Type*} (x m v vhat : E) :
    (AdaptiveMomentState.mk x m v vhat).m = m := by
  rfl

/-- The second-moment projection of a state built from coordinates is the supplied
second moment. -/
@[simp]
theorem mk_v {E : Type*} (x m v vhat : E) :
    (AdaptiveMomentState.mk x m v vhat).v = v := by
  rfl

/-- The memory projection of a state built from coordinates is the supplied
long-term memory moment. -/
@[simp]
theorem mk_vhat {E : Type*} (x m v vhat : E) :
    (AdaptiveMomentState.mk x m v vhat).vhat = vhat := by
  rfl

/-- Initial adaptive-moment state with the supplied iterate and zeroed first,
second, and long-term memory moments.

Layer: Model | Concept: adaptive-moment zero-moment initialization
Proof: (definitional construction; store the initial iterate and three zero moment fields)
Source: Adam-family adaptive-gradient initialization notation and Mathlib zero APIs
Used in: base states for adaptive-gradient recurrences before the first observed gradient
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec/initialization
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
def initial {E : Type*} [Zero E] (x0 : E) : AdaptiveMomentState E where
  x := x0
  m := 0
  v := 0
  vhat := 0

/-- The zero-moment initializer unfolds to the supplied iterate and three zero
moment coordinates.

Layer: Model | Gap: Level 0 (adaptive-moment initialization unfolding)
Proof: by rfl after unfolding `AdaptiveMomentState.initial`
Source: Mathlib structure constructor projection and zero APIs
Used in: base-case simplification of adaptive-gradient state sequences
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec/initialization
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
@[simp]
theorem initial_eq {E : Type*} [Zero E] (x0 : E) :
    initial x0 = ({ x := x0, m := 0, v := 0, vhat := 0 } : AdaptiveMomentState E) := by
  rfl

/-- First-moment exponential moving-average update
`beta1 t • state.m + (1 - beta1 t) • g`.

Layer: Model | Concept: adaptive-moment first-moment update
Proof: (definitional construction; convex-combination-shaped real scalar update of the stored first moment)
Source: Adam-family exponential moving averages and Mathlib scalar-action APIs
Used in: adaptive-gradient one-step recurrences that update the momentum estimate from a current gradient
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec/steps/1
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
def firstMoment {E : Type*} [Add E] [SMul Real E]
    (beta1 : Nat → Real) (t : Nat) (state : AdaptiveMomentState E) (g : E) : E :=
  beta1 t • state.m + (1 - beta1 t) • g

/-- The first-moment update unfolds to its exponential moving-average formula.

Layer: Model | Gap: Level 0 (adaptive-moment first-moment unfolding)
Proof: by rfl after unfolding `AdaptiveMomentState.firstMoment`
Source: Mathlib scalar-action and additive-expression APIs
Used in: algebraic simplification of adaptive-gradient momentum recurrences
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec/steps/1
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
@[simp]
theorem firstMoment_eq {E : Type*} [Add E] [SMul Real E]
    (beta1 : Nat → Real) (t : Nat) (state : AdaptiveMomentState E) (g : E) :
    firstMoment beta1 t state g = beta1 t • state.m + (1 - beta1 t) • g := by
  rfl

/-- Second-moment exponential moving-average update
`beta2 • state.v + (1 - beta2) • square g`.

Layer: Model | Concept: adaptive-moment second-moment update
Proof: (definitional construction; real scalar update of the stored second moment after an explicit square operation)
Source: Adam-family second-moment recurrences and Mathlib scalar-action APIs
Used in: adaptive-gradient one-step recurrences that accumulate coordinatewise squared gradients
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec/steps/2
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
def secondMoment {E : Type*} [Add E] [SMul Real E]
    (square : E → E) (beta2 : Real) (state : AdaptiveMomentState E) (g : E) : E :=
  beta2 • state.v + (1 - beta2) • square g

/-- The second-moment update unfolds to its squared-gradient moving-average
formula.

Layer: Model | Gap: Level 0 (adaptive-moment second-moment unfolding)
Proof: by rfl after unfolding `AdaptiveMomentState.secondMoment`
Source: Mathlib scalar-action and additive-expression APIs
Used in: algebraic simplification of adaptive-gradient second-moment recurrences
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec/steps/2
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
@[simp]
theorem secondMoment_eq {E : Type*} [Add E] [SMul Real E]
    (square : E → E) (beta2 : Real) (state : AdaptiveMomentState E) (g : E) :
    secondMoment square beta2 state g = beta2 • state.v + (1 - beta2) • square g := by
  rfl

/-- Long-term adaptive memory update obtained by combining the stored memory
moment with the new second moment.

Layer: Model | Concept: adaptive-moment long-term memory update
Proof: (definitional construction; apply the supplied coordinatewise memory combiner to `state.vhat` and the new second moment)
Source: AMSGrad and AdaMax-style adaptive-memory recurrences over coordinatewise maximum-like operations
Used in: adaptive-gradient one-step recurrences that replace the denominator memory by a coordinatewise maximum or related monotone combiner
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec/steps/3
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
def longTermMemory {E : Type*}
    (coordMax : E → E → E) (state : AdaptiveMomentState E) (v : E) : E :=
  coordMax state.vhat v

/-- The long-term memory update unfolds to the supplied memory combiner applied
to the stored memory and the new second moment.

Layer: Model | Gap: Level 0 (adaptive-moment long-term memory unfolding)
Proof: by rfl after unfolding `AdaptiveMomentState.longTermMemory`
Source: Mathlib function application and structure projection APIs
Used in: simplification of adaptive-gradient denominator-memory recurrences
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec/steps/3
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
@[simp]
theorem longTermMemory_eq {E : Type*}
    (coordMax : E → E → E) (state : AdaptiveMomentState E) (v : E) :
    longTermMemory coordMax state v = coordMax state.vhat v := by
  rfl

end AdaptiveMomentState

/-- The measurable space on an adaptive-moment state generated by its four
coordinates.

Layer: Model | Concept: adaptive-moment optimizer state
Proof: (definitional construction; supremum of the four coordinate-comap
  measurable spaces)
Source: Mathlib measure-theory measurable-space comap APIs
Used in: measurability of Adam-family state processes whose iterate and moment
  coordinates are measurable -/
@[reducible]
def adaptiveMomentStateMeasurableSpace
    {E : Type*} [MeasurableSpace E] : MeasurableSpace (AdaptiveMomentState E) :=
  MeasurableSpace.comap (fun s : AdaptiveMomentState E => s.x) inferInstance ⊔
    MeasurableSpace.comap (fun s : AdaptiveMomentState E => s.m) inferInstance ⊔
      MeasurableSpace.comap (fun s : AdaptiveMomentState E => s.v) inferInstance ⊔
        MeasurableSpace.comap (fun s : AdaptiveMomentState E => s.vhat) inferInstance

/-- The adaptive-moment state measurable space unfolds to the supremum of its
four coordinate-comap measurable spaces. -/
@[simp]
theorem adaptiveMomentStateMeasurableSpace_def
    {E : Type*} [MeasurableSpace E] :
    (adaptiveMomentStateMeasurableSpace : MeasurableSpace (AdaptiveMomentState E)) =
      MeasurableSpace.comap (fun s : AdaptiveMomentState E => s.x) inferInstance ⊔
        MeasurableSpace.comap (fun s : AdaptiveMomentState E => s.m) inferInstance ⊔
          MeasurableSpace.comap (fun s : AdaptiveMomentState E => s.v) inferInstance ⊔
            MeasurableSpace.comap (fun s : AdaptiveMomentState E => s.vhat) inferInstance := by
  rfl

/-- The iterate coordinate is measurable for the coordinate-generated state
measurable space. -/
theorem adaptiveMomentState_x_measurable
    {E : Type*} [MeasurableSpace E] :
    @Measurable (AdaptiveMomentState E) E
      adaptiveMomentStateMeasurableSpace inferInstance
      (fun s => s.x) := by
  exact Measurable.of_comap_le ((le_sup_left.trans le_sup_left).trans le_sup_left)

/-- The first-moment coordinate is measurable for the coordinate-generated state
measurable space. -/
theorem adaptiveMomentState_m_measurable
    {E : Type*} [MeasurableSpace E] :
    @Measurable (AdaptiveMomentState E) E
      adaptiveMomentStateMeasurableSpace inferInstance
      (fun s => s.m) := by
  exact Measurable.of_comap_le ((le_sup_right.trans le_sup_left).trans le_sup_left)

/-- The second-moment coordinate is measurable for the coordinate-generated state
measurable space. -/
theorem adaptiveMomentState_v_measurable
    {E : Type*} [MeasurableSpace E] :
    @Measurable (AdaptiveMomentState E) E
      adaptiveMomentStateMeasurableSpace inferInstance
      (fun s => s.v) := by
  exact Measurable.of_comap_le (le_sup_right.trans le_sup_left)

/-- The long-term memory coordinate is measurable for the coordinate-generated
state measurable space. -/
theorem adaptiveMomentState_vhat_measurable
    {E : Type*} [MeasurableSpace E] :
    @Measurable (AdaptiveMomentState E) E
      adaptiveMomentStateMeasurableSpace inferInstance
      (fun s => s.vhat) := by
  exact Measurable.of_comap_le le_sup_right

/-- Measurable coordinate processes assemble into a measurable adaptive-moment
state process for the coordinate-generated state measurable space. -/
theorem adaptiveMomentState_mk_measurable
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {x m v vhat : Ω → E}
    (hx : Measurable x) (hm : Measurable m) (hv : Measurable v)
    (hvhat : Measurable vhat) :
    @Measurable Ω (AdaptiveMomentState E) inferInstance
      adaptiveMomentStateMeasurableSpace
      (fun ω => AdaptiveMomentState.mk (x ω) (m ω) (v ω) (vhat ω)) := by
  apply Measurable.of_comap_le
  simp only [adaptiveMomentStateMeasurableSpace_def, MeasurableSpace.comap_sup,
    MeasurableSpace.comap_comp]
  exact sup_le (sup_le (sup_le hx.comap_le hm.comap_le) hv.comap_le) hvhat.comap_le

end SOptLib
