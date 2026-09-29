import Mathlib.Order.Filter.Extr

namespace SOptLib

/-- A parameterized feasible argmin relation.

The relation records that a selected ambient point is feasible and that, after
restricting the parameterized objective to the feasible subtype, the selected
point minimizes the objective over all feasible candidates. -/
def parameterizedFeasibleArgmin {E P R : Type*} [Preorder R]
    (objective : P -> E -> E -> R) (F : Set E) (param : P) (source x : E) : Prop :=
  ∃ hx : x ∈ F,
    IsMinOn (fun z : {z : E // z ∈ F} => objective param source z.1)
      Set.univ ⟨x, hx⟩

/-- Unfold a parameterized feasible argmin relation to feasibility plus the
subtype minimizer certificate. -/
@[simp]
theorem parameterizedFeasibleArgmin_def {E P R : Type*} [Preorder R]
    (objective : P -> E -> E -> R) (F : Set E) (param : P) (source x : E) :
    parameterizedFeasibleArgmin objective F param source x ↔
      ∃ hx : x ∈ F,
        IsMinOn (fun z : {z : E // z ∈ F} => objective param source z.1)
          Set.univ ⟨x, hx⟩ := by
  rfl

/-- A selected point in a parameterized feasible argmin relation is feasible. -/
theorem parameterizedFeasibleArgmin_mem {E P R : Type*} [Preorder R]
    {objective : P -> E -> E -> R} {F : Set E} {param : P} {source x : E}
    (h : parameterizedFeasibleArgmin objective F param source x) :
    x ∈ F := by
  rcases h with ⟨hx, _⟩
  exact hx

/-- The subtype-minimizer package is equivalent to ambient feasibility together
with `IsMinOn` for the ambient objective over the feasible set. -/
theorem parameterizedFeasibleArgmin_iff_isMinOn {E P R : Type*} [Preorder R]
    (objective : P -> E -> E -> R) (F : Set E) (param : P) (source x : E) :
    parameterizedFeasibleArgmin objective F param source x ↔
      x ∈ F ∧ IsMinOn (fun z : E => objective param source z) F x := by
  constructor
  · intro h
    rcases h with ⟨hx, hmin⟩
    refine ⟨hx, ?_⟩
    rw [isMinOn_iff]
    intro z hz
    have hle := (isMinOn_iff.mp hmin) ⟨z, hz⟩ (Set.mem_univ _)
    simpa using hle
  · intro h
    rcases h with ⟨hx, hmin⟩
    refine ⟨hx, ?_⟩
    rw [isMinOn_iff]
    intro z _hz
    exact (isMinOn_iff.mp hmin) z.1 z.2

/-- Pointwise comparison form of `parameterizedFeasibleArgmin`. -/
theorem parameterizedFeasibleArgmin_iff_forall_le {E P R : Type*} [Preorder R]
    (objective : P -> E -> E -> R) (F : Set E) (param : P) (source x : E) :
    parameterizedFeasibleArgmin objective F param source x ↔
      x ∈ F ∧ ∀ z ∈ F, objective param source x ≤ objective param source z := by
  rw [parameterizedFeasibleArgmin_iff_isMinOn, isMinOn_iff]

end SOptLib
