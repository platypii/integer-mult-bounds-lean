import IntegerMultBounds.Networks.FramedControlShape
import IntegerMultBounds.Networks.Shared50FiniteFramed

/-! Exact role-and-gate shape independence for physical DAG schedules, including
complemented reversal and finite-bank restriction. -/
namespace IntegerMultBounds.Networks.DAGFramedShape
open FramedCircuit FramedControlShape
variable {α L E F : Type*} {h : ℕ} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

 theorem forward_schedule (triples : α → Finset (Fin h))
    (f : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E)
    (g : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) F)
    (es : List (DAGSupportTrace.Event α)) (current : ℕ → Finset α) :
    shape (DAGFramedExecution.schedule triples f es current) =
      shape (DAGFramedExecution.schedule triples g es current) := by
  induction es generalizing current with
  | nil => rfl
  | cons e es ih =>
    simp only [DAGFramedExecution.schedule,shape_append,DAGFramedExecution.eventInstructions,
      shape_edges,shape_gates,ih]

theorem complement_align (f : L → Frame (ZMod 2) E) (g : L → Frame (ZMod 2) F)
    (xs : List (ℕ × L)) (current : ℕ → L) :
    shape (DAGComplementExecution.align f current xs) =
      shape (DAGComplementExecution.align g current xs) := by
  induction xs generalizing current with
  | nil => rfl
  | cons x xs ih =>
    simpa only [DAGComplementExecution.align,shape,List.map_cons] using
      congrArg (List.cons (FramedControlSchedule.Step.edge x.1 ())) (ih _)

theorem inverse_schedule (triples : α → Finset (Fin h))
    (f : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E)
    (g : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) F)
    (es : List (DAGSupportTrace.Event α)) (current : ℕ → Finset α) :
    shape (DAGComplementExecution.schedule triples f es current) =
      shape (DAGComplementExecution.schedule triples g es current) := by
  induction es generalizing current with
  | nil => rfl
  | cons e es ih =>
    simp only [DAGComplementExecution.schedule,shape_append,DAGComplementExecution.eventInverse,
      shape_gates,ih,complement_align f g]

theorem finite_forward (f : Submodule ℚ (Fin 50 → ℚ) → Frame (ZMod 2) E)
    (g : Submodule ℚ (Fin 50 → ℚ) → Frame (ZMod 2) F) :
    shape (Shared50FiniteFramed.forward f) = shape (Shared50FiniteFramed.forward g) :=
  shape_restrict_eq _ _ _ _ _ (forward_schedule _ f g _ _)

theorem finite_inverse (f : Submodule ℚ (Fin 50 → ℚ) → Frame (ZMod 2) E)
    (g : Submodule ℚ (Fin 50 → ℚ) → Frame (ZMod 2) F) :
    shape (Shared50FiniteFramed.inverse f) = shape (Shared50FiniteFramed.inverse g) :=
  shape_restrict_eq _ _ _ _ _ (inverse_schedule _ f g _ _)

end IntegerMultBounds.Networks.DAGFramedShape
