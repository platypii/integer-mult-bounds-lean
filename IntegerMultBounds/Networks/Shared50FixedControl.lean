import IntegerMultBounds.Networks.Shared50OrderedControl
import IntegerMultBounds.Networks.Shared50FramedShape

/-! One fixed interleaved rational control list for every runtime radix width.
Frame realization changes neither physical roles, gate positions, nor which
ordered rational field program is attached to each edge. -/
namespace IntegerMultBounds.Networks.Shared50FixedControl
noncomputable section
open FramedControlShape Shared50OrderedControl
open Shared50GlobalBudget (World)
open Shared50ModularControl (prime)
open Shared50ModularExecution (Arrays)
attribute [local irreducible] Shared50Finite.program SharedPointReplay.circuit SharedPointExecution.code
  Shared50GlobalCircuit.program50 Shared50GlobalCircuit.enumeration
  Shared50AffineControl.rationalSchedules Shared50SignedFramed.program

private theorem moveAll_shape {A : Type*} (is : List World) (move : A ≃ A) :
    shape (Shared50FiniteInterchange.moveAll is move) =
      is.map (fun i => FramedControlSchedule.Step.edge (R := ZMod 2) i ()) := by
  simp only [Shared50FiniteInterchange.moveAll,shape,List.map_map,Function.comp_def]

/-- The entire literal instruction shape is independent of the modulus. -/
theorem program_shape (m m' : ℕ) :
    shape (Shared50FiniteInterchange.program m) = shape (Shared50FiniteInterchange.program m') := by
  simp only [Shared50FiniteInterchange.program,shape_append,Shared50FiniteInterchange.pre,
    Shared50FiniteInterchange.post,moveAll_shape,Shared50ModularExecution.program,
    Shared50FramedShape.signed _ (Shared50ModularExecution.frames m)
      (Shared50ModularExecution.frames m') (Shared50ModularExecution.sourceFrames m)
      (Shared50ModularExecution.sourceFrames m')]

/-- Select a single fixed finite list; no runtime dimension appears here. -/
def control : List Control := schedule 0

/-- Rational field code, physical role names, and scalar-gate interleaving are
literally the same list at every width, not merely extensionally equivalent. -/
theorem schedule_eq (b : ℕ) : schedule b = control :=
  attach_eq _ _ (program_shape (prime^b) (prime^0)) _

theorem instruction_matches (b : ℕ) :
    List.Forall₂ (FramedControlSchedule.Matches (Realizes b)) control
      (Shared50FiniteInterchange.program (prime^b)) := by
  rw [← schedule_eq b]
  exact Shared50OrderedControl.instruction_matches b

theorem programs_exact : FramedControlSchedule.programs control = Shared50AffineControl.rationalSchedules :=
  Shared50OrderedControl.programs_exact 0

theorem gates_exact : FramedControlSchedule.gates control = Shared50GlobalCircuit.program50 :=
  Shared50OrderedControl.gates_exact 0

theorem calls_exact : calls control = Shared50Parameters.s := Shared50OrderedControl.calls_exact 0

/-- One and the same control list implements full routed transpose at all widths.
This statement concerns semantics; physical recursive calls are still separate. -/
theorem run_identity (b : ℕ) (stored : World → Arrays (prime^b)) :
    FramedControlSchedule.run (edgeAction b) control stored =
      fun i a => stored (Shared50ShearEndpoints.route i) (a.2,a.1) := by
  rw [← schedule_eq b]
  exact Shared50OrderedControl.run_identity b stored

end
end IntegerMultBounds.Networks.Shared50FixedControl
