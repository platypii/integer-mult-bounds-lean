module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamCropPlan
public import IntegerMultBounds.NLogN.PhaseCellBoundaryCropSchedule

/-! Boundary geometry changes metadata in three fixed port pairs, not code. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.SeamCropPlan
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN.PhaseCellMatrix

variable {T Q A : ℕ} {P U : Type} {source : Fin T}

/-- The physical program has no line length or core width parameter. -/
def boundaryProgram (plan : SeamCropPlan T source) (skip count : Fin 3 → Fin T) : Pr P T Q A U :=
  plan.portProgram (List.ofFn (fun i => (skip i,count i))).reverse

theorem program_boundary_eq (plan : SeamCropPlan T source) (s width : ℕ)
    (skip count : Fin 3 → Fin T)
    (hskip : ∀ i, plan.skip (boundaryCropIndex s width i) = skip i)
    (hcount : ∀ i, plan.count (boundaryCropIndex s width i) = count i) :
    plan.program (Q := Q) (P := P) (A := A) (U := U) (boundaryCropSchedule s width) =
      plan.boundaryProgram skip count := by
  rw [plan.program_eq_portProgram,boundaryCropSchedule_eq_reverse_slots,List.map_reverse,List.map_ofFn]
  have he : (fun k => (plan.skip k,plan.count k)) ∘ boundaryCropIndex s width =
      (fun i => (skip i,count i)) := by
    funext i
    exact Prod.ext (hskip i) (hcount i)
  rw [he]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.SeamCropPlan
