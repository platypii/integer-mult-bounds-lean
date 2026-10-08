import IntegerMultBounds.Networks.DAGFramedShape
import IntegerMultBounds.Networks.Shared50SignedFramed

/-! Every actual Shared50 physical wire and scalar gate is independent of the
chosen realization of frames. No large circuit list is evaluated. -/
namespace IntegerMultBounds.Networks.Shared50FramedShape
noncomputable section
open FramedCircuit FramedControlShape
variable {M N : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  [AddCommGroup N] [Module (ZMod 2) N]
attribute [local irreducible] Shared50Finite.program SharedPointReplay.circuit SharedPointExecution.code
  Shared50FiniteFramed.forward Shared50FiniteFramed.inverse
  Shared50FramedInvocation.middle Shared50FramedOpposite.middle
  Shared50FramedInvocation.program Shared50FramedOpposite.program
  Shared50GlobalFramed.localProgram Shared50GlobalFramed.invocation Shared50GlobalFramed.partialStage
  Shared50GlobalFramed.stage Shared50GlobalFramed.boundary

@[simp] theorem align {ι L : Type*} [Fintype ι] [DecidableEq ι]
    (f : L → Frame (ZMod 2) M) (current desired : ι → L) :
    shape (Shared50FramedInvocation.align f current desired) =
      (Finset.univ.toList : List ι).map (fun i => FramedControlSchedule.Step.edge i ()) :=
  shape_edges _ _ _

@[simp] theorem scalar {ι : Type*} (p : Circuit.Program ι (ZMod 2)) :
    shape (Shared50FramedInvocation.scalar (M := M) p) = p.map FramedControlSchedule.Step.gate :=
  shape_gates _

section Local
open MotifLabels Shared50BlockFrames Shared50StageFrames Shared50LabeledInvocation NeighborCounts
variable {n s : ℕ} {E H : Type*} [AddCommGroup E] [Module ℚ E] [AddCommGroup H] [Module ℚ H]

theorem middle (g : Geometry ℚ E Factor) (q : H)
    (f : Space E H → Frame (ZMod 2) M) (f' : Space E H → Frame (ZMod 2) N) :
    shape (Shared50FramedInvocation.middle (n := n) (s := s) g q f) =
      shape (Shared50FramedInvocation.middle (n := n) (s := s) g q f') := by
  simp only [Shared50FramedInvocation.middle,shape_embed,DAGFramedShape.finite_forward _
    (fun U => f' (Shared50StageFrames.label g q U))]

theorem opposite_middle (g : Geometry ℚ E Factor) (q : H)
    (f : Space E H → Frame (ZMod 2) M) (f' : Space E H → Frame (ZMod 2) N) :
    shape (Shared50FramedOpposite.middle (n := n) (s := s) g q f) =
      shape (Shared50FramedOpposite.middle (n := n) (s := s) g q f') := by
  simp only [Shared50FramedOpposite.middle,shape_embed,DAGFramedShape.finite_inverse _
    (fun U => f' (Shared50StageFrames.label g q U))]

theorem local_forward (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (f : Space E H → Frame (ZMod 2) M) (f' : Space E H → Frame (ZMod 2) N)
    (initial : Wire n s → Space E H) :
    shape (Shared50FramedInvocation.program g q e f initial) =
      shape (Shared50FramedInvocation.program g q e f' initial) := by
  simp only [Shared50FramedInvocation.program,shape_append,align,scalar,middle g q f f']

theorem local_opposite (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (f : Space E H → Frame (ZMod 2) M) (f' : Space E H → Frame (ZMod 2) N)
    (initial : Wire n s → Space E H) :
    shape (Shared50FramedOpposite.program g q e f initial) =
      shape (Shared50FramedOpposite.program g q e f' initial) := by
  simp only [Shared50FramedOpposite.program,shape_append,align,scalar,opposite_middle g q f f']
end Local

open Shared50GlobalTrace (Label)
open Shared50GlobalBudget (Triple World)
variable {n : ℕ}

theorem localProgram (e : Fin n ≃ Triple) (f : Label → Frame (ZMod 2) M)
    (g : Label → Frame (ZMod 2) N) (j : Fin 3) (q : Triple × Triple) :
    shape (Shared50GlobalFramed.localProgram e f j q) =
      shape (Shared50GlobalFramed.localProgram e g j q) := by
  unfold Shared50GlobalFramed.localProgram
  split_ifs
  · exact local_forward _ _ e _ _ _
  · exact local_opposite _ _ e _ _ _
  · exact local_forward _ _ e _ _ _

theorem invocation (e : Fin n ≃ Triple) (f : Label → Frame (ZMod 2) M)
    (g : Label → Frame (ZMod 2) N) (j : Fin 3) (q : Triple × Triple) :
    shape (Shared50GlobalFramed.invocation e f j q) =
      shape (Shared50GlobalFramed.invocation e g j q) := by
  simp only [Shared50GlobalFramed.invocation,shape_embed,localProgram e f g]

theorem partialStage (e : Fin n ≃ Triple) (f : Label → Frame (ZMod 2) M)
    (g : Label → Frame (ZMod 2) N) (j : Fin 3) (qs : List (Triple × Triple)) :
    shape (Shared50GlobalFramed.partialStage e f j qs) =
      shape (Shared50GlobalFramed.partialStage e g j qs) := by
  unfold Shared50GlobalFramed.partialStage shape
  rw [List.map_flatMap,List.map_flatMap]
  apply congrArg (fun f => qs.flatMap f)
  funext q
  exact invocation e f g j q

theorem stage (e : Fin n ≃ Triple) (f : Label → Frame (ZMod 2) M)
    (g : Label → Frame (ZMod 2) N) (j : Fin 3) :
    shape (Shared50GlobalFramed.stage e f j) = shape (Shared50GlobalFramed.stage e g j) :=
  by
    unfold Shared50GlobalFramed.stage
    exact partialStage e f g j _

/-- Even initial frames may differ arbitrarily: exact wire/gate positions remain fixed. -/
theorem signed (e : Fin n ≃ Triple) (f : Label → Frame (ZMod 2) M)
    (g : Label → Frame (ZMod 2) N) (initial : World → Frame (ZMod 2) M)
    (initial' : World → Frame (ZMod 2) N) :
    shape (Shared50SignedFramed.program e f initial) =
      shape (Shared50SignedFramed.program e g initial') := by
  simp only [Shared50SignedFramed.program,Shared50SignedFramed.first,Shared50SignedFramed.tail,
    shape_append,shape_edges,stage e f g,Shared50GlobalFramed.boundary,align]

end
end IntegerMultBounds.Networks.Shared50FramedShape
