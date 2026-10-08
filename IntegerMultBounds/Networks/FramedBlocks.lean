import IntegerMultBounds.Networks.Shared50BlockFrames
import IntegerMultBounds.Networks.BoundedFramedCircuit

/-! Whole-bank alignments and common-frame scalar-block execution helpers. -/

namespace IntegerMultBounds.Networks.Shared50FramedInvocation

open Circuit FramedCircuit Shared50BlockFrames

section General
variable {ι L M : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module (ZMod 2) M]

noncomputable def align (frameOf : L → Frame (ZMod 2) M) (current desired : ι → L) :
    List (Instruction ι (ZMod 2) M) :=
  edges (fun i => frameOf (current i)) (fun i => frameOf (desired i)) Finset.univ.toList

theorem align_run (frameOf : L → Frame (ZMod 2) M) (current desired : ι → L) (state : ι → M) :
    FramedCircuit.run (align frameOf current desired) (encode (fun i => frameOf (current i)) state) =
      encode (fun i => frameOf (desired i)) state := by
  rw [align,edges_invariant]
  congr 1
  funext i
  simp [afterEdges_apply]

def scalar (p : Program ι (ZMod 2)) : List (Instruction ι (ZMod 2) M) := p.map Instruction.gate

omit [Fintype ι] in
theorem scalar_run (frameOf : L → Frame (ZMod 2) M) (current : ι → L)
    (p : Program ι (ZMod 2)) (hp : Uniform current p) (state : ι → M) :
    FramedCircuit.run (scalar p) (encode (fun i => frameOf (current i)) state) =
      encode (fun i => frameOf (current i)) (moduleRun p state) := by
  rw [scalar,FanoutFrames.run_gate_instructions,module_invariant frameOf current p hp]

theorem erase_align (frameOf : L → Frame (ZMod 2) M) (current desired : ι → L) :
    BoundedFramedCircuit.erase (align frameOf current desired) = [] := by
  unfold align
  generalize (Finset.univ : Finset ι).toList = wires
  generalize (fun i => frameOf (current i)) = frames
  generalize (fun i => frameOf (desired i)) = target
  induction wires generalizing frames with
  | nil => rfl
  | cons i wires ih =>
    simpa only [edges,BoundedFramedCircuit.erase,List.filterMap_cons] using ih (Function.update frames i (target i))

omit [Fintype ι] [DecidableEq ι] in
theorem erase_scalar (p : Program ι (ZMod 2)) :
    BoundedFramedCircuit.erase (scalar (M := M) p) = p := by
  simp [BoundedFramedCircuit.erase,scalar]
omit [Fintype ι] [DecidableEq ι] in
theorem erase_append (left right : List (Instruction ι (ZMod 2) M)) :
    BoundedFramedCircuit.erase (left++right) = BoundedFramedCircuit.erase left ++ BoundedFramedCircuit.erase right :=
  List.filterMap_append
end General

end IntegerMultBounds.Networks.Shared50FramedInvocation
