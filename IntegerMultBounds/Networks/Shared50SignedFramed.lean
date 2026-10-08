import IntegerMultBounds.Networks.Shared50GlobalShear

/-! The actual reused physical schedule with arbitrary initial frames over any
binary module. Only its first alignment changes; all local physical programs
and subsequent boundaries are the existing ones. This isolates the generic
physical semantics needed by finite-modulus frame implementations. -/

namespace IntegerMultBounds.Networks.Shared50SignedFramed

noncomputable section
open FramedCircuit Shared50GlobalTrace
open Shared50GlobalBudget (World Triple)

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

/-- Align each physical wire once from its chosen initial frame. -/
def first (frameOf : Label → Frame (ZMod 2) M) (initialFrames : World → Frame (ZMod 2) M) :
    List (Instruction World (ZMod 2) M) :=
  edges initialFrames (fun i => frameOf (input 0 i)) wires

/-- Preserve the exact existing sparse physical suffix and chronological order. -/
def tail (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M) :
    List (Instruction World (ZMod 2) M) :=
  Shared50GlobalFramed.stage e frameOf 0 ++ Shared50GlobalFramed.boundary frameOf 1 ++
    Shared50GlobalFramed.stage e frameOf 1 ++ Shared50GlobalFramed.boundary frameOf 2 ++
    Shared50GlobalFramed.stage e frameOf 2 ++ Shared50GlobalFramed.boundary frameOf 3

def tailUpdates (e : Fin n ≃ Triple) : List (World × Label) :=
  Shared50GlobalTraceStages.stageUpdates e 0 ++ boundaryUpdates 1 ++
    Shared50GlobalTraceStages.stageUpdates e 1 ++ boundaryUpdates 2 ++
    Shared50GlobalTraceStages.stageUpdates e 2 ++ boundaryUpdates 3

def program (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (initialFrames : World → Frame (ZMod 2) M) : List (Instruction World (ZMod 2) M) :=
  first frameOf initialFrames ++ tail e frameOf

/-- Initial frame changes add no pointwise scalar arithmetic. -/
theorem first_erasure (frameOf : Label → Frame (ZMod 2) M) (initialFrames : World → Frame (ZMod 2) M) :
    BoundedFramedCircuit.erase (first frameOf initialFrames) = [] :=
  Shared50FramedInvocation.erase_align (fun f : Frame (ZMod 2) M => f)
    initialFrames (fun i => frameOf (input 0 i))

theorem scalar_erasure (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (initialFrames : World → Frame (ZMod 2) M) :
    BoundedFramedCircuit.erase (program e frameOf initialFrames) = Shared50GlobalCircuit.program e := by
  simp only [program,tail,Shared50FramedInvocation.erase_append,first_erasure,
    Shared50GlobalFramed.stage_erasure,Shared50GlobalFramed.boundary_erasure,
    List.nil_append,List.append_nil,Shared50GlobalCircuit.program]

theorem first_invariant (frameOf : Label → Frame (ZMod 2) M) (initialFrames : World → Frame (ZMod 2) M)
    (state : World → M) :
    run (first frameOf initialFrames) (encode initialFrames state) =
      encode (fun i => frameOf (input 0 i)) state := by
  rw [first,edges_invariant]
  congr 1
  funext i
  simp only [afterEdges_apply,mem_wires,ite_true]

theorem tail_invariant (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M) (state : World → M) :
    run (tail e frameOf) (encode (fun i => frameOf (input 0 i)) state) =
      encode (fun i => frameOf (sink i)) (moduleRun (Shared50GlobalCircuit.program e) state) := by
  have h1 (v : World → M) : run (Shared50GlobalFramed.boundary frameOf 1)
      (encode (fun i => frameOf (output 0 i)) v) = encode (fun i => frameOf (input 1 i)) v :=
    Shared50GlobalFramed.boundary_run frameOf 1 v
  have h2 (v : World → M) : run (Shared50GlobalFramed.boundary frameOf 2)
      (encode (fun i => frameOf (output 1 i)) v) = encode (fun i => frameOf (input 2 i)) v :=
    Shared50GlobalFramed.boundary_run frameOf 2 v
  have h3 (v : World → M) : run (Shared50GlobalFramed.boundary frameOf 3)
      (encode (fun i => frameOf (output 2 i)) v) = encode (fun i => frameOf (sink i)) v :=
    Shared50GlobalFramed.boundary_run frameOf 3 v
  simp only [tail,run_append,Shared50GlobalFramed.stage_run,h1,h2,h3,
    Shared50GlobalCircuit.program,GroupedModuleFrames.moduleRun_append]

theorem program_invariant (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (initialFrames : World → Frame (ZMod 2) M) (state : World → M) :
    run (program e frameOf initialFrames) (encode initialFrames state) =
      encode (fun i => frameOf (sink i)) (moduleRun (Shared50GlobalCircuit.program e) state) := by
  rw [program,run_append,first_invariant,tail_invariant]

/-- Exact stored-state semantics, with no clean-data or clean-scratch premise. -/
theorem program_identity (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (initialFrames : World → Frame (ZMod 2) M) (stored : World → M) :
    run (program e frameOf initialFrames) stored =
      encode (fun i => frameOf (sink i))
        (moduleRun (Shared50GlobalCircuit.program e) (decode initialFrames stored)) := by
  conv_lhs => rw [← encode_decode initialFrames stored]
  exact program_invariant e frameOf initialFrames _

/-- The routed initial value uses its own initial frame, including dirty scratch. -/
theorem program_route (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (initialFrames : World → Frame (ZMod 2) M) (stored : World → M) :
    run (program e frameOf initialFrames) stored = fun i => frameOf (sink i)
      ((initialFrames (Shared50ShearEndpoints.route i)).symm (stored (Shared50ShearEndpoints.route i))) := by
  rw [program_identity,Shared50ShearEndpoints.module_route]
  rfl

private theorem edges_pairs_nodup {ι : Type*} [DecidableEq ι]
    (current desired : ι → Frame (ZMod 2) M) (xs : List ι) (hn : xs.Nodup) :
    FramedEdgeTrace.pairs (edges current desired xs) = xs.map (fun i => (current i,desired i)) := by
  induction xs generalizing current with
  | nil => rfl
  | cons i xs ih =>
    obtain ⟨hi,ht⟩ := List.nodup_cons.mp hn
    simp only [edges,FramedEdgeTrace.pairs,List.filterMap_cons,List.map_cons]
    change (current i, desired i) ::
      FramedEdgeTrace.pairs (edges (Function.update current i (desired i)) desired xs) = _
    rw [show FramedEdgeTrace.pairs (edges (Function.update current i (desired i)) desired xs) = _ from ih _ ht]
    congr 1
    apply List.map_congr_left
    intro j hj
    have hji : j ≠ i := by intro h; subst j; exact hi hj
    simp only [Function.update_of_ne hji]

/-- One genuine initial frame pair per actual physical wire, in its fixed order. -/
theorem first_pairs (frameOf : Label → Frame (ZMod 2) M) (initialFrames : World → Frame (ZMod 2) M) :
    FramedEdgeTrace.pairs (first frameOf initialFrames) =
      wires.map (fun i => (initialFrames i,frameOf (input 0 i))) :=
  edges_pairs_nodup _ _ wires (Finset.nodup_toList _)

theorem tail_pairs (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M) :
    FramedEdgeTrace.pairs (tail e frameOf) =
      (RankTrace.edges (input 0) (tailUpdates e)).map (fun p => (frameOf p.1,frameOf p.2)) := by
  have h1 : RankTrace.finish (output 0) (boundaryUpdates 1) = input 1 := boundary_finish 1
  have h2 : RankTrace.finish (output 1) (boundaryUpdates 2) = input 2 := boundary_finish 2
  simp only [tail,FramedEdgeTrace.pairs_append,Shared50GlobalFramed.stage_pairs,
    Shared50GlobalFramed.boundary_pairs,tailUpdates,RankTrace.edges_append,
    RankTrace.finish_append,Shared50GlobalTraceStages.stage_finish,h1,h2,List.map_append,boundaryBefore]

/-- Exact ordered physical frame pairs, rather than an assumed implementation contract. -/
theorem program_pairs (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (initialFrames : World → Frame (ZMod 2) M) :
    FramedEdgeTrace.pairs (program e frameOf initialFrames) =
      wires.map (fun i => (initialFrames i,frameOf (input 0 i))) ++
        (RankTrace.edges (input 0) (tailUpdates e)).map (fun p => (frameOf p.1,frameOf p.2)) := by
  rw [program,FramedEdgeTrace.pairs_append,first_pairs,tail_pairs]

/-- The already proved rational signed physical network is this exact specialization. -/
theorem rational_specialization (e : Fin n ≃ Triple) :
    program e Shared50GlobalShear.frames Shared50GlobalShear.sourceFrames = Shared50GlobalShear.program e := rfl

end
end IntegerMultBounds.Networks.Shared50SignedFramed
