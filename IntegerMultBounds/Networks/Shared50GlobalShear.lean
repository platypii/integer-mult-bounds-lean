import IntegerMultBounds.Networks.Shared50GlobalFramed
import IntegerMultBounds.Networks.Shared50GlobalProjectionRank
import IntegerMultBounds.Networks.Shared50SignedBoundary
import IntegerMultBounds.Networks.Shared50ShearEndpoints

/-! Full signed physical optimized network, with actual shear-operator ranks.
The first boundary uses the negative source frames. Every subsequent physical
instruction is the existing optimized reused-world program. All binary arrays,
including arbitrary dirty scratch arrays, undergo a uniform full address shear
after the exact data-bank exchange. Finite-radix and tape realization are separate. -/

namespace IntegerMultBounds.Networks.Shared50GlobalShear

noncomputable section
open FramedCircuit Shared50GlobalTrace
open Shared50GlobalBudget (World Ambient Triple sourceTotal)
open Shared50ReuseLabels (cubeForm cube_symm)
open Shared50InvocationProjectionRank (rangeRank Realizes)

variable {n : ℕ}
abbrev Arrays := (Ambient × Ambient) → ZMod 2

def frames : Label → Frame (ZMod 2) Arrays :=
  Shared50InvocationProjectionRank.projectorFrame cubeForm cube_symm

def sourceFrames (i : World) : Frame (ZMod 2) Arrays :=
  ShearFrame.frame (-Shared50ShearEndpoints.projector (source i))

/-- The unchanged physical suffix after the first boundary. -/
def tail (e : Fin n ≃ Triple) : List (Instruction World (ZMod 2) Arrays) :=
  Shared50GlobalFramed.stage e frames 0 ++ Shared50GlobalFramed.boundary frames 1 ++
    Shared50GlobalFramed.stage e frames 1 ++ Shared50GlobalFramed.boundary frames 2 ++
    Shared50GlobalFramed.stage e frames 2 ++ Shared50GlobalFramed.boundary frames 3

def tailUpdates (e : Fin n ≃ Triple) : List (World × Label) :=
  Shared50GlobalTraceStages.stageUpdates e 0 ++ boundaryUpdates 1 ++
    Shared50GlobalTraceStages.stageUpdates e 1 ++ boundaryUpdates 2 ++
    Shared50GlobalTraceStages.stageUpdates e 2 ++ boundaryUpdates 3

/-- Literal signed physical network: replace exactly its first boundary. -/
def program (e : Fin n ≃ Triple) : List (Instruction World (ZMod 2) Arrays) :=
  Shared50SignedBoundary.physical ++ tail e

/-- Signed source alignment adds no scalar arithmetic instruction. -/
theorem scalar_erasure (e : Fin n ≃ Triple) :
    BoundedFramedCircuit.erase (program e) = Shared50GlobalCircuit.program e := by
  have hs : BoundedFramedCircuit.erase Shared50SignedBoundary.physical = [] :=
    Shared50FramedInvocation.erase_align (fun f : Frame (ZMod 2) Arrays => f)
      sourceFrames (fun i => frames (input 0 i))
  simp only [program,tail,Shared50FramedInvocation.erase_append,hs,
    Shared50GlobalFramed.stage_erasure,Shared50GlobalFramed.boundary_erasure,
    List.nil_append,List.append_nil,Shared50GlobalCircuit.program]

theorem tail_invariant (e : Fin n ≃ Triple) (state : World → Arrays) :
    run (tail e) (encode (fun i => frames (input 0 i)) state) =
      encode (fun i => frames (sink i)) (moduleRun (Shared50GlobalCircuit.program e) state) := by
  have h1 (v : World → Arrays) : run (Shared50GlobalFramed.boundary frames 1)
      (encode (fun i => frames (output 0 i)) v) = encode (fun i => frames (input 1 i)) v :=
    Shared50GlobalFramed.boundary_run frames 1 v
  have h2 (v : World → Arrays) : run (Shared50GlobalFramed.boundary frames 2)
      (encode (fun i => frames (output 1 i)) v) = encode (fun i => frames (input 2 i)) v :=
    Shared50GlobalFramed.boundary_run frames 2 v
  have h3 (v : World → Arrays) : run (Shared50GlobalFramed.boundary frames 3)
      (encode (fun i => frames (output 2 i)) v) = encode (fun i => frames (sink i)) v :=
    Shared50GlobalFramed.boundary_run frames 3 v
  simp only [tail,run_append,Shared50GlobalFramed.stage_run,h1,h2,h3,
    Shared50GlobalCircuit.program,GroupedModuleFrames.moduleRun_append]

theorem signed_boundary_run (state : World → Arrays) :
    run Shared50SignedBoundary.physical (encode sourceFrames state) =
      encode (fun i => frames (input 0 i)) state := by
  change run (edges sourceFrames (fun i => frames (input 0 i)) wires) (encode sourceFrames state) = _
  rw [edges_invariant]
  congr 1
  funext i
  simp only [afterEdges_apply,mem_wires,ite_true]

theorem program_invariant (e : Fin n ≃ Triple) (state : World → Arrays) :
    run (program e) (encode sourceFrames state) =
      encode (fun i => frames (sink i)) (fun i => state (Shared50ShearEndpoints.route i)) := by
  rw [program,run_append,signed_boundary_run,tail_invariant,Shared50ShearEndpoints.module_route]

/-- Exact full shear on every output array, for arbitrary stored scratch. -/
theorem program_identity (e : Fin n ≃ Triple) (stored : World → Arrays) :
    run (program e) stored = fun i =>
      ShearFrame.frame (LinearMap.id : Ambient →ₗ[ℚ] Ambient)
        (stored (Shared50ShearEndpoints.route i)) := by
  conv_lhs => rw [← encode_decode sourceFrames stored]
  rw [program_invariant]
  funext i
  exact Shared50ShearEndpoints.frame_endpoint i _

/-- Actual suffix operators, preserving every physical edge and its order. -/
def tailOperators (e : Fin n ≃ Triple) : List (Ambient →ₗ[ℚ] Ambient) :=
  Shared50InvocationProjectionRank.operators cubeForm cube_symm (input 0) (tailUpdates e)

def operators (e : Fin n ≃ Triple) : List (Ambient →ₗ[ℚ] Ambient) :=
  Shared50SignedBoundary.operators ++ tailOperators e

def rankSum (e : Fin n ≃ Triple) : ℕ := ((operators e).map rangeRank).sum

theorem tail_pairs (e : Fin n ≃ Triple) :
    FramedEdgeTrace.pairs (tail e) =
      (RankTrace.edges (input 0) (tailUpdates e)).map (fun p => (frames p.1,frames p.2)) := by
  have h1 : RankTrace.finish (output 0) (boundaryUpdates 1) = input 1 := boundary_finish 1
  have h2 : RankTrace.finish (output 1) (boundaryUpdates 2) = input 2 := boundary_finish 2
  simp only [tail,FramedEdgeTrace.pairs_append,Shared50GlobalFramed.stage_pairs,
    Shared50GlobalFramed.boundary_pairs,tailUpdates,RankTrace.edges_append,
    RankTrace.finish_append,Shared50GlobalTraceStages.stage_finish,h1,h2,List.map_append,boundaryBefore]

theorem tail_realizes (e : Fin n ≃ Triple) :
    List.Forall₂ Realizes (FramedEdgeTrace.pairs (tail e)) (tailOperators e) :=
  Shared50InvocationProjectionRank.physical_realizes _ _ _ _ _ (tail_pairs e)

/-- Every actual signed physical frame change has its counted shear matrix. -/
theorem physical_realizes (e : Fin n ≃ Triple) :
    List.Forall₂ Realizes (FramedEdgeTrace.pairs (program e)) (operators e) := by
  rw [program,FramedEdgeTrace.pairs_append,operators]
  exact List.rel_append Shared50SignedBoundary.physical_realizes (tail_realizes e)

private theorem sum_operators_append {ι V : Type*} [DecidableEq ι] [AddCommGroup V]
    [Module ℚ V] [FiniteDimensional ℚ V] (B : LinearMap.BilinForm ℚ V) (hs : B.IsSymm)
    (current : ι → Submodule ℚ V) (left right : List (ι × Submodule ℚ V)) :
    ((Shared50InvocationProjectionRank.operators B hs current (left ++ right)).map rangeRank).sum =
      ProjectionTrace.rankSum B hs current left +
      ((Shared50InvocationProjectionRank.operators B hs (RankTrace.finish current left) right).map rangeRank).sum := by
  simp only [Shared50InvocationProjectionRank.operators,RankTrace.edges_append,List.map_append,List.sum_append]
  congr 1
  simp only [ProjectionTrace.rankSum,List.map_map]
  rfl

theorem ordinary_rank_split (e : Fin n ≃ Triple) :
    Shared50GlobalProjectionRank.rankSum e =
      ProjectionTrace.rankSum cubeForm cube_symm source (boundaryUpdates 0) +
        ((tailOperators e).map rangeRank).sum := by
  have ht : Shared50GlobalTraceStages.trace e = boundaryUpdates 0 ++ tailUpdates e := by
    simp only [Shared50GlobalTraceStages.trace,tailUpdates,List.append_assoc]
  have hf : RankTrace.finish source (boundaryUpdates 0) = input 0 := boundary_finish 0
  unfold Shared50GlobalProjectionRank.rankSum Shared50GlobalProjectionRank.operators
  rw [ht,sum_operators_append,hf]
  rfl

/-- Replacing the actual first boundary adds exactly the proved source total. -/
theorem rankSum_eq (e : Fin n ≃ Triple) :
    rankSum e = Shared50GlobalProjectionRank.rankSum e + sourceTotal := by
  have hb := Shared50SignedBoundary.operators_rankSum_eq_trace
  have ht := ordinary_rank_split e
  unfold rankSum operators
  rw [List.map_append,List.sum_append]
  change _ + _ = _
  change ((Shared50SignedBoundary.operators.map rangeRank).sum) = _ at hb
  omega

/-- Exact improved budget for the actual signed physical operator list. -/
theorem rankSum50_exact : rankSum Shared50GlobalCircuit.enumeration = Shared50Parameters.s := by
  rw [rankSum_eq]
  exact Shared50GlobalProjectionRank.corrected_rank_exact

/-- The real signed physical network meets the selected strict branching bound. -/
theorem branching_bound :
    ((rankSum Shared50GlobalCircuit.enumeration : ℕ) : ℝ) / Shared50Parameters.W <
      (Shared50Parameters.m : ℝ) ^ Parameters.tau := by
  rw [rankSum50_exact]
  exact Shared50Parameters.branching_bound

end
end IntegerMultBounds.Networks.Shared50GlobalShear
