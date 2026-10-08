import IntegerMultBounds.Networks.Shared50FramedInvocation
import IntegerMultBounds.Networks.Shared50PhysicalEdges

/-! The complete forward physical instruction list has exactly the ordered
frame edges used in the proved local rank history. Scalar erasure, execution
and rank accounting thus describe the same sparse invocation. -/

namespace IntegerMultBounds.Networks.Shared50InvocationPhysicalEdges

open scoped TensorProduct
open FramedCircuit FramedEdgeTrace MotifLabels Shared50StageFrames
  Shared50LabeledInvocation Shared50FramedInvocation NeighborCounts

variable {n s : ℕ} {E H M : Type*} [AddCommGroup E] [Module ℚ E]
  [AddCommGroup H] [Module ℚ H] [AddCommGroup M] [Module (ZMod 2) M]

theorem align_pairs {ι L : Type*} [Fintype ι] [DecidableEq ι]
    (frameOf : L → Frame (ZMod 2) M) (current desired : ι → L) :
    pairs (Shared50FramedInvocation.align frameOf current desired) =
      (RankTrace.edges current (Shared50InvocationRank.align desired)).map
        (fun p => (frameOf p.1,frameOf p.2)) :=
  pairs_edges frameOf current desired _

theorem middle_pairs (g : Geometry ℚ E Factor) (q : H)
    (frameOf : Space E H → Frame (ZMod 2) M) :
    pairs (Shared50FramedInvocation.middle (n := n) (s := s) g q frameOf) =
      (RankTrace.edges (returned (n := n) (s := s) g q) (Shared50InvocationRank.middleUpdates g q)).map
        (fun p => (frameOf p.1,frameOf p.2)) := by
  rw [Shared50FramedInvocation.middle,pairs_embed,Shared50PhysicalEdges.forward,Shared50InvocationRank.middle_edges,List.map_map]
  rfl

/-- Every physical old/new frame pair, in order, comes from the proved full
label history; identity edges and repeated incidences are retained. -/
theorem program_pairs (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (frameOf : Space E H → Frame (ZMod 2) M) (initial : Wire n s → Space E H) :
    pairs (program g q e frameOf initial) =
      (RankTrace.edges initial (Shared50InvocationRank.updates g q e)).map
        (fun p => (frameOf p.1,frameOf p.2)) := by
  simp only [program,pairs_append,scalar,pairs_gates,align_pairs,middle_pairs,
    List.append_nil,Shared50InvocationRank.updates,
    RankTrace.edges_append,RankTrace.finish_append,Shared50InvocationRank.align_finish,
    Shared50InvocationRank.middle_finish,List.map_append]

end IntegerMultBounds.Networks.Shared50InvocationPhysicalEdges
