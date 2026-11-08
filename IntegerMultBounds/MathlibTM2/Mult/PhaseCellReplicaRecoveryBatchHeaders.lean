module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryProblem
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaProblemLayout

/-! Recovery uses the same geometry and arithmetic format. Replacing only
the source rows suffices to reuse the ordinary batched-interior headers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T A : ℕ} [NeZero s]

theorem ReplicaRecoveryBatch.problem_layout {H : ReplicaHaloProblem s} {target : ℕ}
    {X : ℕ → ZMod s → ℝ} (B : ReplicaRecoveryBatch H target X) (htarget) :
    H.SameLayout (B.problem htarget) := by
  obtain ⟨hq,hstage,hw,_⟩ := B.problem_sizing htarget
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,hq,hstage,hw,B.inputs_length⟩

theorem ReplicaRecoveryBatch.headers {H : ReplicaHaloProblem s} {target : ℕ} {X : ℕ → ZMod s → ℝ}
    (B : ReplicaRecoveryBatch H target X) (htarget)
    (gather : Fin 126 → Fin T) (buffers nextBuffers : ReplicaLoopBuffers A) (S F : Stacks T A)
    (h : ReplicaLoopHeaders H gather buffers S)
    (hframe : ∀ k : Fin 126, k ≠ 124 → F.R (gather k) = S.R (gather k))
    (hsource : F.R (gather 124) = B.inputs.flatMap
      (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R))++nextBuffers.packedRhsTail) :
    ReplicaLoopHeaders (B.problem htarget) gather nextBuffers F := by
  apply h.replace_source (B.problem_layout htarget) gather buffers nextBuffers S F hframe
  have hw := (B.problem_sizing htarget).2.2.1
  change F.R (gather 124) = B.inputs.flatMap
    (fun R => cstream A (B.problem htarget).wordWidth (packedInterval H.origin H.span R))++nextBuffers.packedRhsTail
  rw [hw]
  exact hsource

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
