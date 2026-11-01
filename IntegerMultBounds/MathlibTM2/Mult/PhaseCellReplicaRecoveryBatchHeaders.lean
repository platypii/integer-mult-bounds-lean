module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryProblem

/-! Recovery uses the same geometry and arithmetic format. Replacing only
the source rows suffices to reuse the ordinary batched-interior headers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T A : ℕ} [NeZero s]

theorem ReplicaRecoveryBatch.headers {H : ReplicaHaloProblem s} {target : ℕ} {X : ℕ → ZMod s → ℝ}
    (B : ReplicaRecoveryBatch H target X) (htarget)
    (gather : Fin 126 → Fin T) (buffers nextBuffers : ReplicaLoopBuffers A) (S F : Stacks T A)
    (h : ReplicaLoopHeaders H gather buffers S)
    (hframe : ∀ k : Fin 126, k ≠ 124 → F.R (gather k) = S.R (gather k))
    (hsource : F.R (gather 124) = B.inputs.flatMap
      (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R))++nextBuffers.packedRhsTail) :
    ReplicaLoopHeaders (B.problem htarget) gather nextBuffers F := by
  obtain ⟨hq,hstage,hw,hmeta⟩ := B.problem_sizing htarget
  have hcount : (B.problem htarget).Fs.length = H.Fs.length := B.inputs_length
  constructor
  · intro r hr h102 h116
    have hall : replicaFactoryHeaderCopies.all (fun r => decide (r.1 ≠ 124)) = true := by decide +kernel
    have h124 : r.1 ≠ 124 := of_decide_eq_true (List.all_eq_true.mp hall r hr)
    rw [hframe r.1 h124]
    change (S.R (gather r.1)).length = replicaFactoryHeaderValue (2^15*H.p)
      ((B.problem htarget).stage+1) (B.problem htarget).precision H.l s H.t H.u H.band
      (B.problem htarget).Fs.length 0 0 (B.problem htarget).wordWidth r.1
    rw [hstage,hq,hw,hcount]
    exact h.masters r hr h102 h116
  · rw [hframe 111 (by decide)]; exact h.origin
  · rw [hframe 113 (by decide)]; exact h.endpoint
  · rw [hmeta,hframe 115 (by decide)]; exact h.width
  · rw [hw,hframe 123 (by decide)]; exact h.volume
  · change F.R (gather 124) = B.inputs.flatMap
      (fun R => cstream A (B.problem htarget).wordWidth (packedInterval H.origin H.span R))++nextBuffers.packedRhsTail
    rw [hw]
    exact hsource
  · intro k hk
    rw [hframe k (by intro he; subst k; norm_num at hk)]
    exact h.blank k hk
  · intro k hk
    have h124 : k ≠ 124 := by intro he; subst k; norm_num at hk
    rw [hframe k h124]
    exact h.fresh k hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
