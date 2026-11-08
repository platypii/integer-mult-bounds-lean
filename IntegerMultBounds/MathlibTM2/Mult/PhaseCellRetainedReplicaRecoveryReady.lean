module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaPassPost

/-! Recovery keeps the numerical bank and original RHS headers, not the already
consumed residual archive. This contract transports through archive handoff. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T A : ℕ} [NeZero s]

structure RetainedReplicaRecoveryReady (H : ReplicaHaloProblem s) (job : CachedReplicaPassPlacement T)
    (buffers : ReplicaLoopBuffers A) (pageTail : List (Fin (A+4))) (F : Stacks T A) : Prop where
  ready : RetainedCouplingReady (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin
    (H.origin+H.span) buffers.rhsTail (embStk groupReg (embStk intervalPageReg (embStk job.coupling.bank F)))
  metadata : CouplingIntervalMetadata H.metadataWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span (embStk job.coupling.bank F)
  coefficients : F.R (job.coupling.bank 138) = cstream A H.wordWidth
    (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span)++pageTail
  coefficientWords : (F.R (job.coupling.bank 139)).length = (couplingCoefficientPageInterval
    (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span).length
  coefficientRows : (F.R (job.coupling.bank 140)).length = 2*H.band+1
  fresh : ∀ i ∈ [(127 : Fin 168),143,166,158,135,167], F.R (job.coupling.bank i) = []
  work : ∀ i ∈ [(136 : Fin 168),159,161], F.R (job.coupling.bank i) = []
  recoveryRhs : ReplicaRecoveryRhsHeaders H job.plan.gather buffers F

theorem CachedReplicaPassPost.recovery_ready {H : ReplicaHaloProblem s} {job : CachedReplicaPassPlacement T}
    {buffers : ReplicaLoopBuffers A} {S F : Stacks T A} {Ds : List (ZMod s → GaussianInt)}
    (post : CachedReplicaPassPost H job buffers S F Ds) :
    RetainedReplicaRecoveryReady H job buffers (S.R (job.coupling.bank 138)) F := by
  exact ⟨(job.coupling.native_view F).symm ▸ post.ready,post.metadata,post.coefficients,
    post.coefficientWords,post.coefficientRows,post.fresh,post.recoveryWork,post.recoveryRhs⟩

theorem RetainedReplicaRecoveryReady.of_bank_frame {H : ReplicaHaloProblem s} {job : CachedReplicaPassPlacement T}
    {buffers : ReplicaLoopBuffers A} {pageTail : List (Fin (A+4))} {F : Stacks T A}
    {T' : ℕ} {job' : CachedReplicaPassPlacement T'} {G : Stacks T' A}
    (h : RetainedReplicaRecoveryReady H job buffers pageTail F)
    (hbank : embStk job'.coupling.bank G = embStk job.coupling.bank F)
    (headers : ReplicaRecoveryRhsHeaders H job'.plan.gather buffers G) :
    RetainedReplicaRecoveryReady H job' buffers pageTail G := by
  have hr (i : Fin 168) : G.R (job'.coupling.bank i) = F.R (job.coupling.bank i) :=
    congrArg (fun S : Stacks 168 A => S.R i) hbank
  refine ⟨?_,?_,?_,?_,?_,?_,?_,headers⟩
  · rw [hbank]; exact h.ready
  · rw [hbank]; exact h.metadata
  · rw [hr]; exact h.coefficients
  · rw [hr]; exact h.coefficientWords
  · rw [hr]; exact h.coefficientRows
  · intro i hi; rw [hr]; exact h.fresh i hi
  · intro i hi; rw [hr]; exact h.work i hi

theorem RetainedReplicaRecoveryReady.of_owns_frame {H : ReplicaHaloProblem s}
    {job : CachedReplicaPassPlacement T} {buffers : ReplicaLoopBuffers A}
    {pageTail : List (Fin (A+4))} {F G : Stacks T A}
    (h : RetainedReplicaRecoveryReady H job buffers pageTail F)
    (hin : G.inp = F.inp) (hout : G.out = F.out)
    (hf : ∀ k, job.Owns k → G.L k = F.L k ∧ G.R k = F.R k) :
    RetainedReplicaRecoveryReady H job buffers pageTail G := by
  apply h.of_bank_frame
  · refine Stacks.ext hin hout ?_ ?_
    · funext i; exact (hf _ (.bank i)).1
    · funext i; exact (hf _ (.bank i)).2
  · apply h.recoveryRhs.of_frame H job.plan.gather buffers F G
    intro i; exact (hf _ (.gather i)).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
