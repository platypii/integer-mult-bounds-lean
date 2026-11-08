module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedCachedReplicaInteriorCoupling

/-! Local prerequisites of one existing cached pass. Disjoint passes transport
this contract through their ordinary tape frame, without repeating setup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

structure CachedReplicaPassPlacement (T : ℕ) where
  plan : ReplicaInteriorPlacement T
  coupling : ReplicaCouplingPlacement plan
  output : Fin T
  rhs : Fin T
  gather_output : ∀ i, plan.gather i ≠ output
  gather_rhs : ∀ i, plan.gather i ≠ rhs
  bank_output : ∀ i, coupling.bank i ≠ output
  bank_rhs : ∀ i, coupling.bank i ≠ rhs
  solver_output : ∀ i, plan.solver i ≠ output
  solver_rhs : ∀ i, plan.solver i ≠ rhs
  output_rhs : output ≠ rhs

inductive CachedReplicaPassPlacement.Owns {T : ℕ} (job : CachedReplicaPassPlacement T) : Fin T → Prop
  | bank (i : Fin 168) : Owns job (job.coupling.bank i)
  | gather (i : Fin 126) : Owns job (job.plan.gather i)
  | solver (i : Fin 121) : Owns job (job.plan.solver i)
  | output : Owns job job.output
  | rhs : Owns job job.rhs

structure CachedReplicaPassInput {s T A : ℕ} (H : ReplicaHaloProblem s)
    (job : CachedReplicaPassPlacement T) (buffers : ReplicaLoopBuffers A) (S : Stacks T A) : Prop where
  headers : ReplicaLoopHeaders H job.plan.gather buffers S
  bank : embStk weightCacheCoreReg (embStk job.plan.solver S) =
    releasedCellBank [] buffers.rhsTail buffers.solverOutputTail S.inp S.out
  cache : S.R (job.plan.solver 117) = buffers.cacheTail
  solverFresh : ∀ i ∈ [(118 : Fin 121),119,120], S.R (job.plan.solver i) = []
  input : S.inp = buffers.input
  outputStream : S.out = buffers.output
  savedGather : embStk job.plan.gather S = buffers.savedGather
  keys : S.R (job.plan.gather 87) = buffers.keyTail
  destination : S.R job.output = buffers.accumulatorTail
  gatherFresh : ∀ i ∈ [(86 : Fin 126),119], S.R (job.plan.gather i) = []
  couplingBlank : ∀ i ∈ [(145 : Fin 168),146,147,148,149,151,154,155,156,157,163,164,165],
    S.R (job.coupling.bank i) = []
  couplingFresh : ∀ i ∈ [(127 : Fin 168),135,139,140,143,158,166,167], S.R (job.coupling.bank i) = []
  couplingWork : ∀ i ∈ [(136 : Fin 168),159,161], S.R (job.coupling.bank i) = []

theorem CachedReplicaPassInput.of_frame {s T A : ℕ} {H : ReplicaHaloProblem s}
    {job : CachedReplicaPassPlacement T} {buffers : ReplicaLoopBuffers A} {S F : Stacks T A}
    (h : CachedReplicaPassInput H job buffers S) (hin : F.inp = S.inp) (hout : F.out = S.out)
    (hf : ∀ k, job.Owns k → F.L k = S.L k ∧ F.R k = S.R k) :
    CachedReplicaPassInput H job buffers F := by
  have hg : embStk job.plan.gather F = embStk job.plan.gather S := by
    refine Stacks.ext hin hout ?_ ?_
    · funext i; exact (hf _ (.gather i)).1
    · funext i; exact (hf _ (.gather i)).2
  have hs : embStk job.plan.solver F = embStk job.plan.solver S := by
    refine Stacks.ext hin hout ?_ ?_
    · funext i; exact (hf _ (.solver i)).1
    · funext i; exact (hf _ (.solver i)).2
  refine ⟨?_,?_,?_,?_,hin.trans h.input,hout.trans h.outputStream,hg.trans h.savedGather,?_,?_,?_,?_,?_,?_⟩
  · apply h.headers.of_frame
    intro i _ _
    exact (hf _ (.gather i)).2
  · rw [hs,hin,hout]; exact h.bank
  · exact (hf _ (.solver 117)).2.trans h.cache
  · intro i hi; exact (hf _ (.solver i)).2.trans (h.solverFresh i hi)
  · exact (hf _ (.gather 87)).2.trans h.keys
  · exact (hf _ .output).2.trans h.destination
  · intro i hi; exact (hf _ (.gather i)).2.trans (h.gatherFresh i hi)
  · intro i hi; exact (hf _ (.bank i)).2.trans (h.couplingBlank i hi)
  · intro i hi; exact (hf _ (.bank i)).2.trans (h.couplingFresh i hi)
  · intro i hi; exact (hf _ (.bank i)).2.trans (h.couplingWork i hi)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
