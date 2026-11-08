module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaConsumerExport

/-! Export consumes the two residual archives while preserving the peripheral
state for both second interior passes. No hidden first-pass inputs are needed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open CyclicReplicaPlacement
variable {A : ℕ}

theorem cyclicReplicaConsumerExportState_retained (S : Stacks 834 A) (rows : List (Fin (A+4)))
    (k : Fin 834) (hk : left.Owns k ∨ right.Owns k)
    (hl : k ≠ left.plan.gather 125) (hr : k ≠ right.plan.gather 125) :
    (cyclicReplicaConsumerExportState S rows).L k = S.L k ∧
      (cyclicReplicaConsumerExportState S rows).R k = S.R k := by
  have hoff (i : Fin 234) : k ≠ factorReg i := by
    intro he
    rcases hk with hk | hk
    · exact (factor_disjoint i).1 (he ▸ hk)
    · exact (factor_disjoint i).2 (he ▸ hk)
  have h := cyclicReplicaConsumerExportState_pass_frame S rows k hk
  exact ⟨h.1,h.2.trans ((cyclicReplicaArchiveHandoff_read _ k hl hr (hoff 169) (hoff 172)).trans
    (cyclicReplicaConsumerHeaders_frame S k hk).2)⟩

theorem cyclicReplicaConsumerExport_resume {s : ℕ} {H K : ReplicaHaloProblem s}
    {buffersL buffersR : ReplicaLoopBuffers A} {S : Stacks 834 A}
    (hL : ReplicaInteriorResumeReady H left buffersL S)
    (hR : ReplicaInteriorResumeReady K right buffersR S) (rows : List (Fin (A+4))) :
    ReplicaInteriorResumeReady H left buffersL (cyclicReplicaConsumerExportState S rows) ∧
      ReplicaInteriorResumeReady K right buffersR (cyclicReplicaConsumerExportState S rows) := by
  have keep (job : CachedReplicaPassPlacement 834) (J : ReplicaHaloProblem s) (buffers : ReplicaLoopBuffers A)
      (h : ReplicaInteriorResumeReady J job buffers S)
      (howns : ∀ k, job.Owns k → left.Owns k ∨ right.Owns k)
      (haway : ∀ k, job.Owns k → k ≠ job.plan.gather 125 →
        k ≠ left.plan.gather 125 ∧ k ≠ right.plan.gather 125) :
      ReplicaInteriorResumeReady J job buffers (cyclicReplicaConsumerExportState S rows) := by
    have hf (k : Fin 834) (hk : job.Owns k) (h125 : k ≠ job.plan.gather 125) :=
      (cyclicReplicaConsumerExportState_retained S rows k (howns k hk)
        (haway k hk h125).1 (haway k hk h125).2).2
    apply h.transport (job' := job) (F := cyclicReplicaConsumerExportState S rows) rfl rfl
    · intro i hi; exact hf _ (.gather i) (job.plan.gather_injective.ne hi)
    · intro i _; exact hf _ (.solver i) (job.plan.disjoint 125 i).symm
    · intro i
      exact (cyclicReplicaConsumerExportState_pass_frame S rows _ (howns _ (.solver (weightCacheCoreReg i)))).1
    · exact hf _ .output (job.gather_output 125).symm
  constructor
  · apply keep left H buffersL hL (fun _ hk => Or.inl hk)
    intro k hk h125
    exact ⟨h125,fun he => disjoint _ (he ▸ hk) (.gather 125)⟩
  · apply keep right K buffersR hR (fun _ hk => Or.inr hk)
    intro k hk h125
    exact ⟨fun he => disjoint _ (.gather 125) (he ▸ hk),h125⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
