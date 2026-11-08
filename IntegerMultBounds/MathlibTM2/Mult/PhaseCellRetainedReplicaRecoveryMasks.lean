module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaPassPost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedInitializeCouplingMasks

/-! Prepare recovery selectors once from the executed first pass. The retained
numerical bank supplies scratch space and is unchanged by selector generation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem retainedReplicaRecoveryMasks_exec_within (H : ReplicaHaloProblem s)
    (job : CachedReplicaPassPlacement T) (buffers : ReplicaLoopBuffers A)
    (S F : Stacks T A) (Ds : List (ZMod s → GaussianInt))
    (inputs : CachedReplicaPassInput H job buffers S)
    (post : CachedReplicaPassPost H job buffers S F Ds) (v : HS T Q A U) :
    let G := couplingMasksState job.coupling.bank true s H.t H.band H.origin
      (H.origin+H.span) H.origin H.span F
    ∃ vf m, vf.user = v.user ∧ m ≤ initializeRecoveryMasksCost H.metadataWidth H.span H.band ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+
          mnProgPush (initializeCouplingMasks true (P := Empty) (Q := Q) (A := A) (U := U))*
            initializeRecoveryMasksCost H.metadataWidth H.span H.band)
        depth (placedInitializeCouplingMasks job.coupling.bank true) (mk v F) m (mk vf G)) ∧
      RetainedCouplingReady (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
        H.origin (H.origin+H.span) buffers.rhsTail
        (embStk weightCacheCoreReg (embStk job.plan.solver G)) := by
  dsimp only
  have hclean : ∀ i : Fin 168, i.val < 63 → F.R (job.coupling.bank i) = [] := by
    intro i hi
    have hc := (post.ready.clean (⟨i.val,by omega⟩ : Fin 64)).2
    simpa [embStk,weightCacheCoreReg,mul,ReplicaCouplingPlacement.bank,
      show i.val < 117 by omega] using hc
  have hwork : ∀ i ∈ [(136 : Fin 168),159,161], F.R (job.coupling.bank i) = [] := by
    intro i hi
    have hlarge : 117 ≤ i.val := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    have hoff : i ∉ replicaCouplingSetupPorts := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    rw [post.bankFrame i hlarge hoff]
    exact inputs.couplingWork i hi
  obtain ⟨vf,m,hu,hm,he⟩ := placedInitializeCouplingMasks_exec_within (body := body)
    job.coupling.bank job.coupling.bank_injective true H.s_lt_t
    (by have hf := H.span_fit; omega) H.span_fit H.band_fit H.span_fit
    H.coupling_geometry.2 H.coupling_geometry.1 v F post.metadata hclean
    (hwork 136 (by simp)) (post.fresh 158 (by simp))
    (hwork 159 (by simp)) (hwork 161 (by simp))
  refine ⟨vf,m,hu,hm,he,?_⟩
  have hcore : embStk weightCacheCoreReg (embStk job.plan.solver
      (couplingMasksState job.coupling.bank true s H.t H.band H.origin
        (H.origin+H.span) H.origin H.span F)) =
      embStk weightCacheCoreReg (embStk job.plan.solver F) := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    change (couplingMasksState job.coupling.bank true s H.t H.band H.origin
      (H.origin+H.span) H.origin H.span F).R (job.plan.solver (weightCacheCoreReg i)) =
        F.R (job.plan.solver (weightCacheCoreReg i))
    rw [← job.coupling.bank_native i]
    apply couplingMasksState_frame
    · intro h
      have hv := congrArg (fun k : Fin 168 => k.val) (job.coupling.bank_injective h)
      change i.val = 159 at hv
      have hi := i.isLt
      omega
    · intro h
      have hv := congrArg (fun k : Fin 168 => k.val) (job.coupling.bank_injective h)
      change i.val = 161 at hv
      have hi := i.isLt
      omega
  rw [hcore]
  exact post.ready

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
