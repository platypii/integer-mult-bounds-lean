module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedRecoveryCouplingRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareRetainedReplicaRecovery

/-! The recovery row invariant is derived from the actual preparation endpoint,
using the first pass's retained coefficient page and geometry. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T A : ℕ} [NeZero s]

theorem preparedRecoveryCouplingReady (H : ReplicaHaloProblem s)
    (job : CachedReplicaPassPlacement T) (buffers : ReplicaLoopBuffers A)
    (S F : Stacks T A) (Ds : List (ZMod s → GaussianInt))
    (post : CachedReplicaPassPost H job buffers S F Ds)
    (ready : RetainedCouplingReady (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
      H.origin (H.origin+H.span) buffers.rhsTail
      (embStk weightCacheCoreReg (embStk job.plan.solver (prepareRetainedReplicaRecoveryState H job F)))) :
    CachedRecoveryCouplingReady H buffers.rhsTail (S.R (job.coupling.bank 138))
      (embStk job.coupling.bank (prepareRetainedReplicaRecoveryState H job F)) := by
  let G := prepareRetainedReplicaRecoveryState H job F
  have hframe (i : Fin 168) (h93 : i ≠ 93) (h159 : i ≠ 159) (h161 : i ≠ 161) :
      G.R (job.coupling.bank i) = F.R (job.coupling.bank i) := by
    simp [G,prepareRetainedReplicaRecoveryState,couplingMasksState,
      job.coupling.bank_injective.eq_iff,h93,h159,h161]
  refine ⟨(job.coupling.native_view G).symm ▸ ready,?_,?_,?_,?_,?_,?_,?_⟩
  · change G.R (job.coupling.bank 138) = _
    rw [hframe 138 (by decide) (by decide) (by decide)]
    exact post.coefficients
  · change (G.R (job.coupling.bank 140)).length = _
    rw [hframe 140 (by decide) (by decide) (by decide)]
    exact post.coefficientRows
  · change (G.R (job.coupling.bank 139)).length = _
    rw [hframe 139 (by decide) (by decide) (by decide)]
    exact post.coefficientWords
  · change G.R (job.coupling.bank 165) = _
    rw [hframe 165 (by decide) (by decide) (by decide)]
    exact post.metadata.count
  · simp [embStk,prepareRetainedReplicaRecoveryState,couplingMasksState,
      job.coupling.bank_injective.eq_iff]
  · simp [embStk,prepareRetainedReplicaRecoveryState,couplingMasksState,
      job.coupling.bank_injective.eq_iff]
  · intro i hi
    have hn : i ≠ (93 : Fin 168) ∧ i ≠ 159 ∧ i ≠ 161 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    change G.R (job.coupling.bank i) = []
    rw [hframe i hn.1 hn.2.1 hn.2.2]
    exact post.fresh i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
