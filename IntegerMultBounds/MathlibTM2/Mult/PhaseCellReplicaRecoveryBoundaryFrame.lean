module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryPhasePlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryRhs

/-! Persistent boundary headers and a restored recovery core supply the next
boundary row's physical readiness, independently of the recovered field. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
variable {s A : ℕ} [NeZero s]

theorem ReplicaBoundaryRhsReady.of_recovery_core (H : ReplicaHaloProblem s) (W : ℕ)
    {S F : Stacks 255 A} (h : ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg S))
    (hcore : ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) F))
    (hpersistent : ∀ k : Fin 255, 248 ≤ k.val → F.R k = S.R k) :
    ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg F) := by
  have hheader (i : Fin 242) (hi : i ∈ [116,117,118,120,123,124,167]) :
      (embStk replicaBoundaryPhaseReg F).R i = (embStk replicaBoundaryPhaseReg S).R i := by
    apply hpersistent
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  constructor
  · rw [hheader 123 (by decide)]; exact h.volume
  · rw [hheader 124 (by decide)]; exact h.rhsVolume
  · exact (hheader 167 (by decide)).trans h.mask
  · change (F.R (replicaBoundaryPhaseReg 130)).length = H.wordWidth
    rw [replicaBoundaryPhaseReg_fixed _ (by decide)]
    exact hcore.masters.width
  · rw [hheader 116 (by decide)]; exact h.count
  · rw [hheader 117 (by decide)]; exact h.floor
  · rw [hheader 118 (by decide)]; exact h.parity
  · rw [hheader 120 (by decide)]; exact h.bytes
  · change F.R (replicaBoundaryPhaseReg 104) = []
    rw [replicaBoundaryPhaseReg_fixed _ (by decide)]
    exact hcore.native 104 (by decide) (by decide) (by decide)
  · change F.R (replicaBoundaryPhaseReg 105) = []
    rw [replicaBoundaryPhaseReg_fixed _ (by decide)]
    exact hcore.native 105 (by decide) (by decide) (by decide)
  · change F.R (replicaBoundaryPhaseReg 143) = []
    rw [replicaBoundaryPhaseReg_fixed _ (by decide)]
    exact hcore.rhs
  · intro i hi
    change F.R (replicaBoundaryPhaseReg i) = []
    rw [replicaBoundaryPhaseReg_fixed i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
      norm_num
      omega)]
    exact hcore.native ⟨i.val,by omega⟩
      (by intro he; have hv := congrArg Fin.val he; norm_num at hv; omega)
      (by intro he; have hv := congrArg Fin.val he; norm_num at hv; omega)
      (by intro he; have hv := congrArg Fin.val he; norm_num at hv; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
