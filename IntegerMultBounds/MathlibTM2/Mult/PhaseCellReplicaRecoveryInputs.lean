module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryInputBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryPhaseBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryRhs

/-! The retained boundary phase supplies the dimensions and disposable headers
for staging an actual encoded original RHS before local recovery. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 255 Q A U}

def replicaRecoveryInputsCost (H : ReplicaHaloProblem s) :=
  14*(H.span*H.wordWidth)+4*(haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+6*H.span+24

theorem replicaRecoveryInputs_exec (H : ReplicaHaloProblem s) (W : ℕ)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4))) (v : HS 255 Q A U) (S : Stacks 255 A)
    (hphysical : ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg S))
    (hbank : PackedPreparedBank H.precision H.wordWidth W
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card (embStk (Fin.castLE (by decide : 242 ≤ 255)) S))
    (hsource : S.R 93 = cstream A H.wordWidth (packedInterval H.origin H.span C)++tail)
    (h116 : S.R 116 = []) (h167 : S.R 167 = []) :
    let F := preparedReplicaRecoveryInputState S (cstream A H.wordWidth (packedInterval H.origin H.span C)) tail
    ∃ v', v'.user = v.user ∧
      Exec body prepareReplicaRecoveryInputs (mk v S) (replicaRecoveryInputsCost H) (mk v' F) ∧
      PackedPreparedBank H.precision H.wordWidth W
        (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card (embStk (Fin.castLE (by decide : 242 ≤ 255)) F) ∧
      F.R 116 = List.replicate (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card tick ∧
      F.R 167 = couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin (H.origin+H.span) H.origin H.span := by
  dsimp only
  have hlen : (cstream A H.wordWidth (packedInterval H.origin H.span C)).length = H.span*H.wordWidth := by
    have hfit := H.span_fit
    simp [packedInterval]
    omega
  have hvolume : (S.R 251).length = H.span*H.wordWidth := by
    have hh := hphysical.volume
    change (S.R (replicaBoundaryPhaseReg 123)).length = _ at hh
    simpa only [replicaBoundaryPhaseReg_volume] using hh
  have hcount : (S.R 253).length = (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card := by
    have hh := hphysical.count
    change (S.R (replicaBoundaryPhaseReg 116)).length = _ at hh
    simpa only [replicaBoundaryPhaseReg_count] using hh
  have hmask : S.R 254 = couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin (H.origin+H.span) H.origin H.span := by
    have hh := hphysical.mask
    change S.R (replicaBoundaryPhaseReg 167) = _ at hh
    simpa only [replicaBoundaryPhaseReg_mask] using hh
  have hfresh : S.R 0 = [] ∧ S.R 1 = [] ∧ S.R 104 = [] ∧ S.R 105 = [] := by
    constructor
    · have hh := hphysical.scratch 0 (by decide)
      change S.R (replicaBoundaryPhaseReg 0) = [] at hh
      rw [replicaBoundaryPhaseReg_fixed _ (by decide)] at hh
      exact hh
    constructor
    · have hh := hphysical.scratch 1 (by decide)
      change S.R (replicaBoundaryPhaseReg 1) = [] at hh
      rw [replicaBoundaryPhaseReg_fixed _ (by decide)] at hh
      exact hh
    constructor
    · have hh := hphysical.saved
      change S.R (replicaBoundaryPhaseReg 104) = [] at hh
      rw [replicaBoundaryPhaseReg_fixed _ (by decide)] at hh
      exact hh
    · have hh := hphysical.tmp
      change S.R (replicaBoundaryPhaseReg 105) = [] at hh
      rw [replicaBoundaryPhaseReg_fixed _ (by decide)] at hh
      exact hh
  obtain ⟨v',hu,he⟩ := prepareReplicaRecoveryInputs_exec (body := body) v S
    (cstream A H.wordWidth (packedInterval H.origin H.span C)) tail hsource (by rw [hlen]; exact hvolume)
    hfresh.1 hfresh.2.1 hfresh.2.2.1 hfresh.2.2.2 h116 h167
  refine ⟨v',hu,?_,preparedBank_prepare_recovery_inputs S _ tail hbank,?_,?_⟩
  · simpa only [hlen,hcount,hmask,couplingSourceIntervalMaskSymbols_length,replicaRecoveryInputsCost] using he
  · simp [preparedReplicaRecoveryInputState,seededReplicaRecoveryState,stagedReplicaRecoveryRhsState,hcount]
  · simp [preparedReplicaRecoveryInputState,seededReplicaRecoveryState,stagedReplicaRecoveryRhsState,hmask]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
