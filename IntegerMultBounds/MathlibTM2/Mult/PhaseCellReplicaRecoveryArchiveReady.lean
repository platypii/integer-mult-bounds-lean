module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedReplicaRecoveryPreparation
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryOwnedFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryBoundaryFrame

/-! Installing the two input queues preserves the shared recovery language.
The cursor is supplied by the executed archive handoff, independently of factors. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s A : ℕ} [NeZero s]

theorem replicaRecoveryPreparationReady_of_archive_frame (H : ReplicaHaloProblem s) (target : ℕ)
    (X : ℕ → ZMod s → ℝ) (columns : List (ZMod s → GaussianInt))
    (residualTail rhsTail boundaryTail recoveryTail : List (Fin (A+4))) {S F : Stacks 257 A}
    (hcursor : ReplicaRecoveryPreparationCursor H target X residualTail rhsTail boundaryTail recoveryTail 0 F)
    (hfactor : ReplicaBoundaryFactorData H target columns (embStk (Fin.castLE (by decide : 242 ≤ 257)) S))
    (hleft : ∀ i : Fin 242, S.L (Fin.castLE (by decide : 242 ≤ 257) i) =
      S.L (Fin.castLE (by decide : 255 ≤ 257) (replicaBoundaryPhaseReg i)))
    (hphysical : ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg
      (embStk (Fin.castLE (by decide : 255 ≤ 257)) S)))
    (hcore : ReplicaRecoveryCoreReady H (12*H.band+1) (embStk (Fin.castLE (by decide : 248 ≤ 257)) S))
    (hcount : S.R 116 = []) (hmask : S.R 167 = []) (hL : F.L = S.L)
    (hframe : ∀ k : Fin 257, k ≠ 93 → k ≠ 238 → F.R k = S.R k) :
    ReplicaRecoveryPreparationReady H target X columns residualTail rhsTail boundaryTail recoveryTail F := by
  have hc : ReplicaRecoveryCoreReady H (12*H.band+1)
      (embStk (Fin.castLE (by decide : 248 ≤ 257)) F) := by
    apply hcore.of_owned_frame H (12*H.band+1)
      (congrArg (fun L => L ∘ Fin.castLE (by decide : 248 ≤ 257)) hL)
    intro k hk
    apply hframe
    · intro he
      have hk93 : k = 93 := Fin.ext (congrArg (fun j : Fin 257 => j.val) he)
      subst k
      exact hk (by decide)
    · intro he
      have hk238 : k = 238 := Fin.ext (congrArg (fun j : Fin 257 => j.val) he)
      subst k
      exact hk (by decide)
  refine ⟨hcursor,?_,?_,?_,hc,hframe 116 (by decide) (by decide) |>.trans hcount,
    hframe 167 (by decide) (by decide) |>.trans hmask⟩
  · apply hfactor.of_runtime_frame H target columns
      (congrArg (fun L => L ∘ Fin.castLE (by decide : 242 ≤ 257)) hL)
    · intro k hk
      apply hframe
      · intro he; have hv : k.val = 93 := congrArg (fun j : Fin 257 => j.val) he; omega
      · intro he; have hv : k.val = 238 := congrArg (fun j : Fin 257 => j.val) he; omega
    · exact hframe 119 (by decide) (by decide)
    · intro k hk h238
      apply hframe
      · intro he; have hv : k.val = 93 := congrArg (fun j : Fin 257 => j.val) he; omega
      · intro he
        exact h238 (Fin.ext (congrArg (fun j : Fin 257 => j.val) he))
  · intro i
    rw [hL]
    exact hleft i
  · have hc' : ReplicaRecoveryCoreReady H (12*H.band+1)
        (embStk (Fin.castLE (by decide : 248 ≤ 255))
          (embStk (Fin.castLE (by decide : 255 ≤ 257)) F)) := hc
    apply ReplicaBoundaryRhsReady.of_recovery_core H (12*H.band+1) hphysical hc'
    intro k hk
    apply hframe
    · intro he; have hv : k.val = 93 := congrArg (fun j : Fin 257 => j.val) he; omega
    · intro he; have hv : k.val = 238 := congrArg (fun j : Fin 257 => j.val) he; omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
