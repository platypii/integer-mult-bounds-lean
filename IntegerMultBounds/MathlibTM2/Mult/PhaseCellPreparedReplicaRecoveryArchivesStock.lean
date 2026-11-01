module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaRecoveryArchives
public import IntegerMultBounds.MathlibTM2.Host.ClosedProgramStock
public import IntegerMultBounds.MathlibTM2.Host.NativePushBoundMono

/-! Physical boundary setup and archive installation use only native actions.
Their shared push bound turns the existing exact execution into a stock trace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 392 Q A U}

@[irreducible] noncomputable def preparedReplicaRecoveryArchivesPush : ℕ :=
  mnProgPush (replicaRecoveryCallerSetup (P := Empty) (Q := Q) (A := A) (U := U))+2

theorem preparedReplicaRecoveryArchives_native :
    mnNativePushBound (preparedReplicaRecoveryArchivesPush (Q := Q) (A := A) (U := U))
      (preparedReplicaRecoveryArchives (P := P) (Q := Q) (A := A) (U := U)) := by
  unfold preparedReplicaRecoveryArchivesPush
  constructor
  · apply mnNativePushBound_mono (Nat.le_add_right _ 2)
    exact embProg_native _ Empty.elim _ (WordCmd.empty_native (replicaRecoveryCallerSetup (P := Empty)))
  · apply mnNativePushBound_mono (Nat.le_add_left 2 _)
    simp [placedReplicaRecoveryArchiveHandoff,replicaRecoveryArchiveHandoff,prepareReplicaRecoveryRhs,
      copyRowsOrdered,restoringRowScan,scanP,popPush,copyPrefix,copyR,copyStep,transfer,transferAct,moveRightOrdered,
      scanR,drainR,popDo,keepIn,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

noncomputable def preparedReplicaRecoveryArchivesWorkspace (H : ReplicaHaloProblem s) : ℕ :=
  preparedReplicaRecoveryArchivesPush (Q := Q) (A := A) (U := U)*
    ((((4*(H.span*H.wordWidth)+4)+initializeReplicaBoundaryRhsCost H)+
      copyRowsOrderedCost H.Fs.length (H.span*H.wordWidth))+4*(H.Fs.length*(H.span*H.wordWidth))+4)

theorem preparedReplicaRecoveryArchives_exec_within (H : ReplicaHaloProblem s) (target : ℕ)
    (hA : 4 ≤ A) (X : ℕ → ZMod s → ℝ)
    (buffers : ReplicaLoopBuffers A) (v : HS 392 Q A U) (S : Stacks 392 A)
    (headers : ReplicaRecoveryRhsHeaders H replicaRecoveryBatchInterior.gather buffers S) (hblank : S.R 391 = [])
    (Ds : List (ZMod s → GaussianInt)) (hlen : Ds.length = H.Fs.length)
    (harchive : S.R (replicaRecoveryBatchInterior.gather 125) = Ds.flatMap
      (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D)))
    (hgood : ∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) (Ds[j.val]'j.isLt))
    (columns : List (ZMod s → GaussianInt))
    (hfactor : ReplicaBoundaryFactorData H target columns (embStk (Fin.castLE (by decide : 242 ≤ 257))
      (embStk replicaRecoveryPreparationCallerWorkerReg S)))
    (hleft : ∀ i : Fin 242, S.L (replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide : 242 ≤ 257) i)) =
      S.L (replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide : 255 ≤ 257) (replicaBoundaryPhaseReg i))))
    (hcore : ReplicaRecoveryCoreReady H (12*H.band+1) (embStk (Fin.castLE (by decide : 248 ≤ 257))
      (embStk replicaRecoveryPreparationCallerWorkerReg S)))
    (hcount : S.R (replicaRecoveryPreparationCallerWorkerReg 116) = [])
    (hmask : S.R (replicaRecoveryPreparationCallerWorkerReg 167) = [])
    (hvolume : (S.R 123).length = H.span*H.wordWidth)
    (hblankSetup : ∀ i : Fin 255, 248 ≤ i.val →
      S.R (replicaRecoverySetupWorkerReg i) = []) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ ((4*(H.span*H.wordWidth)+4)+initializeReplicaBoundaryRhsCost H)+
        (copyRowsOrderedCost H.Fs.length (H.span*H.wordWidth)+4*(H.Fs.length*(H.span*H.wordWidth))+4) ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          preparedReplicaRecoveryArchivesWorkspace (Q := Q) (A := A) (U := U) H)
        depth preparedReplicaRecoveryArchives (mk v S) n (mk v' F)) ∧
      ReplicaRecoveryPreparationReady H target X columns
        (S.R (replicaRecoveryPreparationCallerWorkerReg 238)) (S.R (replicaRecoveryPreparationCallerWorkerReg 93))
        (F.R (replicaRecoveryPreparationCallerWorkerReg 125)) (F.R (replicaRecoveryPreparationCallerWorkerReg 256))
        (embStk replicaRecoveryPreparationCallerWorkerReg F) ∧ F.R 390 = S.R 390 ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.R 125 = [] ∧
      (∀ k, k ≠ 125 → (∀ i, replicaRecoverySetupWorkerReg i ≠ k) → F.R k = S.R k) ∧
      (∀ k : Fin 248, k ≠ 93 → k ≠ 238 →
        F.R (replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide) k)) =
          S.R (replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide) k))) := by
  obtain ⟨v',F,n,hu,hn,hex,hrest⟩ := preparedReplicaRecoveryArchives_exec (body := body) H target hA X
    buffers v S headers hblank Ds hlen harchive hgood columns hfactor hleft hcore hcount hmask hvolume hblankSetup
  refine ⟨v',F,n,hu,hn,?_,hrest⟩
  intro depth
  have hbound : preparedReplicaRecoveryArchivesPush (Q := Q) (A := A) (U := U)*n ≤
      preparedReplicaRecoveryArchivesWorkspace (Q := Q) (A := A) (U := U) H := by
    simpa only [preparedReplicaRecoveryArchivesWorkspace,Nat.add_assoc] using
      Nat.mul_le_mul_left (preparedReplicaRecoveryArchivesPush (Q := Q) (A := A) (U := U)) hn
  exact mn_native_exec_within hex (preparedReplicaRecoveryArchivesPush (Q := Q) (A := A) (U := U))
    preparedReplicaRecoveryArchives_native depth _ (Nat.add_le_add_left hbound _)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
