module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryArchiveHandoff
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryArchiveReady

/-! Concrete archive handoff in the common recovery caller. Register 391 is a
restored reversal buffer, so it remains available for final assembled output. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 392 Q A U}

private theorem worker_injective : Function.Injective replicaRecoveryPreparationCallerWorkerReg :=
  replicaRecoveryPreparationCallerReg_injective.comp (Fin.castLE_injective _)

private theorem gather_worker_disjoint (i : Fin 126) (j : Fin 257) :
    replicaRecoveryBatchInterior.gather i ≠ replicaRecoveryPreparationCallerWorkerReg j :=
  (replicaRecoveryPreparationCallerReg_gather_disjoint _ i).symm

def placedReplicaRecoveryArchiveHandoff : Pr P 392 Q A U :=
  replicaRecoveryArchiveHandoff replicaRecoveryBatchInterior replicaRecoveryPreparationCallerWorkerReg 391

theorem placedReplicaRecoveryArchiveHandoff_exec (H : ReplicaHaloProblem s) (target : ℕ)
    (X : ℕ → ZMod s → ℝ)
    (buffers : ReplicaLoopBuffers A) (v : HS 392 Q A U) (S : Stacks 392 A)
    (headers : ReplicaRecoveryRhsHeaders H replicaRecoveryBatchInterior.gather buffers S) (hblank : S.R 391 = [])
    (Ds : List (ZMod s → GaussianInt)) (hlen : Ds.length = H.Fs.length)
    (harchive : S.R (replicaRecoveryBatchInterior.gather 125) = Ds.flatMap
      (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D)))
    (hgood : ∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) Ds[j.val])
    (columns : List (ZMod s → GaussianInt))
    (hfactor : ReplicaBoundaryFactorData H target columns (embStk (Fin.castLE (by decide : 242 ≤ 257))
      (embStk replicaRecoveryPreparationCallerWorkerReg S)))
    (hleft : ∀ i : Fin 242, S.L (replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide : 242 ≤ 257) i)) =
      S.L (replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide : 255 ≤ 257) (replicaBoundaryPhaseReg i))))
    (hphysical : ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg
      (embStk (Fin.castLE (by decide : 255 ≤ 257)) (embStk replicaRecoveryPreparationCallerWorkerReg S))))
    (hcore : ReplicaRecoveryCoreReady H (12*H.band+1) (embStk (Fin.castLE (by decide : 248 ≤ 257))
      (embStk replicaRecoveryPreparationCallerWorkerReg S)))
    (hcount : S.R (replicaRecoveryPreparationCallerWorkerReg 116) = [])
    (hmask : S.R (replicaRecoveryPreparationCallerWorkerReg 167) = []) :
    let J := {S with R := Function.update S.R (replicaRecoveryPreparationCallerWorkerReg 93) (H.Fs.flatMap (fun C => cstream A H.wordWidth (packedInterval H.origin H.span C))++S.R (replicaRecoveryPreparationCallerWorkerReg 93))}
    let F := {J with R := Function.update (Function.update J.R (replicaRecoveryBatchInterior.gather 125) []) (replicaRecoveryPreparationCallerWorkerReg 238) (S.R (replicaRecoveryBatchInterior.gather 125)++S.R (replicaRecoveryPreparationCallerWorkerReg 238))}
    ∃ v' n, v'.user = v.user ∧
      n ≤ copyRowsOrderedCost H.Fs.length (H.span*H.wordWidth)+4*(H.Fs.length*(H.span*H.wordWidth))+4 ∧
      Exec body placedReplicaRecoveryArchiveHandoff (mk v S) n (mk v' F) ∧
      ReplicaRecoveryPreparationReady H target X columns (S.R (replicaRecoveryPreparationCallerWorkerReg 238)) (S.R (replicaRecoveryPreparationCallerWorkerReg 93))
        (F.R (replicaRecoveryPreparationCallerWorkerReg 125)) (F.R (replicaRecoveryPreparationCallerWorkerReg 256)) (embStk replicaRecoveryPreparationCallerWorkerReg F) ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, k ≠ replicaRecoveryPreparationCallerWorkerReg 93 → k ≠ replicaRecoveryPreparationCallerWorkerReg 238 → k ≠ replicaRecoveryBatchInterior.gather 125 → F.R k = S.R k) := by
  obtain ⟨v',n,hu,hn,he,hcursor,hL,hi,ho,hframe⟩ := replicaRecoveryArchiveHandoff_exec (body := body) H target X replicaRecoveryBatchInterior
    replicaRecoveryPreparationCallerWorkerReg worker_injective 391
    (fun k => gather_worker_disjoint k 93) (fun k => gather_worker_disjoint k 238)
    (fun k => by change (Fin.castLE (by decide : 126 ≤ 392) k) ≠ 391; intro he; have hv := congrArg Fin.val he; have hk := k.isLt; change k.val = 391 at hv; omega)
    (replicaRecoveryPreparationCallerReg_output_disjoint _) buffers v S headers hblank Ds hlen harchive hgood

  refine ⟨v',n,hu,hn,he,?_,hL,hi,ho,hframe⟩
  apply replicaRecoveryPreparationReady_of_archive_frame H target X columns _ _ _ _ hcursor
    hfactor hleft hphysical hcore hcount hmask (congrArg (fun L => L ∘ replicaRecoveryPreparationCallerWorkerReg) hL)
  intro k h93 h238
  exact hframe _ (worker_injective.ne h93) (worker_injective.ne h238) (gather_worker_disjoint 125 k).symm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
