module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedReplicaRecoveryArchiveHandoff
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedReplicaRecoverySetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedReplicaBoundaryFactory

/-! Execute physical setup and archive installation before cached recovery. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 392 Q A U}

def preparedReplicaRecoveryArchives : Pr P 392 Q A U :=
  .seq placedReplicaRecoverySetup placedReplicaRecoveryArchiveHandoff

theorem preparedReplicaRecoveryArchives_exec (H : ReplicaHaloProblem s) (target : ℕ)
    (hA : 4 ≤ A) (X : ℕ → ZMod s → ℝ)
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
      Exec body preparedReplicaRecoveryArchives (mk v S) n (mk v' F) ∧
      ReplicaRecoveryPreparationReady H target X columns
        (S.R (replicaRecoveryPreparationCallerWorkerReg 238)) (S.R (replicaRecoveryPreparationCallerWorkerReg 93))
        (F.R (replicaRecoveryPreparationCallerWorkerReg 125)) (F.R (replicaRecoveryPreparationCallerWorkerReg 256))
        (embStk replicaRecoveryPreparationCallerWorkerReg F) ∧ F.R 390 = S.R 390 ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.R 125 = [] ∧
      (∀ k, k ≠ 125 → (∀ i, replicaRecoverySetupWorkerReg i ≠ k) → F.R k = S.R k) ∧
      (∀ k : Fin 248, k ≠ 93 → k ≠ 238 →
        F.R (replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide) k)) =
          S.R (replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide) k))) := by
  have hworker (Z : Stacks 392 A) : embStk replicaRecoverySetupWorkerReg Z =
      embStk (Fin.castLE (by decide : 255 ≤ 257)) (embStk replicaRecoveryPreparationCallerWorkerReg Z) := by
    change embStk replicaRecoverySetupWorkerReg Z =
      embStk (fun i => replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide : 255 ≤ 257) i)) Z
    congr 1
    funext i
    exact replicaRecoverySetupWorkerReg_eq i
  have hc : ReplicaRecoveryCoreReady H (12*H.band+1)
      (embStk (Fin.castLE (by decide : 248 ≤ 255)) (embStk replicaRecoverySetupWorkerReg S)) := by
    rw [hworker]
    exact hcore
  obtain ⟨v₁,G,n₁,hu₁,hn₁,he₁,hphysical,hcoreG,hnative,hgather,hL,hhigh,hsetupOff⟩ :=
    placedReplicaRecoverySetup_exec (body := body) H (12*H.band+1) hA v S hc hvolume hblankSetup
  simp only [hworker] at hphysical hcoreG hnative
  have hfactorG : ReplicaBoundaryFactorData H target columns (embStk replicaRecoveryBoundaryFactoryReg G) := by
    have hh := congrArg (embStk (Fin.castLE (by decide : 242 ≤ 248))) hnative
    change embStk replicaRecoveryBoundaryFactoryReg G = embStk replicaRecoveryBoundaryFactoryReg S at hh
    rw [hh]
    exact hfactor
  have hport (k : Fin 248) : G.R (replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide) k)) =
      S.R (replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide) k)) :=
    congrArg (fun Z : Stacks 248 A => Z.R k) hnative
  have hheaders := headers.of_frame H replicaRecoveryBatchInterior.gather buffers S G
    (fun k => congrArg (fun Z : Stacks 126 A => Z.R k) hgather)
  have harchiveG := (congrArg (fun Z : Stacks 126 A => Z.R 125) hgather).trans harchive
  obtain ⟨v',n₂,hu₂,hn₂,he₂,hready,hL₂,hi₂,ho₂,hframe⟩ := placedReplicaRecoveryArchiveHandoff_exec
    (body := body) H target X buffers v₁ G hheaders ((hhigh 391 (by decide)).2.trans hblank)
    Ds hlen harchiveG hgood columns hfactorG (by intro i; rw [hL]; exact hleft i)
    hphysical hcoreG ((hport 116).trans hcount) ((hport 167).trans hmask)
  have h238 : G.R (replicaRecoveryPreparationCallerWorkerReg 238) = S.R (replicaRecoveryPreparationCallerWorkerReg 238) := hport 238
  have h93 : G.R (replicaRecoveryPreparationCallerWorkerReg 93) = S.R (replicaRecoveryPreparationCallerWorkerReg 93) := hport 93
  refine ⟨v',_,n₁+n₂,hu₂.trans hu₁,by omega,Exec.seq he₁ he₂,?_,
    (hframe 390 (by decide) (by decide) (by decide)).trans (hhigh 390 (by decide)).2,hL₂.trans hL,
    hi₂.trans (congrArg (fun Z : Stacks 126 A => Z.inp) hgather),
    ho₂.trans (congrArg (fun Z : Stacks 126 A => Z.out) hgather),?_,?_,?_⟩
  · simpa only [h238,h93] using hready
  · simp only [Function.update_of_ne (by decide : (125 : Fin 392) ≠ replicaRecoveryPreparationCallerWorkerReg 238),
      replicaRecoveryBatchInterior_gather]
    change Function.update (β := fun _ : Fin 392 => List (Fin (A+4))) _ (125 : Fin 392) [] 125 = []
    simp only [Function.update_self]
  · intro k h125 hk
    have h93w : replicaRecoverySetupWorkerReg 93 = replicaRecoveryPreparationCallerWorkerReg 93 := replicaRecoverySetupWorkerReg_eq 93
    have h238w : replicaRecoverySetupWorkerReg 238 = replicaRecoveryPreparationCallerWorkerReg 238 := replicaRecoverySetupWorkerReg_eq 238
    exact (hframe k (fun he => hk 93 (h93w.trans he.symm))
      (fun he => hk 238 (h238w.trans he.symm)) h125).trans (hsetupOff k hk)

  · intro k hk93 hk238
    have hinj : Function.Injective replicaRecoveryPreparationCallerWorkerReg :=
      replicaRecoveryPreparationCallerReg_injective.comp (Fin.castLE_injective _)
    apply (hframe _ ?_ ?_ ?_).trans (hport k)
    · apply hinj.ne
      intro he
      exact hk93 (Fin.ext (congrArg (fun j : Fin 257 => j.val) he))
    · apply hinj.ne
      intro he
      exact hk238 (Fin.ext (congrArg (fun j : Fin 257 => j.val) he))
    · exact replicaRecoveryPreparationCallerReg_gather_disjoint _ 125

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
