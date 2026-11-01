module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaRecoveryArchives
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaRecoveryPeripheral
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedCachedBatchedReplicaRecovery

/-! Physical setup, archive installation, cached recovery and final assembly
are one executed caller. Shared factors and the first-pass residuals are retained. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 392 Q A U}

noncomputable def preparedCachedBatchedReplicaRecovery (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 392 Q A U :=
  .seq preparedReplicaRecoveryArchives (initializedCachedBatchedReplicaRecovery hR hQ)

theorem preparedCachedBatchedReplicaRecovery_exec (H : ReplicaHaloProblem s) (target : ℕ)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hsep : H.span+H.band ≤ s) (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (columns : List (ZMod s → GaussianInt))
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c : ℕ)
    (hpush : mnNativePushBound c (replicaBoundaryRhs (P := Empty) (Q := Q) (A := A) (U := U)))
    (M : ℕ) (hpushM : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ M) (X : ℕ → ZMod s → ℝ)
    (hX : ∀ r < H.Fs.length, Solves (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) (X r)
      (fun i => (value H.precision (H.Fs.reverse.getD r (fun _ => 0) i)).re))
    (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock cr (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr)) ≤ K)
    (buffers : ReplicaLoopBuffers A) (v : HS 392 Q A U) (S : Stacks 392 A)
    (headers : ReplicaRecoveryRhsHeaders H replicaRecoveryBatchInterior.gather buffers S) (hblank : S.R 391 = [])
    (residuals : List (ZMod s → GaussianInt)) (hlen : residuals.length = H.Fs.length)
    (harchive : S.R (replicaRecoveryBatchInterior.gather 125) = residuals.flatMap
      (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D)))
    (hgood : ∀ j : Fin residuals.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) (residuals[j.val]'j.isLt))
    (hfactor : ReplicaBoundaryFactorData H target columns (embStk (Fin.castLE (by decide : 242 ≤ 257))
      (embStk replicaRecoveryPreparationCallerWorkerReg S)))
    (hleftShared : ∀ i : Fin 242, S.L (replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide : 242 ≤ 257) i)) =
      S.L (replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide : 255 ≤ 257) (replicaBoundaryPhaseReg i))))
    (hcore : ReplicaRecoveryCoreReady H (12*H.band+1) (embStk (Fin.castLE (by decide : 248 ≤ 257))
      (embStk replicaRecoveryPreparationCallerWorkerReg S)))
    (hcountEmpty : S.R (replicaRecoveryPreparationCallerWorkerReg 116) = [])
    (hmask : S.R (replicaRecoveryPreparationCallerWorkerReg 167) = [])
    (hvolume : (S.R 123).length = H.span*H.wordWidth)
    (hblankSetup : ∀ i : Fin 255, 248 ≤ i.val →
      S.R (replicaRecoverySetupWorkerReg i) = [])
    (hperipheral : ReplicaRecoveryPeripheralReady H buffers {S with R := Function.update S.R 125 []})
    (h159 : S.R (recoveryMaskCallerReg 159) = []) (h161 : S.R (recoveryMaskCallerReg 161) = [])
    (hcount : (S.R 390).length = H.Fs.length)
    (hleft : ∀ i : Fin 117, S.L (replicaRecoveryPreparationCallerReg (Fin.castLE (by decide : 117 ≤ 258) i)) = [])
    (h93 : S.R (replicaRecoveryPreparationCallerWorkerReg 93) = buffers.solverOutputTail)
    (h110 : S.R (replicaRecoveryPreparationCallerReg 110) = buffers.rhsTail) (h248 : S.R 248 = []) (depth : ℕ) :
    ∃ B : ReplicaRecoveryBatch H target X, ∃ Ds : List (ZMod s → GaussianInt), ∃ v' G n outputs,
      Ds.length = H.Fs.length ∧ v'.user = v.user ∧
      n ≤ (((4*(H.span*H.wordWidth)+4)+initializeReplicaBoundaryRhsCost H)+
        (copyRowsOrderedCost H.Fs.length (H.span*H.wordWidth)+4*(H.Fs.length*(H.span*H.wordWidth))+4))+
        initializedCachedBatchedReplicaRecoveryTime H (B.problem htarget) ∧
      List.Forall₂ (ReplicaRecoveryAssemblyOutput B Ds) (List.finRange H.Fs.length) outputs ∧
      G.R 257 = S.R (replicaRecoveryPreparationCallerWorkerReg 125) ∧ G.R 247 = buffers.accumulatorTail ∧
      G.R 391 = outputs.reverse.flatten ∧
      Exec body (preparedCachedBatchedReplicaRecovery hR hQ) (mk v S) n (mk v' G) ∧ (G.inp = buffers.input ∧ G.out = buffers.output) := by
  obtain ⟨v₁,J,n₁,hu₁,hn₁,he₁,hready,hcountJ,hL,hin,hout,h125,hframe,hnative⟩ :=
    preparedReplicaRecoveryArchives_exec (body := body) H target (by omega : 4 ≤ A) X buffers v S
      headers hblank residuals hlen harchive hgood columns hfactor hleftShared hcore hcountEmpty hmask hvolume hblankSetup
  have hperipheralJ := hperipheral.of_prepared_archives H buffers hL hin hout h125 hframe
  have hport (k : Fin 248) (hk93 : k ≠ 93) (hk238 : k ≠ 238) := hnative k hk93 hk238
  have h248Off : ∀ i, replicaRecoverySetupWorkerReg i ≠ 248 := by
    intro i he
    have hv := congrArg Fin.val he
    have hg := replicaRecoveryCallerReg_gap (Fin.castLE (by decide : 255 ≤ 259) i)
    change (replicaRecoveryCallerReg (Fin.castLE (by decide : 255 ≤ 259) i)).val = 248 at hv
    omega
  have h391Off : ∀ i, replicaRecoverySetupWorkerReg i ≠ 391 := by
    intro i he
    have hv := congrArg Fin.val he
    have hi := (replicaRecoveryCallerWorkerReg i).isLt
    change (replicaRecoveryCallerWorkerReg i).val = 391 at hv
    omega
  have h391J : J.R 391 = [] := (hframe 391 (by decide) h391Off).trans hblank
  have hreadyJ : ReplicaRecoveryPreparationReady H target X columns
      (S.R (replicaRecoveryPreparationCallerWorkerReg 238)) buffers.solverOutputTail
      (J.R (replicaRecoveryPreparationCallerWorkerReg 125)) (J.R (replicaRecoveryPreparationCallerWorkerReg 256))
      (embStk replicaRecoveryPreparationCallerWorkerReg J) := by simpa only [h93] using hready
  obtain ⟨B,Ds,v',G,n₂,outputs,hlenD,hu₂,hn₂,hcert,h257,h247,h391,he₂,hstreams⟩ :=
    initializedCachedBatchedReplicaRecovery_exec_within (body := body) H target hR hQ hA hp hwidth hsep hpad
      htarget columns push c hpush M hpushM X hX R K hpushR hpushK buffers _ _ _ v₁ J hreadyJ
      ((hport 159 (by decide) (by decide)).trans h159) ((hport 161 (by decide) (by decide)).trans h161)
      hperipheralJ (by rw [hcountJ]; exact hcount) (by intro i; rw [hL]; exact hleft i)
      ((hport 110 (by decide) (by decide)).trans h110)
      ((hframe 248 (by decide) h248Off).trans h248) depth
  refine ⟨B,Ds,v',G,n₁+n₂,outputs,hlenD,hu₂.trans hu₁,by omega,hcert,?_,h247,?_,Exec.seq he₁ he₂.toExec,hstreams⟩
  · exact h257.trans (hport 125 (by decide) (by decide))
  · simpa only [h391J,List.append_nil] using h391

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
