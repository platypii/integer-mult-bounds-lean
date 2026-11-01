module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedBatchedReplicaRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedInitializeRecoveryMasks

/-! Generate geometry masks once, prepare all recovery rows with retained factors,
then run the shared second interior pass and assemble its actual outputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 392 Q A U}

noncomputable def initializedCachedBatchedReplicaRecovery (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 392 Q A U :=
  .seq placedInitializeRecoveryMasks (cachedBatchedReplicaRecovery hR hQ)

def initializedCachedBatchedReplicaRecoveryTime (H J : ReplicaHaloProblem s) :=
  initializeRecoveryMasksCost H.metadataWidth H.span H.band+cachedBatchedReplicaRecoveryTime H J

noncomputable def initializedCachedBatchedReplicaRecoveryWorkspace (H J : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (push : BoundarySolvePushBounds (A := A) (U := U) hQ)
    (c M R K : ℕ) : ℕ :=
  initializeRecoveryMasksWorkspace (Q := Q) (A := A) (U := U) H+
    cachedBatchedReplicaRecoveryWorkspace H J hQ push c M R K

theorem initializedCachedBatchedReplicaRecovery_exec_within (H : ReplicaHaloProblem s) (target : ℕ)
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
    (buffers : ReplicaLoopBuffers A) (residualTail boundaryTail recoveryTail : List (Fin (A+4)))
    (v : HS 392 Q A U) (S : Stacks 392 A)
    (hready : ReplicaRecoveryPreparationReady H target X columns residualTail buffers.solverOutputTail boundaryTail recoveryTail
      (embStk replicaRecoveryPreparationCallerWorkerReg S))
    (h159 : S.R (recoveryMaskCallerReg 159) = [])
    (h161 : S.R (recoveryMaskCallerReg 161) = [])
    (hperipheral : ReplicaRecoveryPeripheralReady H buffers S)
    (hcount : (S.R 390).length = H.Fs.length)
    (hleft : ∀ i : Fin 117, S.L (replicaRecoveryPreparationCallerReg (Fin.castLE (by decide) i)) = [])
    (h110 : S.R (replicaRecoveryPreparationCallerReg 110) = buffers.rhsTail) (h248 : S.R 248 = []) (depth : ℕ) :
    ∃ B : ReplicaRecoveryBatch H target X, ∃ Ds : List (ZMod s → GaussianInt), ∃ v' G n outputs,
      Ds.length = H.Fs.length ∧ v'.user = v.user ∧ n ≤ initializedCachedBatchedReplicaRecoveryTime H (B.problem htarget) ∧
      List.Forall₂ (ReplicaRecoveryAssemblyOutput B Ds) (List.finRange H.Fs.length) outputs ∧
      G.R 257 = boundaryTail ∧ G.R 247 = buffers.accumulatorTail ∧
      G.R 391 = outputs.reverse.flatten++S.R 391 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        initializedCachedBatchedReplicaRecoveryWorkspace H (B.problem htarget) hQ push c M R K)
        depth (initializedCachedBatchedReplicaRecovery hR hQ) (mk v S) n (mk v' G) := by
  obtain ⟨v₀,n₀,hu₀,hn₀,he₀⟩ := placedInitializeRecoveryMasks_exec_within (body := body)
    H (12*H.band+1) v S hready.core h159 h161
  let J := initializedRecoveryMaskState H S
  have hreadyJ : ReplicaRecoveryPreparationReady H target X columns residualTail
      buffers.solverOutputTail boundaryTail recoveryTail (embStk replicaRecoveryPreparationCallerWorkerReg J) := by
    apply hready.of_mask_frame H target X columns residualTail buffers.solverOutputTail boundaryTail recoveryTail
      (F := embStk replicaRecoveryPreparationCallerWorkerReg J) rfl
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
    exact initializedRecoveryMaskState_worker_frame H S k hk.1 hk.2
  have hperipheralJ := hperipheral.of_preparation_frame H buffers
    (initializedRecoveryMaskState_gather H S) (initializedRecoveryMaskState_off H S)
  have hcountJ : (J.R 390).length = H.Fs.length := by
    rw [initializedRecoveryMaskState_frame H S 390 (by decide) (by decide)]
    exact hcount
  have h110J : J.R (replicaRecoveryPreparationCallerReg 110) = buffers.rhsTail :=
    (initializedRecoveryMaskState_worker_frame H S 110 (by decide) (by decide)).trans h110
  have h248J : J.R 248 = [] :=
    (initializedRecoveryMaskState_frame H S 248 (by decide) (by decide)).trans h248
  obtain ⟨B,Ds,v',G,n,outputs,hlen,hu,hn,hcert,hboundary,h247,h391,he⟩ :=
    cachedBatchedReplicaRecovery_exec_within (body := body) H target hR hQ hA hp hwidth hsep hpad
      htarget columns push c hpush M hpushM X hX R K hpushR hpushK buffers
      residualTail boundaryTail recoveryTail v₀ J hreadyJ (initializedRecoveryMaskState_ready H S)
      hperipheralJ hcountJ hleft h110J h248J depth
  refine ⟨B,Ds,v',G,n₀+n,outputs,hlen,hu.trans hu₀,?_,hcert,hboundary,h247,?_,?_⟩
  · exact Nat.add_le_add hn₀ hn
  · rw [initializedRecoveryMaskState_frame H S 391 (by decide) (by decide)] at h391
    exact h391
  · exact mn_seq_within_add
      (a := initializeRecoveryMasksWorkspace (Q := Q) (A := A) (U := U) H)
      (b := cachedBatchedReplicaRecoveryWorkspace H (B.problem htarget) hQ push c M R K)
      (he₀ depth) he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
