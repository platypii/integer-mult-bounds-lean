module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedReplicaRecoveryPreparationStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchedReplicaRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryReleasedBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedReplicaRecoveryFinish

/-! The amortized recovery caller: prepare all rows with retained factors,
run one shared second interior pass, and assemble its actual outputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 392 Q A U}

noncomputable def batchedReplicaRecoveryWorkspace (H J : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (push : BoundarySolvePushBounds (A := A) (U := U) hQ)
    (c M R K : ℕ) : ℕ :=
  replicaRecoveryPreparationRowWorkspace H hQ push c M+
    (replicaRecoveryInteriorWorkspace (A := A) (U := U) H J hQ R K+
      2*retainedPackedPublicationMergeCost H.span H.wordWidth)

theorem batchedReplicaRecovery_exec_within (H : ReplicaHaloProblem s) (target : ℕ)
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
    (hperipheral : ReplicaRecoveryPeripheralReady H buffers S)
    (hcount : (S.R 390).length = H.Fs.length)
    (hleft : ∀ i : Fin 117, S.L (replicaRecoveryPreparationCallerReg (Fin.castLE (by decide) i)) = [])
    (h110 : S.R (replicaRecoveryPreparationCallerReg 110) = buffers.rhsTail) (h248 : S.R 248 = []) (depth : ℕ) :
    ∃ B : ReplicaRecoveryBatch H target X, ∃ Ds : List (ZMod s → GaussianInt), ∃ v' G n outputs,
      Ds.length = H.Fs.length ∧ v'.user = v.user ∧ n ≤ batchedReplicaRecoveryTime H (B.problem htarget) ∧
      List.Forall₂ (ReplicaRecoveryAssemblyOutput B Ds) (List.finRange H.Fs.length) outputs ∧
      G.R 257 = boundaryTail ∧ G.R 247 = buffers.accumulatorTail ∧
      G.R 391 = outputs.reverse.flatten++S.R 391 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        batchedReplicaRecoveryWorkspace H (B.problem htarget) hQ push c M R K)
        depth (batchedReplicaRecovery hR hQ) (mk v S) n (mk v' G) := by
  obtain ⟨v₀,F,n₀,B,hu₀,hn₀,he₀,h390,hboundary,hsource,hgather,hinp,hout,
    hfactor,hcore,hphysical,h238,h93,h116,h167,hL,h110F,hstockF,hoff⟩ := placedReplicaRecoveryPreparation_exec_within
    (body := body) H target hQ hA hp hwidth hsep htarget columns push c hpush M hpushM X hX
      residualTail buffers.solverOutputTail boundaryTail recoveryTail v S hcount hready
  have hperipheralF := hperipheral.of_preparation_frame H buffers hgather hoff
  have hleftF (i : Fin 117) : F.L (replicaRecoveryPreparationCallerReg (Fin.castLE (by decide) i)) = [] := by
    exact (congrFun hL (Fin.castLE (by decide : 117 ≤ 257) i)).trans (hleft i)
  have hbank := replicaRecoveryPreparationCaller_released H (12*H.band+1) F hcore
    buffers.rhsTail buffers.solverOutputTail hleftF h93 (h110F.trans h110) h116
  have hmask : F.R 386 = couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin
      (H.origin+H.span) H.origin H.span := by
    have hh := hphysical.mask
    change F.R (replicaRecoveryPreparationCallerWorkerReg
      (Fin.castLE (by decide : 255 ≤ 257) (replicaBoundaryPhaseReg 167))) = _ at hh
    rw [replicaBoundaryPhaseReg_mask] at hh
    exact hh
  have hfresh : ∀ k ∈ ([390,299,248] : List (Fin 392)), F.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl
    · exact h390
    · exact h167
    · apply (hoff 248 (by
        intro i he
        have hv := congrArg (fun k : Fin 392 => k.val) he
        have hh := replicaRecoveryPreparationCallerReg_gap i
        change (replicaRecoveryPreparationCallerReg i).val = 248 at hv
        omega)).2.trans h248
  obtain ⟨vi,I,n₁,hu₁,hn₁,hfields,hgatherI,hspectator,he₁⟩ := placedReplicaRecoveryInterior_exec
    (body := body) H target X B htarget hR hQ hA hp hwidth hpad R K hpushR hpushK buffers recoveryTail
      v₀ F hperipheralF hsource hbank depth
  obtain ⟨Ds,v',G,m,outputs,hlen,hu,hm,hcert,hboundaryG,h247,h391,he⟩ := placedReplicaRecoveryFinish_exec
    (body := body) H target X B htarget hR hQ (by omega) buffers boundaryTail
      v₀ vi F I n₁ depth (replicaRecoveryInteriorWorkspace (A := A) (U := U) H (B.problem htarget) hQ R K)
      hperipheralF hboundary hmask hfresh hu₁ he₁ hfields hgatherI hspectator
  have h391F : F.R 391 = S.R 391 := (hoff 391 replicaRecoveryPreparationCallerReg_output_disjoint).2
  refine ⟨B,Ds,v',G,n₀+m,outputs,hlen,hu.trans hu₀,?_,hcert,hboundaryG,h247,
    h391.trans (congrArg (fun tail => outputs.reverse.flatten++tail) h391F),mn_seq_within_add (a := replicaRecoveryPreparationRowWorkspace H hQ push c M) (b := (replicaRecoveryInteriorWorkspace (A := A) (U := U) H (B.problem htarget) hQ R K+2*retainedPackedPublicationMergeCost H.span H.wordWidth)) (he₀ depth) he⟩
  unfold batchedReplicaRecoveryTime
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
