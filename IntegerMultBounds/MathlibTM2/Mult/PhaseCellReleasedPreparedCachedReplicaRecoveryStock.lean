module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCachedBatchedReplicaRecoveryStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasedPreparedCachedReplicaRecovery
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedReplicaCouplingRelease
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

theorem placedReplicaCouplingRelease_native :
    mnNativePushBound 0 (placedReplicaCouplingRelease (P := P) (Q := Q) (A := A) (U := U)) := by
  exact embProg_native replicaRecoveryPreparationNativeReg Empty.elim _ (clearWords_native replicaCouplingNativePorts)

theorem releasedPreparedCachedReplicaRecovery_exec_within (H : ReplicaHaloProblem s) (target : ℕ)
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
    (hshared : ReplicaRecoverySharedBank H (12*H.band+1) (embStk replicaRecoveryPreparationNativeReg S))
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
      n ≤ releaseReplicaCouplingNativeCost (embStk replicaRecoveryPreparationNativeReg S)+(((4*(H.span*H.wordWidth)+4)+initializeReplicaBoundaryRhsCost H)+
        (copyRowsOrderedCost H.Fs.length (H.span*H.wordWidth)+4*(H.Fs.length*(H.span*H.wordWidth))+4))+
        initializedCachedBatchedReplicaRecoveryTime H (B.problem htarget) ∧
      List.Forall₂ (ReplicaRecoveryAssemblyOutput B Ds) (List.finRange H.Fs.length) outputs ∧
      G.R 257 = S.R (replicaRecoveryPreparationCallerWorkerReg 125) ∧ G.R 247 = buffers.accumulatorTail ∧
      G.R 391 = outputs.reverse.flatten ∧
      ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          preparedCachedBatchedReplicaRecoveryWorkspace H (B.problem htarget) hQ push c M R K)
        depth (releasedPreparedCachedReplicaRecovery hR hQ) (mk v S) n (mk v' G) ∧ (G.inp = buffers.input ∧ G.out = buffers.output) := by
  obtain ⟨v₁,J,hu₁,he₁,hfactorJ,hcoreJ,hL,hin,hout,hkeep,hoff,h116⟩ :=
    placedReplicaCouplingRelease_exec (body := body) H target columns v S hfactor hshared
  have hg (j : Fin 126) : J.R (replicaRecoveryBatchInterior.gather j) = S.R (replicaRecoveryBatchInterior.gather j) :=
    (hoff _ (fun i => replicaRecoveryPreparationCallerReg_gather_disjoint _ j)).2
  have hgather : embStk replicaRecoveryBatchInterior.gather J = embStk replicaRecoveryBatchInterior.gather S :=
    Stacks.ext hin hout (congrArg (fun L => L ∘ replicaRecoveryBatchInterior.gather) hL) (funext hg)
  have hheaders := headers.of_frame H replicaRecoveryBatchInterior.gather buffers S J hg
  have hperipheralJ : ReplicaRecoveryPeripheralReady H buffers {J with R := Function.update J.R 125 []} := by
    apply hperipheral.of_preparation_frame H buffers
    · refine Stacks.ext hin hout (congrArg (fun L => L ∘ Fin.castLE (by decide : 126 ≤ 392)) hL) ?_
      funext j
      change Function.update J.R 125 [] (Fin.castLE (by decide : 126 ≤ 392) j) = Function.update S.R 125 [] _
      by_cases hj : (Fin.castLE (by decide : 126 ≤ 392) j) = 125
      · simp only [hj,Function.update_self]
      · rw [Function.update_of_ne hj,Function.update_of_ne hj]
        exact hg j
    · intro k hk
      refine ⟨congrFun hL k,?_⟩
      change Function.update J.R 125 [] k = Function.update S.R 125 [] k
      by_cases h125 : k = 125
      · simp only [h125,Function.update_self]
      · rw [Function.update_of_ne h125,Function.update_of_ne h125]
        exact (hoff k (fun i => hk (Fin.castLE (by decide : 248 ≤ 258) i))).2
  have hhighOff (k : Fin 392) (hk : 389 ≤ k.val) : ∀ i, replicaRecoveryPreparationNativeReg i ≠ k := by
    intro i he
    have hold : replicaRecoveryPreparationNativeReg i = Fin.castLE (by decide : 389 ≤ 392)
        (replicaRecoveryCallerWorkerReg (Fin.castLE (by decide : 248 ≤ 255) i)) :=
      replicaRecoverySetupWorkerReg_eq (Fin.castLE (by decide : 248 ≤ 255) i) |>.symm
    have hv := congrArg Fin.val (hold.symm.trans he)
    have hi := (replicaRecoveryCallerWorkerReg (Fin.castLE (by decide : 248 ≤ 255) i)).isLt
    change (replicaRecoveryCallerWorkerReg (Fin.castLE (by decide : 248 ≤ 255) i)).val = k.val at hv
    omega
  have hblankJ : J.R 391 = [] := (hoff 391 (hhighOff 391 (by decide))).2.trans hblank
  have hblankSetupJ (i : Fin 255) (hi : 248 ≤ i.val) : J.R (replicaRecoverySetupWorkerReg i) = [] := by
    apply (hoff _ ?_).2.trans (hblankSetup i hi)
    intro j he
    have hh := replicaRecoveryPreparationCallerReg_injective
      (he.trans (replicaRecoveryPreparationCallerReg_worker i).symm)
    have hv := congrArg Fin.val hh
    have hj := j.isLt
    change j.val = i.val at hv
    omega
  have h248Off : ∀ i, replicaRecoveryPreparationNativeReg i ≠ 248 := by
    intro i he
    have hg := replicaRecoveryCallerReg_gap (Fin.castLE (by decide : 248 ≤ 259) i)
    have hold : replicaRecoveryPreparationNativeReg i = Fin.castLE (by decide : 389 ≤ 392)
        (replicaRecoveryCallerWorkerReg (Fin.castLE (by decide : 248 ≤ 255) i)) :=
      replicaRecoverySetupWorkerReg_eq (Fin.castLE (by decide : 248 ≤ 255) i) |>.symm
    have hv := congrArg Fin.val (hold.symm.trans he)
    change (replicaRecoveryCallerReg (Fin.castLE (by decide : 248 ≤ 259) i)).val = 248 at hv
    omega
  have h123 : J.R 123 = S.R 123 := hg 123
  obtain ⟨B,Ds,v',G,n,outputs,hlenD,hu₂,hn,hcert,h257,h247,h391,he₂,hstreams⟩ :=
    preparedCachedBatchedReplicaRecovery_exec_within (body := body) H target hR hQ hA hp hwidth hsep hpad htarget
      columns push c hpush M hpushM X hX R K hpushR hpushK buffers v₁ J hheaders hblankJ
      residuals hlen ((hg 125).trans harchive) hgood hfactorJ (by intro i; rw [hL]; exact hleftShared i)
      hcoreJ h116 ((hkeep 167 (Or.inl (by decide))).trans hmask) (by rw [h123]; exact hvolume) hblankSetupJ
      hperipheralJ ((hkeep 159 (Or.inl (by decide))).trans h159) ((hkeep 161 (Or.inl (by decide))).trans h161)
      (by rw [(hoff 390 (hhighOff 390 (by decide))).2]; exact hcount)
      (by intro i; rw [hL]; exact hleft i)
      ((hkeep 93 (Or.inr (Or.inl rfl))).trans h93) ((hkeep 110 (Or.inr (Or.inr rfl))).trans h110)
      ((hoff 248 h248Off).2.trans h248) depth
  refine ⟨B,Ds,v',G,releaseReplicaCouplingNativeCost (embStk replicaRecoveryPreparationNativeReg S)+n,outputs,
    hlenD,hu₂.trans hu₁,?_,hcert,h257.trans (hkeep 125 (Or.inl (by decide))),h247,h391,?_,hstreams⟩
  · have hc := Nat.add_le_add_left hn (releaseReplicaCouplingNativeCost (embStk replicaRecoveryPreparationNativeReg S))
    simpa only [Nat.add_assoc] using hc
  · have ht := mn_native_exec_within he₁ 0 placedReplicaCouplingRelease_native depth
      (mnSize (mk v S)+depth) (by omega)
    have hsize := ht.final
    refine .seq (ht.mono ?_) (he₂.mono ?_)
    all_goals intro d z hz; omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
