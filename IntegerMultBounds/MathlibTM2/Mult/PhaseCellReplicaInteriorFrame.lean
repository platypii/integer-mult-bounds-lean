module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedReplicaHaloLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedGatheredReplicaFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingPlacement

/-! Structural footprints preserve arbitrary spectators through the complete
interior controller. Numerical implementations remain behind their embeddings. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type}

private theorem copyUnaryHeaders_avoids_right (tmp outside : Fin T) (rs : List (Fin T × Fin T))
    (htmp : tmp ≠ outside) (hports : ∀ r ∈ rs, r.1 ≠ outside ∧ r.2 ≠ outside) :
    programOn (fun k => k ≠ HK.rt outside) (copyUnaryHeaders (P := P) (Q := Q) (A := A) (U := U) tmp rs) := by
  induction rs with
  | nil => trivial
  | cons r rs ih =>
    refine ⟨?_,ih (fun p hp => hports p (by simp [hp]))⟩
    have hp := hports r (by simp)
    simp [ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,programOn,actionOn,hp,htmp]

private theorem reloadReplicaFactoryInput_avoids_right (plan : ReplicaInteriorPlacement T) (outside : Fin T)
    (hg : ∀ i, plan.gather i ≠ outside) (hs : ∀ i, plan.solver i ≠ outside) :
    programOn (fun k => k ≠ HK.rt outside) (reloadReplicaFactoryInput (P₀ := P) (Q := Q) (A := A) (U := U) plan) := by
  refine ⟨?_,?_⟩
  · apply copyUnaryHeaders_avoids_right _ outside _ (hg 7)
    intro r hr
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    exact ⟨hg _,hs _⟩
  · simp [reloadReplicaOriginPackets,repeatPrefix,unaryProduct,scanP,copyPrefix,copyR,copyStep,
      transfer,transferAct,ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,popPush,
      moveR,moveStep,whileR,peekR,uclear,programOn,actionOn,hg,hs]

private theorem accumulatingGatheredPublication_avoids_right (plan : ReplicaInteriorPlacement T)
    (dst outside : Fin T) (hg : ∀ i, plan.gather i ≠ outside) (hs : ∀ i, plan.solver i ≠ outside) (hd : dst ≠ outside) :
    programOn (fun k => k ≠ HK.rt outside) (accumulatingGatheredPublication (P := P) (Q := Q) (A := A) (U := U) plan dst) := by
  refine ⟨embProg_empty_avoids_right _ Empty.elim outside (fun i => hg (Fin.castLE (by decide) i)) _,?_,?_⟩
  · simp [retainedEncodedPublication,symbolEncodedPublication,symbolReplicaPublicationStep,countedLoop,countedLoopBody,
      scatterBatch,scatterLoopBody,scatterPacket,gatherRead,gatherReadStep,WordCmd.peekRp,copyR,copyStep,
      discardPrefix,transfer,transferAct,scanR,keepIn,moveR,moveStep,whileR,peekR,pushN,popPush,uclear,drainR,popDo,
      programOn,actionOn,hg,hs,hd]
  · simp [uclear,drainR,popDo,peekR,programOn,actionOn,hg]

private theorem conditionalGeneratedHaloReplicaClass_avoids_right (plan : ReplicaInteriorPlacement T)
    (dst outside : Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (hg : ∀ i, plan.gather i ≠ outside) (hs : ∀ i, plan.solver i ≠ outside) (hd : dst ≠ outside) :
    programOn (fun k => k ≠ HK.rt outside) (conditionalGeneratedHaloReplicaClass (P := P) (A := A) (U := U) plan dst hR hQ) := by
  simp only [conditionalGeneratedHaloReplicaClass,whenRightNonempty,repeatableGatheredReplicaClass,
    releasedAccumulatingGatheredReplica,generatedAccumulatingGatheredReplica,retireGatheredNumericalKey,programOn]
  refine ⟨embProg_empty_avoids_right _ Empty.elim outside (fun i => hg (Fin.castLE (by decide) i)) _,
    ⟨?_,⟨reloadReplicaFactoryInput_avoids_right plan outside hg hs,
      ⟨generatedGatheredReplicaInteriorBatch_avoids_right plan hR hQ outside hg hs,
        accumulatingGatheredPublication_avoids_right plan dst outside hg hs hd⟩,
      embProg_empty_avoids_right _ Empty.elim outside hs _⟩,True.intro⟩,?_⟩
  · simp [peekR,actionOn,hg]
  · simp [releaseGatheredOriginPages,releasePairedOriginPages,unaryProduct,scanP,discardPrefix,transfer,transferAct,
      ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,popPush,moveR,moveStep,whileR,peekR,uclear,programOn,actionOn,hg]

theorem initializedReplicaHaloLoop_avoids_right (plan : ReplicaInteriorPlacement T) (dst outside : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hg : ∀ i, plan.gather i ≠ outside)
    (hs : ∀ i, plan.solver i ≠ outside) (hd : dst ≠ outside) :
    programOn (fun k => k ≠ HK.rt outside) (initializedReplicaHaloLoop (P := P) (A := A) (U := U) plan dst hR hQ) := by
  simp only [initializedReplicaHaloLoop,placedHaloLengthKeys,runReplicaHaloLoop,generatedHaloReplicaKeyLoop,
    generatedHaloReplicaKeyStep,countedStep,processGeneratedHaloReplicaKey,programOn]
  refine ⟨?_,⟨⟨embProg_empty_avoids_right _ Empty.elim outside (fun i => hg (Fin.castLE (by decide) i)) _,?_⟩,?_,?_,⟨?_,?_,?_⟩,?_⟩⟩
  all_goals first
    | exact conditionalGeneratedHaloReplicaClass_avoids_right plan dst outside hR hQ hg hs hd
    | simp [initializeReplicaAccumulator,allocateZeroLine,replicaLengthKeyParser,takeUnaryKey,takeBinaryUnaryKey,
        takePrefix,toUnary,hornerIter,udbl,eachSym,unaryProduct,scanP,transfer,transferAct,
        ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,popPush,moveR,moveStep,whileR,peekR,uclear,programOn,actionOn,hg,hd]

theorem initializedReplicaHaloLoop_preserves_right {body : P → Pr P T Q A U}
    (plan : ReplicaInteriorPlacement T) (dst outside : Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (hg : ∀ i, plan.gather i ≠ outside) (hs : ∀ i, plan.solver i ≠ outside) (hd : dst ≠ outside)
    {v v' : HS T Q A U} {S F : Stacks T A} {n : ℕ}
    (hex : Exec body (initializedReplicaHaloLoop plan dst hR hQ) (mk v S) n (mk v' F)) :
    F.R outside = S.R outside :=
  hex.preserves_stack (HK.rt outside) (initializedReplicaHaloLoop_avoids_right plan dst outside hR hQ hg hs hd)

theorem ReplicaCouplingPlacement.interior_preserves_extended {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (dst : Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (hd : ∀ i, placement.bank i ≠ dst) (k : Fin 168) (hk : 117 ≤ k.val)
    {body : P → Pr P T Q A U} {v v' : HS T Q A U} {S F : Stacks T A} {n : ℕ}
    (hex : Exec body (initializedReplicaHaloLoop plan dst hR hQ) (Host.mk v S) n (Host.mk v' F)) :
    F.R (placement.bank k) = S.R (placement.bank k) := by
  apply initializedReplicaHaloLoop_preserves_right plan dst (placement.bank k) hR hQ
    (fun i => (placement.bank_gather_disjoint k i).symm) ?_ (hd k).symm hex
  intro i
  unfold ReplicaCouplingPlacement.bank
  rw [dif_neg (by omega : ¬k.val < 117)]
  exact (placement.extra_solver_disjoint _ i).symm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
