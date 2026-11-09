module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFirstCachedReplicaWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellActualResidualBatchWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicRecoveryWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaPassMasks
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicRecoverySchedule

/-! Instantiate the first-pass bound with the actual cyclic machine's programs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

noncomputable def cyclicReplicaRingPush (hR : rpStates ≤ Q) : ℕ :=
  mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
    Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR)

noncomputable def cyclicReplicaBatchPush (hQ : SS.states ≤ Q) : ℕ :=
  mnProgPush (cmulBlock cr (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
    mul mul_injective (by decide) hQ cr))

noncomputable def cyclicCachedReplicaTrafficFactor (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (ct ce : ℕ) : ℕ :=
  let cw := 16*20+8*ct+8*ce+128
  (76*cw+82)+40*cw*replicaHaloTrafficFactor (A := A) (U := U) hQ
    (cyclicReplicaRingPush (A := A) (U := U) hR) (2*cw+426009)

theorem selectedCachedReplicaPassWorkspace_le (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (ct ce : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)],
      ∀ H : ReplicaHaloProblem (Sizes.s n i), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) → H.u ≤ Sizes.p n →
      H.target ≤ ct*Sizes.p n → H.rhsExp ≤ ce*Sizes.p n →
      cachedReplicaPassWorkspace (A := A) (U := U) H hR hQ ≤
        4*Sizes.T n+cyclicCachedReplicaTrafficFactor (A := A) (U := U) hR hQ ct ce*
          H.Fs.length*H.t*H.p := by
  let push := actualBoundarySolvePushBounds (A := A) (U := U) hQ
  filter_upwards [selectedInitializedCachedReplicaInteriorWorkspace_le hQ push 0
    (cyclicRecoveryMulPush (A := A) (U := U) hQ)
    (cyclicReplicaRingPush (A := A) (U := U) hR)
    (cyclicReplicaBatchPush (A := A) (U := U) hQ) ct ce] with n hs
  intro h i _ H hp ht hl hu htarget hrhs
  simpa only [cachedReplicaPassWorkspace,cyclicRecoveryMulPush,cyclicReplicaRingPush,
    cyclicReplicaBatchPush,cyclicCachedReplicaTrafficFactor] using hs h i H hp ht hl hu htarget hrhs

theorem selectedCachedReplicaPassMasksWorkspace_le (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (ct ce : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)],
      ∀ H K : ReplicaHaloProblem (Sizes.s n i),
      (∀ D ∈ [H,K], D.p = Sizes.p n ∧ D.t = Sizes.t n i ∧
        D.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧ D.u ≤ Sizes.p n ∧
        D.target ≤ ct*Sizes.p n ∧ D.rhsExp ≤ ce*Sizes.p n) →
      cachedReplicaPassMasksWorkspace (A := A) (U := U) H K hR hQ ≤
        9*Sizes.T n+cyclicCachedReplicaTrafficFactor (A := A) (U := U) hR hQ ct ce*
          (H.Fs.length+K.Fs.length)*Sizes.t n i*Sizes.p n := by
  let cw := 16*20+8*ct+8*ce+128
  let cV := (2*cw+426009)*cw
  let maskPush := replicaBoundaryMaskPush (Q := Q) (A := A) (U := U)
  filter_upwards [selectedCachedReplicaPassWorkspace_le hR hQ ct ce,
    selectedAxisPolynomial_le_volume (maskPush*120024*(cV+5)^2) 4 6] with n hs hv
  intro h i _ H K hprofile
  have hH := hprofile H (by simp)
  have hK := hprofile K (by simp)
  have hpassH := hs h i H hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 hH.2.2.2.2.1 hH.2.2.2.2.2
  have hpassK := hs h i K hK.1 hK.2.1 hK.2.2.1 hK.2.2.2.1 hK.2.2.2.2.1 hK.2.2.2.2.2
  have hmeta (D : ReplicaHaloProblem (Sizes.s n i)) (hD : D ∈ [H,K]) :
      D.metadataWidth ≤ cV*Sizes.p n := by
    obtain ⟨hp,ht,hl,hu,htarget,hrhs⟩ := hprofile D hD
    obtain ⟨_,_,hw,hV⟩ := selectedHaloGatheredWidths ct ce h i D.u D.target D.rhsExp hu htarget hrhs
    have hwD : D.wordWidth ≤ cw*Sizes.p n := by
      simpa only [ReplicaHaloProblem.wordWidth,hp,ht,hl,cw] using hw
    have hVD : D.metadataWidth ≤ (2*cw+426009)*D.wordWidth := by
      simpa only [ReplicaHaloProblem.metadataWidth,ReplicaHaloProblem.precision,
        ReplicaHaloProblem.wordWidth,hp,ht,hl,cw] using hV
    exact hVD.trans (by dsimp only [cV]; nlinarith only [hwD])
  have ht : 1 ≤ Sizes.t n i := by have := h.good.lt i; omega
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hshared := solvedCyclicRecoverySharedTime_core_le H K cV (Sizes.t n i) (Sizes.p n)
    (h.good.lt i).le ht hp (hmeta H (by simp)) (hmeta K (by simp))
  have hscaled := Nat.mul_le_mul_left maskPush hshared
  have hvolume := hv i
  have hmaskTime : placedReplicaBoundaryMaskCost H+placedReplicaBoundaryMaskCost K ≤
      solvedCyclicRecoverySharedTime H K := by unfold solvedCyclicRecoverySharedTime; omega
  have hmask := Nat.mul_le_mul_left maskPush hmaskTime
  have hmaskBound : maskPush*(placedReplicaBoundaryMaskCost H+placedReplicaBoundaryMaskCost K) ≤ Sizes.T n := by
    nlinarith only [hmask,hscaled,hvolume]
  rw [hH.1,hH.2.1] at hpassH
  rw [hK.1,hK.2.1] at hpassK
  unfold cachedReplicaPassMasksWorkspace
  change _ ≤ 9*Sizes.T n+_
  change _ ≤ _ at hmaskBound
  nlinarith only [hpassH,hpassK,hmaskBound]

end IntegerMultBounds.MathlibTM2.Cost
