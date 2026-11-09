module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicRecoveryWorkspace

/-! Shared cyclic recovery fits selected volume; all row copies remain linear. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s Q A : ℕ} [NeZero s] {U : Type}

private theorem boundaryMask_le_initialization (H : ReplicaHaloProblem s) :
    placedReplicaBoundaryMaskCost H ≤ initializeRecoveryMasksCost H.metadataWidth H.span H.band := by
  unfold placedReplicaBoundaryMaskCost initializeRecoveryMasksCost
  nlinarith only [Nat.zero_le (H.span*tblC H.metadataWidth 1),Nat.zero_le (H.band*tblC H.metadataWidth 1)]

theorem solvedCyclicRecoverySharedWorkspace_le_components (H K : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (N n w : ℕ) :
    solvedCyclicRecoverySharedWorkspace (A := A) (U := U) H K N n w hQ ≤
      (replicaBoundaryMaskPush (Q := Q) (A := A) (U := U)+
        mnProgPush (initializeCouplingMasks true (P := Empty) (Q := Q) (A := A) (U := U)))*
        (initializeRecoveryMasksCost H.metadataWidth H.span H.band+
          initializeRecoveryMasksCost K.metadataWidth K.span K.band)+
      (cachedRecoveryCouplingWorkspace (A := A) (U := U) H hQ+
        cachedRecoveryCouplingWorkspace (A := A) (U := U) K hQ)+
      (24*(H.span*H.wordWidth)+24*(K.span*K.wordWidth)+4*nativeCyclicBoundaryRowCost N n w+88) := by
  have hm := Nat.mul_le_mul_left (replicaBoundaryMaskPush (Q := Q) (A := A) (U := U))
    (Nat.add_le_add (boundaryMask_le_initialization H) (boundaryMask_le_initialization K))
  have hmax : max (nativeCyclicBoundaryBatchWorkspace 0 N n w)
      (cyclicRecoveryPreparationSharedWorkspace (A := A) (U := U) H K hQ) ≤
      nativeCyclicBoundaryBatchWorkspace 0 N n w+
        cyclicRecoveryPreparationSharedWorkspace (A := A) (U := U) H K hQ :=
    max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  have hsum := Nat.add_le_add hm hmax
  apply hsum.trans_eq
  unfold cyclicRecoveryPreparationSharedWorkspace cyclicRecoveryCouplingPieceWorkspace
    nativeCyclicBoundaryBatchWorkspace
  ring

theorem selectedSolvedCyclicRecoveryWorkspace_le (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (cw cV : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
      ∀ (H K : ReplicaHaloProblem (Sizes.s m i)) (replicas N n w : ℕ),
      H.p = Sizes.p m → K.p = Sizes.p m → H.t = Sizes.t m i → K.t = Sizes.t m i →
      H.wordWidth ≤ cw*H.p → K.wordWidth ≤ cw*K.p →
      H.metadataWidth ≤ cV*H.p → K.metadataWidth ≤ cV*K.p →
      H.Fs.length = replicas → K.Fs.length = replicas →
      N ≤ Sizes.s m i → n ≤ Sizes.s m i → w ≤ cw*Sizes.p m →
      solvedCyclicRecoveryWorkspace (A := A) (U := U) H K replicas N n w hQ ≤
        (65*cw+84)*replicas*Sizes.t m i*Sizes.p m+5*Sizes.T m := by
  let maskPush := replicaBoundaryMaskPush (Q := Q) (A := A) (U := U)
  let initPush := mnProgPush (initializeCouplingMasks true (P := Empty) (Q := Q) (A := A) (U := U))
  filter_upwards [selectedInitializeRecoveryMasksCost_volume_le cV (maskPush+initPush),
    selectedCachedRecoveryCouplingWorkspace_le hQ push cw cV 1,
    selectedAxisPolynomial_le_volume (5000*(cw+1)) 1 1] with m hm hc hv
  intro h i _ H K replicas N n w hpH hpK htH htK hwH hwK hVH hVK hcountH hcountK hN hn hw
  have hst := (h.good.lt i).le
  have ht : 1 ≤ Sizes.t m i := by have := h.good.lt i; omega
  have hp : 1 ≤ Sizes.p m := by have := h.thirteen_le_p; omega
  have hHN : H.span ≤ Sizes.t m i := by have := H.span_fit; omega
  have hKN : K.span ≤ Sizes.t m i := by have := K.span_fit; omega
  have hbH : H.band ≤ Sizes.t m i := H.band_fit.trans hst
  have hbK : K.band ≤ Sizes.t m i := K.band_fit.trans hst
  have hiH := hm h i H.metadataWidth H.span H.band hHN hbH (by simpa only [hpH] using hVH)
  have hiK := hm h i K.metadataWidth K.span K.band hKN hbK (by simpa only [hpK] using hVK)
  have hcH := hc h i H hpH htH hwH hVH
  have hcK := hc h i K hpK htK hwK hVK
  simp only [one_mul] at hcH hcK
  have hvolH := Nat.mul_le_mul hHN (show H.wordWidth ≤ cw*Sizes.p m by simpa only [hpH] using hwH)
  have hvolK := Nat.mul_le_mul hKN (show K.wordWidth ≤ cw*Sizes.p m by simpa only [hpK] using hwK)
  have hvol := Nat.mul_le_mul (hn.trans hst) hw
  have hone : 1 ≤ Sizes.t m i*Sizes.p m := Nat.mul_pos ht hp
  have hrows : N+n+1 ≤ 3*Sizes.t m i := by omega
  have hwidth : w+1 ≤ (cw+1)*Sizes.p m := by nlinarith only [hw,hp]
  have hrow := nativeCyclicBoundaryRow_workspace_le N n w
  have hrowScale := Nat.mul_le_mul_left 1000 (Nat.mul_le_mul hrows hwidth)
  have hvolume := hv i
  simp only [pow_one] at hvolume
  have hroute : 24*(H.span*H.wordWidth)+24*(K.span*K.wordWidth)+
      4*nativeCyclicBoundaryRowCost N n w+88 ≤ Sizes.T m := by
    nlinarith only [hvolH,hvolK,hrow,hrowScale,hvolume,hone]
  have hshared := solvedCyclicRecoverySharedWorkspace_le_components (A := A) (U := U) H K hQ N n w
  have hsharedBound : solvedCyclicRecoverySharedWorkspace (A := A) (U := U) H K N n w hQ ≤ 5*Sizes.T m := by
    change (maskPush+initPush)*_ ≤ _ at hiH hiK
    change _ ≤ (maskPush+initPush)*_+_+_ at hshared
    nlinarith only [hshared,hiH,hiK,hcH,hcK,hroute]
  have hlinear : n*w+32*(H.span*H.wordWidth)+32*(K.span*K.wordWidth)+84 ≤
      (65*cw+84)*Sizes.t m i*Sizes.p m := by
    nlinarith only [hvol,hvolH,hvolK,hone]
  have hbatch := solvedCyclicRecoveryWorkspace_le_shared_add (A := A) (U := U) H K hQ replicas N n w hcountH hcountK
  have hlinearBatch := Nat.mul_le_mul_left replicas hlinear
  nlinarith only [hbatch,hsharedBound,hlinearBatch]

end IntegerMultBounds.MathlibTM2.Cost
