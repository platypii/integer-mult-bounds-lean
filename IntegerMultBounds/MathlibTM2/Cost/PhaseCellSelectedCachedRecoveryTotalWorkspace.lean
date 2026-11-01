module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCachedRecoveryWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCachedPreparationWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedReplicaInteriorSharedWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryMaskInitialization

/-! Complete selected recovery space: shared volume plus linear replica payload. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedInitializedCachedRecoveryWorkspace_total_le (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M R K ct ce : ℕ)
    :
    let cw := 16*20+8*ct+8*ce+128
    let cV := 2*cw+426009
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (H : ReplicaHaloProblem (Sizes.s n i)), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      H.u ≤ Sizes.p n → H.target ≤ ct*Sizes.p n → H.rhsExp ≤ ce*Sizes.p n →
      ∀ (target : ℕ) (X : ℕ → ZMod (Sizes.s n i) → ℝ) (B : ReplicaRecoveryBatch H target X)
        htargetRecovery,
      initializedCachedBatchedReplicaRecoveryWorkspace H (B.problem htargetRecovery) hQ push c M R K ≤
        4*Sizes.T n+
          (cw*(150+40*replicaHaloTrafficFactor (A := A) (U := U) hQ R cV))*H.Fs.length*H.t*H.p := by
  dsimp only
  let cw := 16*20+8*ct+8*ce+128
  let cV := 2*cw+426009
  let cVp := cV*cw
  let cInit := mnProgPush (initializeRecoveryMasks (P := Empty) (Q := Q) (A := A) (U := U))
  filter_upwards [selectedInitializeRecoveryMasksCost_volume_le cVp cInit,
    selectedCachedRecoveryPreparationWorkspace_volume_le hQ push c M cw cVp 1,
    selectedReplicaInteriorSharedWorkspace_volume_le (A := A) (U := U) hQ R K cV 20 cw 20 cVp 1,
    selectedAxisPolynomial_le_volume (24*cw+134) 1 1] with n hm hprep hi hmerge
  intro h i _ H hp ht hl hu htarget hrhs target X B htargetRecovery
  have ha := selectedInitializedCachedRecoveryWorkspace_le_affine hQ push c M R K ct ce h i
    H hp ht hl hu htarget hrhs target X B htargetRecovery
  obtain ⟨_,_,hw,hV⟩ := selectedHaloGatheredWidths ct ce h i H.u H.target H.rhsExp hu htarget hrhs
  have hwH : H.wordWidth ≤ cw*H.p := by
    simpa only [ReplicaHaloProblem.wordWidth,hp,ht,hl,cw] using hw
  have hVw : H.metadataWidth ≤ cV*H.wordWidth := by
    simpa only [ReplicaHaloProblem.metadataWidth,ReplicaHaloProblem.precision,
      ReplicaHaloProblem.wordWidth,hp,ht,hl,cw,cV] using hV
  have hVp : H.metadataWidth ≤ cVp*H.p := by
    calc
      _ ≤ cV*(cw*H.p) := hVw.trans (Nat.mul_le_mul_left cV hwH)
      _ = cVp*H.p := by dsimp only [cVp]; ring
  have hspan : H.span ≤ H.t := by have := H.span_fit; have := H.s_lt_t; omega
  have hband : H.band ≤ H.t := H.band_fit.trans H.s_lt_t.le
  have hmask := hm h i H.metadataWidth H.span H.band (by simpa only [ht] using hspan)
    (by simpa only [ht] using hband) (by simpa only [hp] using hVp)
  have hmask' : initializeRecoveryMasksWorkspace (Q := Q) (A := A) (U := U) H ≤ Sizes.T n := hmask
  have hprep' := hprep h i H hp ht hwH hVp
  obtain ⟨_,_,hwJ,hVJ⟩ := B.problem_sizing htargetRecovery
  obtain ⟨hlSize,hrSize,_,_⟩ := selectedHaloGatheredWidths ct ce h i H.u H.target H.rhsExp hu htarget hrhs
  have hlH : H.l ≤ 20*H.p := by simpa only [hl,hp] using hlSize
  have hrH : 2^H.l ≤ 20*H.p := by simpa only [hl,hp] using hrSize
  have hi' := hi h i (B.problem htargetRecovery) hp ht (by change H.u ≤ H.p; simpa only [hp] using hu)
    hlH (hwJ.trans_le hwH) hrH (hVJ.trans_le hVp)
  have htpos : 1 ≤ H.t := by have := H.s_lt_t; omega
  have hppos := H.p_pos
  have hsw := Nat.mul_le_mul hspan hwH
  have hN : H.span ≤ H.t*H.p := hspan.trans (Nat.le_mul_of_pos_right _ hppos)
  have hunit : 1 ≤ H.t*H.p := Nat.mul_pos htpos hppos
  have hmerge' : 2*retainedPackedPublicationMergeCost H.span H.wordWidth+56 ≤ Sizes.T n := by
    have hv : (24*cw+134)*H.t*H.p ≤ Sizes.T n := by simpa only [hp,ht,pow_one] using hmerge i
    apply le_trans (b := (24*cw+134)*H.t*H.p) ?_ hv
    unfold retainedPackedPublicationMergeCost
    nlinarith only [hsw,hN,hunit]
  simp only [one_mul] at hprep' hi'
  unfold cachedRecoverySharedWorkspace at ha
  change _ ≤ 4*Sizes.T n+(cw*(150+40*replicaHaloTrafficFactor (A := A) (U := U) hQ R cV))*H.Fs.length*H.t*H.p
  change initializedCachedBatchedReplicaRecoveryWorkspace H (B.problem htargetRecovery) hQ push c M R K ≤
    initializeRecoveryMasksWorkspace (Q := Q) (A := A) (U := U) H+
      cachedReplicaRecoveryPreparationRowWorkspace H hQ push c M+
      replicaInteriorSharedWorkspace (A := A) (U := U) (B.problem htargetRecovery) hQ R K cV+
      2*retainedPackedPublicationMergeCost H.span H.wordWidth+56+
      (cw*(150+40*replicaHaloTrafficFactor (A := A) (U := U) hQ R cV))*H.Fs.length*H.t*H.p at ha
  linarith only [ha,hmask',hprep',hi',hmerge']

end IntegerMultBounds.MathlibTM2.Cost
