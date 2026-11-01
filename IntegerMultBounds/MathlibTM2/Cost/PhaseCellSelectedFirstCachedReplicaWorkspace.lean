module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFirstCachedReplicaWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCachedPreparationWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedReplicaInteriorSharedWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGatheredStock

/-! Selected first-pass space is shared core volume plus linear replica stock.
Coupling reuses recovery preparation's numerical scratch envelope. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedInitializedCachedReplicaInteriorWorkspace_le (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M R K ct ce : ℕ) :
    let cw := 16*20+8*ct+8*ce+128
    let cV := 2*cw+426009
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (H : ReplicaHaloProblem (Sizes.s n i)), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      H.u ≤ Sizes.p n → H.target ≤ ct*Sizes.p n → H.rhsExp ≤ ce*Sizes.p n →
      initializedCachedReplicaInteriorWorkspace (A := A) (U := U) H hQ R K M ≤
        4*Sizes.T n+((76*cw+82)+40*cw*replicaHaloTrafficFactor (A := A) (U := U) hQ R cV)*H.Fs.length*H.t*H.p := by
  dsimp only
  let cw := 16*20+8*ct+8*ce+128
  let cV := 2*cw+426009
  let cVp := cV*cw
  filter_upwards [selectedReleasedCachedCouplingWorkspace_shared_le (Q := Q) (A := A) (U := U) cw cVp,
    selectedCachedRecoveryPreparationWorkspace_volume_le hQ push c M cw cVp 1,
    selectedReplicaInteriorSharedWorkspace_volume_le (A := A) (U := U) hQ R K cV 20 cw 20 cVp 1,
    selectedAxisPolynomial_le_volume (48*cw+112) 1 1] with n hc hpw hi hs
  intro h i _ H hp ht hl hu htarget hrhs
  obtain ⟨hl',hr,hw,hV⟩ := selectedHaloGatheredWidths ct ce h i H.u H.target H.rhsExp hu htarget hrhs
  have hlH : H.l ≤ 20*H.p := by simpa only [hl,hp] using hl'
  have hrH : 2^H.l ≤ 20*H.p := by simpa only [hl,hp] using hr
  have hwH : H.wordWidth ≤ cw*H.p := by simpa only [ReplicaHaloProblem.wordWidth,hp,ht,hl,cw] using hw
  have hVw : H.metadataWidth ≤ cV*H.wordWidth := by
    simpa only [ReplicaHaloProblem.metadataWidth,ReplicaHaloProblem.precision,ReplicaHaloProblem.wordWidth,hp,ht,hl,cw,cV] using hV
  have hVp : H.metadataWidth ≤ cVp*H.p := by
    calc
      _ ≤ cV*(cw*H.p) := hVw.trans (Nat.mul_le_mul_left cV hwH)
      _ = cVp*H.p := by dsimp only [cVp]; ring
  have huH : H.u ≤ H.p := by simpa only [hp] using hu
  have hgap : H.t-Sizes.s n i ≤ Sizes.s n i := by rw [ht]; exact selectedAxis_gap_le_source h i
  have hring : H.l = haloInverseRingLog (Sizes.s n i) H.t := by rw [ht]; exact hl
  have ha := initializedCachedReplicaInteriorWorkspace_le_affine (A := A) (U := U) H hQ R K M cV hgap hring hVw
  have hshared := hi h i H hp ht huH hlH hwH hrH hVp
  have hcoupling := hc h i H M hp ht hwH huH hVp
  have hprep := hpw h i H hp ht hwH hVp
  have htransition := cachedReplicaCouplingTransitionWorkspace_le_preparation H hQ push c M
  have ht1 : 1 ≤ H.t := by have := H.s_lt_t; omega
  have hp1 : 1 ≤ H.p := H.p_pos
  have hspan : H.span ≤ H.t := by have := H.span_fit; have := H.s_lt_t; omega
  have hsw := Nat.mul_le_mul hspan hwH
  have hunit : 1 ≤ H.t*H.p := Nat.mul_pos ht1 hp1
  have hsmall : 48*(H.span*H.wordWidth)+112 ≤ Sizes.T n := by
    have hv : (48*cw+112)*H.t*H.p ≤ Sizes.T n := by simpa only [hp,ht,pow_one] using hs i
    nlinarith only [hv,hsw,hunit]
  have hrow : 76*(H.span*H.wordWidth)+82 ≤ (76*cw+82)*H.t*H.p := by nlinarith only [hsw,hunit]
  have hrows := Nat.mul_le_mul_left H.Fs.length hrow
  have htraffic := Nat.mul_le_mul_left
    (40*replicaHaloTrafficFactor (A := A) (U := U) hQ R cV*H.Fs.length*H.t) hwH
  simp only [one_mul] at hshared hprep
  change _ ≤ 4*Sizes.T n+((76*cw+82)+40*cw*replicaHaloTrafficFactor (A := A) (U := U) hQ R cV)*H.Fs.length*H.t*H.p
  nlinarith only [ha,hshared,hcoupling,hprep,htransition,hsmall,hrows,htraffic]

end IntegerMultBounds.MathlibTM2.Cost
