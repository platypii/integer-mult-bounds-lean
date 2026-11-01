module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFirstCachedReplicaPass
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedCouplingCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedSetupPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryMaskInitialization
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCouplingSetup

/-! The actual cached first-pass shared setup is paid once per core.
Its polynomial envelope includes headers, coefficients, masks and retirement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem cachedReplicaCouplingSharedTime_poly {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) {Z : ℕ}
    (hZ : 1 ≤ Z) (ht : H.t ≤ Z) (hP : 2^15*H.p ≤ Z) (hq : H.precision ≤ Z)
    (hw : H.wordWidth ≤ Z) (hu : H.u ≤ Z) (hV : H.metadataWidth ≤ Z)
    (hlift : liftedCoefficientWidth (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band ≤ Z) :
    cachedReplicaCouplingSharedTime H ≤ 20000000*Z^5 := by
  have hs : s ≤ Z := H.s_lt_t.le.trans ht
  have hb : H.band ≤ Z := H.band_fit.trans hs
  have ha : H.origin ≤ Z := (Nat.le_add_right _ H.span).trans (H.span_fit.trans hs)
  have hab : H.origin+H.span ≤ Z := H.span_fit.trans hs
  have hN : H.span ≤ Z := (Nat.le_add_left H.span H.origin).trans hab
  have ht1 : 1 ≤ H.t := by have := H.s_lt_t; omega
  have hw1 : 1 ≤ H.wordWidth := by unfold ReplicaHaloProblem.wordWidth executionWidth; omega
  have h₂ : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
  have h₃ : Z ≤ Z^3 := Nat.le_self_pow (by decide) Z
  have h₅ : Z ≤ Z^5 := Nat.le_self_pow (by decide) Z
  have h₂₅ : Z^2 ≤ Z^5 := Nat.pow_le_pow_right hZ (by decide)
  have h₃₅ : Z^3 ≤ Z^5 := Nat.pow_le_pow_right hZ (by decide)
  have hheader : replicaCouplingHeaderCost (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span) ≤ 73*Z := by
    unfold replicaCouplingHeaderCost
    omega
  have hgeom : prepareReplicaCouplingGeometryCost H.metadataWidth s H.t H.band H.origin (H.origin+H.span) ≤ 1000*Z^2 := by
    have hprod := Nat.mul_le_mul (show s+H.t+H.band+2*H.origin+2*(H.origin+H.span) ≤ 7*Z by omega)
      (show 4*H.metadataWidth+10 ≤ 4*Z+10 by omega)
    unfold prepareReplicaCouplingGeometryCost generateCouplingGeometryCost
    nlinarith only [hprod,hV,h₂,hZ]
  have hpage := sharedCouplingCoefficientIntervalCost_poly ht1 hZ H.s_lt_t.le
    (show H.origin ≤ s by have := H.span_fit; omega) H.span_fit hP hq hw hu hb hV hlift
  have hpage' : sharedCouplingCoefficientIntervalCost (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
      H.origin (H.origin+H.span) H.metadataWidth ≤ 10000000*Z^5 := by
    calc
      _ ≤ 10000000*H.t*Z^4 := hpage
      _ ≤ 10000000*Z*Z^4 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ht)
      _ = _ := by ring
  have hcounter := scalarPrepareCost_arg_le hq hw hw1
  have hcounter' : replicaCouplingCountersCost H.precision H.wordWidth H.band ≤ 20040*Z^3 := by
    unfold replicaCouplingCountersCost
    nlinarith only [hcounter,hq,hb,hZ,h₃]
  have hmask := initializeRecoveryMasksCost_le H.metadataWidth H.span H.band
  have hmask' : initializeRecoveryMasksCost H.metadataWidth H.span H.band ≤ 1080000*Z^3 := by
    calc
      _ ≤ 10000*(H.span+H.band+1)*(H.metadataWidth+5)^2 := hmask
      _ ≤ 10000*(3*Z)*(6*Z)^2 := by gcongr <;> omega
      _ = _ := by ring
  have hretire : 4*(H.span+H.band)+4 ≤ 12*Z := by omega
  unfold cachedReplicaCouplingSharedTime initializeCachedReplicaCouplingRuntimeCost
  have hN' : H.origin+H.span-H.origin = H.span := Nat.add_sub_cancel_left _ _
  rw [hN']
  nlinarith only [hheader,hgeom,hpage',hcounter',hmask',hretire,h₅,h₂₅,h₃₅]

private theorem linear_le_axis_precision {c C t p : ℕ} (hc : c ≤ C) (ht : 1 ≤ t) :
    c*p ≤ C*t*p := by
  calc
    c*p ≤ C*p := Nat.mul_le_mul_right p hc
    _ ≤ C*(t*p) := Nat.mul_le_mul_left C (Nat.le_mul_of_pos_left p ht)
    _ = C*t*p := (Nat.mul_assoc C t p).symm

private theorem replica_precision_le_width {s : ℕ} (H : ReplicaHaloProblem s) : H.precision ≤ H.wordWidth := by
  unfold ReplicaHaloProblem.precision ReplicaHaloProblem.wordWidth executionPrecision executionWidth
  omega

private theorem selectedReplicaLiftedWidth_le (cw : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (H : ReplicaHaloProblem (Sizes.s n i))
    (hp : H.p = Sizes.p n) (ht : H.t = Sizes.t n i) (hw : H.wordWidth ≤ cw*H.p) (hu : H.u ≤ H.p) :
    liftedCoefficientWidth (2^15*H.p) H.precision H.wordWidth (Sizes.s n i) H.t H.u H.band ≤ (2*cw+426064)*H.p := by
  have hh := selectedLiftedCoefficientWidth_le cw h i H.precision H.wordWidth H.u H.band
    (by simpa only [hp] using hw) (replica_precision_le_width H) (by simpa only [hp] using hu) H.band_fit
  simpa only [← hp,← ht] using hh

private theorem coupling_envelope_coefficients (cw cV : ℕ) :
    let C := 2*cw+cV+500000
    1 ≤ C ∧ cw ≤ C ∧ cV ≤ C ∧ 2^15 ≤ C ∧ 2*cw+426064 ≤ C := by
  dsimp only
  rw [show (2 : ℕ)^15 = 32768 by norm_num]
  omega

theorem selectedCachedReplicaCouplingSharedTime_poly_le (cw cV : ℕ) {n : ℕ}
    (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
    (H : ReplicaHaloProblem (Sizes.s n i)) (hp : H.p = Sizes.p n) (ht : H.t = Sizes.t n i)
    (hw : H.wordWidth ≤ cw*H.p) (hu : H.u ≤ H.p) (hV : H.metadataWidth ≤ cV*H.p) :
    cachedReplicaCouplingSharedTime H ≤ 20000000*((2*cw+cV+500000)*H.t*H.p)^5 := by
  let C := 2*cw+cV+500000
  let Z := C*H.t*H.p
  have ht1 : 1 ≤ H.t := by have := H.s_lt_t; omega
  have hp1 : 1 ≤ H.p := H.p_pos
  have hlinear (c : ℕ) (hc : c ≤ C) : c*H.p ≤ Z := linear_le_axis_precision hc ht1
  obtain ⟨hCZ,hcw,hcV,hCP,hClift⟩ := coupling_envelope_coefficients cw cV
  have hpZ : H.p ≤ Z := by simpa only [one_mul] using hlinear 1 hCZ
  have hZ : 1 ≤ Z := hp1.trans hpZ
  have htZ : H.t ≤ Z :=
    (Nat.le_mul_of_pos_left H.t hCZ).trans (Nat.le_mul_of_pos_right (C*H.t) hp1)
  have hwZ := hw.trans (hlinear cw hcw)
  have hq := replica_precision_le_width H
  have hlift := selectedReplicaLiftedWidth_le cw h i H hp ht hw hu
  have hliftZ := hlift.trans (hlinear (2*cw+426064) hClift)
  have hc := cachedReplicaCouplingSharedTime_poly H hZ htZ
    (hlinear (2^15) hCP) (hq.trans hwZ) hwZ (hu.trans hpZ)
    (hV.trans (hlinear cV hcV)) hliftZ
  exact hc

theorem selectedCachedReplicaCouplingSharedTime_volume_le (cw cV scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)],
      ∀ H : ReplicaHaloProblem (Sizes.s n i), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.wordWidth ≤ cw*H.p → H.u ≤ H.p → H.metadataWidth ≤ cV*H.p →
      scale*cachedReplicaCouplingSharedTime H ≤ Sizes.T n := by
  let C := 2*cw+cV+500000
  filter_upwards [selectedAxisPolynomial_le_volume (scale*20000000*C^5) 5 5] with n hn
  intro h i _ H hp ht hw hu hV
  have hc := selectedCachedReplicaCouplingSharedTime_poly_le cw cV h i H hp ht hw hu hV
  have heq (a b c d e : ℕ) : a*(b*(c*d*e)^5) = (a*b*c^5)*d^5*e^5 := by ring
  calc
    scale*cachedReplicaCouplingSharedTime H ≤ scale*(20000000*(C*H.t*H.p)^5) := Nat.mul_le_mul_left scale hc
    _ = (scale*20000000*C^5)*H.t^5*H.p^5 := heq scale 20000000 C H.t H.p
    _ ≤ Sizes.T n := by simpa only [hp,ht] using hn i

end IntegerMultBounds.MathlibTM2.Cost
