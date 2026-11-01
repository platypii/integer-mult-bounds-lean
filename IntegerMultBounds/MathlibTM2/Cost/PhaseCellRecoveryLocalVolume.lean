module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedRecoveryRowFast

/-! Local recovery work keeps interval payload and sparse boundary products.
In particular it does not charge an ambient axis traversal for every core. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

/-- Scalar preparation is paid by p² local coordinates, and numerical work by
actual boundary rows and the sparse active-row envelope. -/
def replicaRecoveryLocalVolume {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) : ℕ :=
  replicaHaloLocalCoordinates H+H.p^2+H.span+H.band+
    (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+1+
    ((haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+1)*(12*H.band+1)+
    (haloBoundaryCountBound s H.t (2*H.band) H.origin (H.origin+H.span)+4*H.band)*(2*H.band+1)

theorem replicaRecoveryLocalVolume_bounds {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) :
    H.p^2 ≤ replicaRecoveryLocalVolume H ∧
    H.span+H.band+(haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+1 ≤ replicaRecoveryLocalVolume H ∧
    ((haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+1)*(12*H.band+1) ≤ replicaRecoveryLocalVolume H ∧
    (haloBoundaryCountBound s H.t (2*H.band) H.origin (H.origin+H.span)+4*H.band)*(2*H.band+1)+1 ≤
      replicaRecoveryLocalVolume H := by
  unfold replicaRecoveryLocalVolume
  omega

/-- The older whole-axis estimate follows from the local one, for callers
that have not yet exposed their interval overlap. -/
theorem replicaRecoveryLocalVolume_gap_le {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s)
    (haxis : H.p^2 ≤ H.t) :
    replicaRecoveryLocalVolume H ≤ 300*(H.t+(H.t-s)*H.band^2) := by
  have hcoords := replicaHaloLocalCoordinates_le H
  have hspan := H.span_fit
  have hband : H.band ≤ s := H.band_fit
  have hs := H.s_lt_t
  have hN : (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card ≤ s := by
    simpa only [ZMod.card] using (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card_le_univ
  have hk := familyKernelVolume_le (a := H.origin) (b := H.origin+H.span)
    H.s_lt_t (PhaseCellBand.width_pos H.p H.u)
  change familyKernelVolume s H.t H.band H.origin (H.origin+H.span) ≤
    200*(H.t+(H.t-s)*H.band^2) at hk
  unfold familyKernelVolume at hk
  unfold replicaRecoveryLocalVolume
  omega

/-- The actual cached preparation row has a local bound with no ambient-axis
lower bound: scalar preparation is retained in the local volume. -/
theorem cachedReplicaRecoveryPreparationRow_local_fast_le (cw cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s),
      H.wordWidth ≤ cw*H.p → H.metadataWidth ≤ cV*H.p →
      (cachedReplicaRecoveryPreparationRowCost H : ℝ) ≤
        D*(replicaRecoveryLocalVolume H : ℝ)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hsolve⟩ := preparedResidual_fast_le cw
  obtain ⟨E,hE,hloop⟩ := retainedPageSpatialIntervalLoopCost_mask_fast_le cw
  let K := 20020*cw^3+20000*(cw+cV+1)+1000*(cw+1)+20*cw+28
  refine ⟨C+E+K,by positivity,?_⟩
  intro s _ H hw hV
  let V := replicaRecoveryLocalVolume H
  obtain ⟨hpV,hrows,hboundary,hactiveV⟩ := replicaRecoveryLocalVolume_bounds H
  have hVp : 1 ≤ V := by dsimp only [V]; omega
  have hspan : H.span ≤ V := by dsimp only [V]; omega
  have hword : H.wordWidth = 2*H.precision+8 := by
    unfold ReplicaHaloProblem.wordWidth ReplicaHaloProblem.precision executionWidth executionPrecision
    omega
  have hwpos : 1 ≤ H.wordWidth := by omega
  have hqw : H.precision ≤ H.wordWidth := by omega
  have hsetup := recoveryScalarPrepareCost_le cw hqw hwpos hw hpV
  have hwidth : H.wordWidth+H.metadataWidth+1 ≤ (cw+cV+1)*H.p := by
    have := H.p_pos
    nlinarith only [hw,hV,this]
  have hwidth' : H.wordWidth+1 ≤ (cw+1)*H.p := by
    have := H.p_pos
    nlinarith only [hw,this]
  have hpage := couplingCoefficientPageInterval_length_geometry H.s_lt_t (2^15*H.p) H.precision H.u H.band
    H.origin (H.origin+H.span) H.origin H.span H.span_fit H.span_fit
  have hpageV : (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band
      H.origin (H.origin+H.span) H.origin H.span).length+1 ≤ V := by
    dsimp only [V]
    omega
  have hlineWidth : 20*H.wordWidth+26 ≤ (20*cw+26)*H.p := by
    have := H.p_pos
    nlinarith only [hw,this]
  have hnative : prepareCost H.precision H.wordWidth+
      20000*(H.span+H.band+(haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+1)*
        (H.wordWidth+H.metadataWidth+1)+
      1000*((couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band
        H.origin (H.origin+H.span) H.origin H.span).length+1)*(H.wordWidth+1)+
      H.span*(20*H.wordWidth+26)+2 ≤ K*V*H.p := by
    have hrowsW := Nat.mul_le_mul hrows hwidth
    have hpageW := Nat.mul_le_mul hpageV hwidth'
    have hline := Nat.mul_le_mul hspan hlineWidth
    have hunit : 1 ≤ V*H.p := Nat.mul_pos hVp H.p_pos
    dsimp only [K]
    nlinarith only [hsetup,hrowsW,hpageW,hline,hunit]
  have hb := hsolve H.p H.precision
    (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card (12*H.band+1)
    H.p_pos (hword.symm.trans_le hw) (by omega)
  rw [←hword] at hb
  have hl := hloop H.p H.precision H.wordWidth s H.t H.band H.origin
    (H.origin+H.span) H.origin H.span true H.p_pos hwpos hw
  have hactive := retainedCouplingActiveRows_le_geometry H.s_lt_t true H.band H.origin
    (H.origin+H.span) H.origin H.span H.span_fit H.span_fit
  have hactiveProduct : retainedCouplingActiveRows true s H.t H.band H.origin (H.origin+H.span)
      H.origin H.span*(H.band+1) ≤ V := by
    have hh := Nat.mul_le_mul hactive (by omega : H.band+1 ≤ 2*H.band+1)
    dsimp only [V]
    omega
  have hbV : ((((haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+1)*(12*H.band+1) : ℕ) : ℝ) ≤ V := by
    exact_mod_cast hboundary
  have haV : ((retainedCouplingActiveRows true s H.t H.band H.origin (H.origin+H.span)
      H.origin H.span*(H.band+1) : ℕ) : ℝ) ≤ V := by exact_mod_cast hactiveProduct
  have hbs := mul_le_mul_of_nonneg_left hbV (by positivity : (0 : ℝ) ≤ C*(H.p : ℝ)^(129/128 : ℝ))
  have has := mul_le_mul_of_nonneg_left haV (by positivity : (0 : ℝ) ≤ E*(H.p : ℝ)^(129/128 : ℝ))
  have hnR : ((prepareCost H.precision H.wordWidth+
      20000*(H.span+H.band+(haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+1)*
        (H.wordWidth+H.metadataWidth+1)+
      1000*((couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band
        H.origin (H.origin+H.span) H.origin H.span).length+1)*(H.wordWidth+1)+
      H.span*(20*H.wordWidth+26)+2 : ℕ) : ℝ) ≤ (K*V*H.p : ℕ) := by exact_mod_cast hnative
  have hp1 : (1 : ℝ) ≤ H.p := by exact_mod_cast H.p_pos
  have hpPow := Real.self_le_rpow_of_one_le hp1 (by norm_num : (1 : ℝ) ≤ 129/128)
  have hnp := mul_le_mul_of_nonneg_left hpPow (by positivity : (0 : ℝ) ≤ (K : ℝ)*V)
  have hr : (cachedReplicaRecoveryPreparationRowCost H : ℝ) ≤
      ((preparedResidualSolveCost H.precision H.wordWidth
        (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card (12*H.band+1)+
      prepareCost H.precision H.wordWidth+
      20000*(H.span+H.band+(haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+1)*
        (H.wordWidth+H.metadataWidth+1)+
      1000*((couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band
        H.origin (H.origin+H.span) H.origin H.span).length+1)*(H.wordWidth+1)+
      retainedPageSpatialIntervalLoopCost true H.precision H.wordWidth s H.t H.band
        H.origin (H.origin+H.span) H.origin H.span : ℕ) : ℝ) := by
    exact_mod_cast cachedReplicaRecoveryPreparationRowCost_le H
  change _ ≤ (C+E+(K : ℝ))*(V : ℝ)*(H.p : ℝ)^(129/128 : ℝ)
  push_cast at hb hl hbs has hnR hnp hr ⊢
  nlinarith only [hb,hl,hbs,has,hnR,hnp,hr]

end IntegerMultBounds.MathlibTM2.Cost
