module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedRecoveryNativeTraffic
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedSetupPolynomial

/-! The complete cached preparation row has fast numerical cost and linear native traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

/-- Scalar-counter construction is lower order once an axis exceeds the squared precision. -/
theorem recoveryScalarPrepareCost_le {p q w t : ℕ} (cw : ℕ)
    (hq : q ≤ w) (hw : 1 ≤ w) (hwidth : w ≤ cw*p) (haxis : p^2 ≤ t) :
    prepareCost q w ≤ 20020*cw^3*t*p := by
  have hs := scalarPrepareCost_arg_le (hq.trans hwidth) hwidth hw
  have hp := Nat.mul_le_mul_right p haxis
  calc
    _ ≤ 20020*(cw*p)^3 := hs
    _ = 20020*cw^3*(p^2*p) := by ring
    _ ≤ _ := by nlinarith only [Nat.mul_le_mul_left (20020*cw^3) hp]

theorem cachedReplicaRecoveryRow_native_le {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s)
    (cw cV : ℕ) (hw : H.wordWidth ≤ cw*H.p) (hV : H.metadataWidth ≤ cV*H.p)
    (haxis : H.p^2 ≤ H.t) :
    prepareCost H.precision H.wordWidth+
      300000*(H.t+(H.t-s)*H.band^2)*(H.wordWidth+H.metadataWidth+1)+
      H.span*(20*H.wordWidth+26)+2 ≤
      (20020*cw^3+300000*(cw+cV+1)+20*cw+28)*(H.t+(H.t-s)*H.band^2)*H.p := by
  let G := H.t+(H.t-s)*H.band^2
  have hp := H.p_pos
  have ht : 1 ≤ H.t := by have := H.s_lt_t; omega
  have htG : H.t ≤ G := Nat.le_add_right _ _
  have hG : 1 ≤ G := ht.trans htG
  have hspan : H.span ≤ G := by have := H.span_fit; have := H.s_lt_t; omega
  have hqw : H.precision ≤ H.wordWidth := by
    unfold ReplicaHaloProblem.precision ReplicaHaloProblem.wordWidth executionPrecision executionWidth
    omega
  have hwpos : 1 ≤ H.wordWidth := by unfold ReplicaHaloProblem.wordWidth executionWidth; omega
  have hsetup := (recoveryScalarPrepareCost_le cw hqw hwpos hw haxis).trans
    (Nat.mul_le_mul_right H.p (Nat.mul_le_mul_left (20020*cw^3) htG))
  have hwidth : H.wordWidth+H.metadataWidth+1 ≤ (cw+cV+1)*H.p := by nlinarith only [hw,hV,hp]
  have htraffic := Nat.mul_le_mul_left (300000*G) hwidth
  have hlineWidth : 20*H.wordWidth+26 ≤ (20*cw+26)*H.p := by nlinarith only [hw,hp]
  have hline := Nat.mul_le_mul hspan hlineWidth
  have hGp : 1 ≤ G*H.p := Nat.mul_pos hG hp
  change prepareCost H.precision H.wordWidth+300000*G*(H.wordWidth+H.metadataWidth+1)+
    H.span*(20*H.wordWidth+26)+2 ≤ (20020*cw^3+300000*(cw+cV+1)+20*cw+28)*G*H.p
  change _ ≤ _ at hsetup htraffic hline
  nlinarith only [hsetup,htraffic,hline,hGp]

theorem cachedReplicaRecoveryPreparationRow_fast_le (cw cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s),
      H.wordWidth ≤ cw*H.p → H.metadataWidth ≤ cV*H.p → H.p^2 ≤ H.t →
      (cachedReplicaRecoveryPreparationRowCost H : ℝ) ≤
        D*((H.t+(H.t-s)*H.band^2 : ℕ) : ℝ)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hsolve⟩ := preparedResidual_fast_le cw
  obtain ⟨E,hE,hloop⟩ := retainedPageSpatialIntervalLoopCost_mask_fast_le cw
  let K := 20020*cw^3+300000*(cw+cV+1)+20*cw+28
  refine ⟨200*C+200*E+K,by positivity,?_⟩
  intro s _ H hw hV haxis
  let G := H.t+(H.t-s)*H.band^2
  have hword : H.wordWidth = 2*H.precision+8 := by
    unfold ReplicaHaloProblem.wordWidth ReplicaHaloProblem.precision executionWidth executionPrecision
    omega
  have hwpos : 1 ≤ H.wordWidth := by omega
  have hb := hsolve H.p H.precision
    (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card (12*H.band+1)
    H.p_pos (hword.symm.trans_le hw) (by omega)
  rw [←hword] at hb
  have hl := hloop H.p H.precision H.wordWidth s H.t H.band H.origin
    (H.origin+H.span) H.origin H.span true H.p_pos hwpos hw
  have hv := familyKernelVolume_le (a := H.origin) (b := H.origin+H.span) H.s_lt_t
    (PhaseCellBand.width_pos H.p H.u)
  have hboundary : ((haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+1)*(12*H.band+1) ≤ 200*G := by
    apply le_trans (b := familyKernelVolume s H.t H.band H.origin (H.origin+H.span))
    · unfold familyKernelVolume; omega
    · exact hv
  have hactive := retainedCouplingActiveRows_le_geometry H.s_lt_t true H.band H.origin
    (H.origin+H.span) H.origin H.span H.span_fit H.span_fit
  have hcoupling : retainedCouplingActiveRows true s H.t H.band H.origin (H.origin+H.span)
      H.origin H.span*(H.band+1) ≤ 200*G := by
    calc
      _ ≤ (haloBoundaryCountBound s H.t (2*H.band) H.origin (H.origin+H.span)+4*H.band)*(2*H.band+1) :=
        Nat.mul_le_mul hactive (by omega)
      _ ≤ familyKernelVolume s H.t H.band H.origin (H.origin+H.span) := by unfold familyKernelVolume; omega
      _ ≤ _ := hv
  have hbR : ((((haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+1)*(12*H.band+1) : ℕ) : ℝ) ≤ 200*G := by exact_mod_cast hboundary
  have haR : ((retainedCouplingActiveRows true s H.t H.band H.origin (H.origin+H.span)
      H.origin H.span*(H.band+1) : ℕ) : ℝ) ≤ 200*G := by exact_mod_cast hcoupling
  have hbs := mul_le_mul_of_nonneg_left hbR (by positivity : (0 : ℝ) ≤ C*(H.p : ℝ)^(129/128 : ℝ))
  have has := mul_le_mul_of_nonneg_left haR (by positivity : (0 : ℝ) ≤ E*(H.p : ℝ)^(129/128 : ℝ))
  have hn := cachedReplicaRecoveryRow_native_le H cw cV hw hV haxis
  have hnR : ((prepareCost H.precision H.wordWidth+
      300000*G*(H.wordWidth+H.metadataWidth+1)+H.span*(20*H.wordWidth+26)+2 : ℕ) : ℝ) ≤
      (K*G*H.p : ℕ) := by exact_mod_cast hn
  have hp1 : (1 : ℝ) ≤ H.p := by exact_mod_cast H.p_pos
  have hpPow := Real.self_le_rpow_of_one_le hp1 (by norm_num : (1 : ℝ) ≤ 129/128)
  have hnp := mul_le_mul_of_nonneg_left hpPow (by positivity : (0 : ℝ) ≤ (K : ℝ)*G)
  have hr : (cachedReplicaRecoveryPreparationRowCost H : ℝ) ≤
      ((preparedResidualSolveCost H.precision H.wordWidth
        (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card (12*H.band+1)+
      prepareCost H.precision H.wordWidth+300000*G*(H.wordWidth+H.metadataWidth+1)+
      retainedPageSpatialIntervalLoopCost true H.precision H.wordWidth s H.t H.band
        H.origin (H.origin+H.span) H.origin H.span : ℕ) : ℝ) := by
    exact_mod_cast cachedReplicaRecoveryPreparationRowCost_gap H
  dsimp only [G] at hbs has hnR hnp hr
  push_cast at hb hl hbs has hnR hnp hr ⊢
  nlinarith only [hb,hl,hbs,has,hnR,hnp,hr]

end IntegerMultBounds.MathlibTM2.Cost
