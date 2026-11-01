module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedReplicaCouplingTraffic

/-! The cached replica-local row has the sparse halo-volume fast bound for
either source mask. Cache generation is shared and priced separately. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem cachedReplicaLocalCoupling_fast_le (cw cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s),
      H.wordWidth ≤ cw*H.p → H.metadataWidth ≤ cV*H.p → ∀ boundary : Bool,
      (cachedReplicaLocalCouplingCost boundary (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
        H.origin (H.origin+H.span) H.origin H.span H.metadataWidth : ℝ) ≤
        D*((H.t+(H.t-s)*H.band^2 : ℕ) : ℝ)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨E,hE,hfast⟩ := retainedPageSpatialIntervalLoopCost_mask_fast_le cw
  let K := 300000*(cw+cV+1)+20*cw+28
  refine ⟨(K : ℝ)+200*E,by positivity,?_⟩
  intro s _ H hw hV boundary
  let G := H.t+(H.t-s)*H.band^2
  let W := H.wordWidth+H.metadataWidth+1
  have hp := H.p_pos
  have ht : 1 ≤ H.t := by have := H.s_lt_t; omega
  have htG : H.t ≤ G := Nat.le_add_right _ _
  have hG : 1 ≤ G := ht.trans htG
  have hspan : H.span ≤ G := by have := H.span_fit; have := H.s_lt_t; omega
  have hwidth : W ≤ (cw+cV+1)*H.p := by dsimp only [W]; nlinarith only [hw,hV,hp]
  have htraffic := Nat.mul_le_mul_left (300000*G) hwidth
  have hlineWidth : 20*H.wordWidth+26 ≤ (20*cw+26)*H.p := by nlinarith only [hw,hp]
  have hline := Nat.mul_le_mul hspan hlineWidth
  have hunit : 1 ≤ G*H.p := Nat.mul_pos hG hp
  have hnative : 300000*G*W+H.span*(20*H.wordWidth+26)+2 ≤ K*G*H.p := by
    dsimp only [K]
    nlinarith only [htraffic,hline,hunit]
  have hactive := retainedCouplingActiveRows_le_geometry H.s_lt_t boundary H.band H.origin
    (H.origin+H.span) H.origin H.span H.span_fit H.span_fit
  have hvolume := familyKernelVolume_le (a := H.origin) (b := H.origin+H.span) H.s_lt_t
    (PhaseCellBand.width_pos H.p H.u)
  have hcoupling : retainedCouplingActiveRows boundary s H.t H.band H.origin (H.origin+H.span)
      H.origin H.span*(H.band+1) ≤ 200*G := by
    calc
      _ ≤ (haloBoundaryCountBound s H.t (2*H.band) H.origin (H.origin+H.span)+4*H.band)*(2*H.band+1) :=
        Nat.mul_le_mul hactive (by omega)
      _ ≤ familyKernelVolume s H.t H.band H.origin (H.origin+H.span) := by unfold familyKernelVolume; omega
      _ ≤ _ := hvolume
  have hcouplingR : ((retainedCouplingActiveRows boundary s H.t H.band H.origin (H.origin+H.span)
      H.origin H.span*(H.band+1) : ℕ) : ℝ) ≤ 200*G := by exact_mod_cast hcoupling
  have ha := mul_le_mul_of_nonneg_left hcouplingR (by positivity : (0 : ℝ) ≤ E*(H.p : ℝ)^(129/128 : ℝ))
  have hpR : (1 : ℝ) ≤ H.p := by exact_mod_cast hp
  have hpPow := Real.self_le_rpow_of_one_le hpR (by norm_num : (1 : ℝ) ≤ 129/128)
  have hnPow := mul_le_mul_of_nonneg_left hpPow (by positivity : (0 : ℝ) ≤ (K : ℝ)*(G : ℝ))
  have hnR : ((300000*G*W+H.span*(20*H.wordWidth+26)+2 : ℕ) : ℝ) ≤ K*G*H.p := by exact_mod_cast hnative
  have hwpos : 1 ≤ H.wordWidth := by unfold ReplicaHaloProblem.wordWidth executionWidth; omega
  have hl := hfast H.p H.precision H.wordWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span
    boundary hp hwpos hw
  have hc := cachedReplicaLocalCouplingCost_gap H boundary
  have hcR := (Nat.cast_le (α := ℝ)).mpr hc
  change _ ≤ ((300000*G*W+_ : ℕ) : ℝ) at hcR
  change _ ≤ ((K : ℝ)+200*E)*(G : ℝ)*(H.p : ℝ)^(129/128 : ℝ)
  push_cast at hcR hnR ha hl ⊢
  nlinarith only [hcR,hl,hnR,hnPow,ha]

end IntegerMultBounds.MathlibTM2.Cost
