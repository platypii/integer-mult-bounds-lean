module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedReplicaCouplingLoopFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryLocalVolume

/-! Cached coupling uses the same local volume as recovery. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem cachedReplicaLocalCoupling_local_fast_le (cw cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s),
      H.wordWidth ≤ cw*H.p → H.metadataWidth ≤ cV*H.p → ∀ boundary : Bool,
      (cachedReplicaLocalCouplingCost boundary (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
        H.origin (H.origin+H.span) H.origin H.span H.metadataWidth : ℝ) ≤
        D*(replicaRecoveryLocalVolume H : ℝ)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨E,hE,hfast⟩ := retainedPageSpatialIntervalLoopCost_mask_fast_le cw
  let K := 10000*(cw+cV+1)+1000*(cw+1)+20*cw+28
  refine ⟨(K : ℝ)+E,by positivity,?_⟩
  intro s _ H hw hV boundary
  let G := replicaRecoveryLocalVolume H
  obtain ⟨_,hrows,_,hactiveG⟩ := replicaRecoveryLocalVolume_bounds H
  have hp := H.p_pos
  have hG : 1 ≤ G := by dsimp only [G]; omega
  have hspan : H.span ≤ G := by dsimp only [G]; omega
  have hrow : H.span+H.band+1 ≤ G := by dsimp only [G]; omega
  have hwidth : H.wordWidth+H.metadataWidth+1 ≤ (cw+cV+1)*H.p := by nlinarith only [hw,hV,hp]
  have hwidth' : H.wordWidth+1 ≤ (cw+1)*H.p := by nlinarith only [hw,hp]
  have hpageG : (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band
      H.origin (H.origin+H.span) H.origin H.span).length+1 ≤ G := by
    rw [couplingCoefficientPageInterval_length_active]
    exact replicaRecoveryLocalVolume_active_le H true
  have hlineWidth : 20*H.wordWidth+26 ≤ (20*cw+26)*H.p := by nlinarith only [hw,hp]
  have hnative : 10000*(H.span+H.band+1)*(H.wordWidth+H.metadataWidth+1)+
      1000*((couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band
        H.origin (H.origin+H.span) H.origin H.span).length+1)*(H.wordWidth+1)+
      H.span*(20*H.wordWidth+26)+2 ≤ K*G*H.p := by
    have hrowsW := Nat.mul_le_mul hrow hwidth
    have hpageW := Nat.mul_le_mul hpageG hwidth'
    have hline := Nat.mul_le_mul hspan hlineWidth
    have hunit : 1 ≤ G*H.p := Nat.mul_pos hG hp
    dsimp only [K]
    nlinarith only [hrowsW,hpageW,hline,hunit]
  have hcoupling : retainedCouplingActiveRows boundary s H.t H.band H.origin (H.origin+H.span)
      H.origin H.span*(H.band+1) ≤ G := by
    have hh := Nat.mul_le_mul_left
      (retainedCouplingActiveRows boundary s H.t H.band H.origin (H.origin+H.span) H.origin H.span)
      (by omega : H.band+1 ≤ 2*H.band+1)
    have ha := replicaRecoveryLocalVolume_active_le H boundary
    dsimp only [G]
    omega
  have hcouplingR : ((retainedCouplingActiveRows boundary s H.t H.band H.origin (H.origin+H.span)
      H.origin H.span*(H.band+1) : ℕ) : ℝ) ≤ G := by exact_mod_cast hcoupling
  have ha := mul_le_mul_of_nonneg_left hcouplingR (by positivity : (0 : ℝ) ≤ E*(H.p : ℝ)^(129/128 : ℝ))
  have hpR : (1 : ℝ) ≤ H.p := by exact_mod_cast hp
  have hpPow := Real.self_le_rpow_of_one_le hpR (by norm_num : (1 : ℝ) ≤ 129/128)
  have hnPow := mul_le_mul_of_nonneg_left hpPow (by positivity : (0 : ℝ) ≤ (K : ℝ)*(G : ℝ))
  have hnR := (Nat.cast_le (α := ℝ)).mpr hnative
  have hwpos : 1 ≤ H.wordWidth := by unfold ReplicaHaloProblem.wordWidth executionWidth; omega
  have hl := hfast H.p H.precision H.wordWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span
    boundary hp hwpos hw
  have hc := cachedReplicaLocalCouplingCost_le boundary (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
    H.origin (H.origin+H.span) H.origin H.span H.metadataWidth
  have hcR := (Nat.cast_le (α := ℝ)).mpr hc
  change _ ≤ ((K : ℝ)+E)*(G : ℝ)*(H.p : ℝ)^(129/128 : ℝ)
  push_cast at hcR hnR ha hl ⊢
  nlinarith only [hcR,hl,hnR,hnPow,ha]

theorem cachedReplicaCouplingTransition_local_fast_le (cw cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s),
      H.wordWidth ≤ cw*H.p → H.metadataWidth ≤ cV*H.p →
      ((cachedReplicaCouplingTransitionCost H H.metadataWidth+3 : ℕ) : ℝ) ≤
        D*(replicaRecoveryLocalVolume H : ℝ)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hrow⟩ := cachedReplicaLocalCoupling_local_fast_le cw cV
  let K := 24*cw+27
  refine ⟨C+K,by positivity,?_⟩
  intro s _ H hw hV
  let G := replicaRecoveryLocalVolume H
  obtain ⟨_,hrows,_,_⟩ := replicaRecoveryLocalVolume_bounds H
  have hp := H.p_pos
  have hG : 1 ≤ G := by dsimp only [G]; omega
  have hspan : H.span ≤ G := by dsimp only [G]; omega
  have hline := Nat.mul_le_mul hspan hw
  have hunit : 1 ≤ G*H.p := Nat.mul_pos hG hp
  have hn : 24*(H.span*H.wordWidth)+27 ≤ K*G*H.p := by
    dsimp only [K]
    nlinarith only [hline,hunit]
  have hnR := (Nat.cast_le (α := ℝ)).mpr hn
  have hpR : (1 : ℝ) ≤ H.p := by exact_mod_cast hp
  have hpPow := Real.self_le_rpow_of_one_le hpR (by norm_num : (1 : ℝ) ≤ 129/128)
  have hnPow := mul_le_mul_of_nonneg_left hpPow (by positivity : (0 : ℝ) ≤ (K : ℝ)*(G : ℝ))
  have hc := hrow H hw hV false
  have hsplit : cachedReplicaCouplingTransitionCost H H.metadataWidth+3 =
      cachedReplicaLocalCouplingCost false (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
        H.origin (H.origin+H.span) H.origin H.span H.metadataWidth+(24*(H.span*H.wordWidth)+27) := by
    unfold cachedReplicaCouplingTransitionCost stageReplicaCouplingRowCost finishReplicaCouplingRowCost
    omega
  rw [hsplit]
  change _ ≤ (C+(K : ℝ))*(G : ℝ)*(H.p : ℝ)^(129/128 : ℝ)
  push_cast at hnR ⊢
  nlinarith only [hc,hnR,hnPow]

end IntegerMultBounds.MathlibTM2.Cost
