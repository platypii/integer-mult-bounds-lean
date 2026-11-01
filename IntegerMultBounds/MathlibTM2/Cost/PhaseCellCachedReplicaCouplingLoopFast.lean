module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaCouplingLoop
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedReplicaCouplingFast

/-! The complete cached counted traversal pays only sparse-volume fast row work
and linear staging/retirement. Shared mask preparation is outside this loop. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem cachedReplicaCouplingTransition_fast_le (cw cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s),
      H.wordWidth ≤ cw*H.p → H.metadataWidth ≤ cV*H.p →
      ((cachedReplicaCouplingTransitionCost H H.metadataWidth+3 : ℕ) : ℝ) ≤
        D*((H.t+(H.t-s)*H.band^2 : ℕ) : ℝ)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hrow⟩ := cachedReplicaLocalCoupling_fast_le cw cV
  let K := 24*cw+27
  refine ⟨C+K,by positivity,?_⟩
  intro s _ H hw hV
  let G := H.t+(H.t-s)*H.band^2
  have hp := H.p_pos
  have ht : 1 ≤ H.t := by have := H.s_lt_t; omega
  have htG : H.t ≤ G := Nat.le_add_right _ _
  have hG : 1 ≤ G := ht.trans htG
  have hspan : H.span ≤ G := by have := H.span_fit; have := H.s_lt_t; omega
  have hline := Nat.mul_le_mul hspan hw
  have hunit : 1 ≤ G*H.p := Nat.mul_pos hG hp
  have hn : 24*(H.span*H.wordWidth)+27 ≤ K*G*H.p := by
    dsimp only [K]
    nlinarith only [hline,hunit]
  have hnR : ((24*(H.span*H.wordWidth)+27 : ℕ) : ℝ) ≤ K*G*H.p := by exact_mod_cast hn
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
  change _ ≤ C*(G : ℝ)*(H.p : ℝ)^(129/128 : ℝ) at hc
  push_cast at hnR ⊢
  nlinarith only [hc,hnR,hnPow]

theorem cachedReplicaCouplingLoop_fast_le (cw cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s),
      H.wordWidth ≤ cw*H.p → H.metadataWidth ≤ cV*H.p → ∀ steps : ℕ,
      steps ≤ H.Fs.length*(cachedReplicaCouplingTransitionCost H H.metadataWidth+3)+2 →
      (steps : ℝ) ≤ 2+D*H.Fs.length*((H.t+(H.t-s)*H.band^2 : ℕ) : ℝ)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨D,hD,hrow⟩ := cachedReplicaCouplingTransition_fast_le cw cV
  refine ⟨D,hD,?_⟩
  intro s _ H hw hV steps hn
  have hc := mul_le_mul_of_nonneg_left (hrow H hw hV)
    (Nat.cast_nonneg H.Fs.length : (0 : ℝ) ≤ H.Fs.length)
  have hs : (steps : ℝ) ≤ H.Fs.length*(cachedReplicaCouplingTransitionCost H H.metadataWidth+3 : ℕ)+2 := by
    exact_mod_cast hn
  push_cast at hc hs ⊢
  nlinarith only [hc,hs]

end IntegerMultBounds.MathlibTM2.Cost
