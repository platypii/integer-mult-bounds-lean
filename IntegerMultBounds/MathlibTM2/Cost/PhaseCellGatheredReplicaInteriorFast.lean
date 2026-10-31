module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatheredReplicaInteriorBatch
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPreparedReplicaInteriorFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellHandedReplicaInteriorFast

/-! Price the actual cache/gather/handoff/numerical execution. Local binary
control decoding occurs once; repeated traffic has no ambient-period factor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

private theorem gatheredTraffic_le (N B L R span w cw M : ℝ)
    (hN : 0 ≤ N) (hB : 0 ≤ B) (hL : 0 ≤ L) (hR : 0 ≤ R) (hspan : 0 ≤ span)
    (hw : 1 ≤ w) (hwidth : w ≤ cw*M) :
    500*N*B*L*w+100*N*(B*L*w+span*w+1) ≤
      600*cw*N*(B*(L+R)+span+1)*M := by
  let X := B*(L+R)+span+1
  have hw0 : 0 ≤ w := by linarith
  have hBR := mul_nonneg hB hR
  have hBL := mul_nonneg hB hL
  have hBX : B*L ≤ X := by dsimp only [X]; nlinarith only [hBR,hspan]
  have hX : 0 ≤ X := hBL.trans hBX
  have hsource : B*L*w+span*w+1 ≤ X*w := by
    have hshort : B*L+span+1 ≤ X := by dsimp only [X]; nlinarith only [hBR]
    have hs := mul_le_mul_of_nonneg_right hshort hw0
    nlinarith only [hs,hw]
  have hcopy := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hBX hw0)
    (show 0 ≤ 500*N by positivity)
  have hgather := mul_le_mul_of_nonneg_left hsource (show 0 ≤ 100*N by positivity)
  have hscale := mul_le_mul_of_nonneg_left hwidth (show 0 ≤ 600*N*X by positivity)
  dsimp only [X] at hcopy hgather hscale
  nlinarith only [hcopy,hgather,hscale]

theorem gatheredReplicaInteriorBatch_fast_le (cl cw cr cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p l N B V span L s t u target rhsExp : ℕ,
      1 ≤ p → 1 ≤ B → 1 ≤ L → l ≤ cl*p → executionWidth p l target rhsExp ≤ cw*p →
      2^l ≤ cr*p → weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
        (executionWidth p l target rhsExp) t u ≤ cV*p →
      (gatheredReplicaInteriorBatchCost p l N B V span L s t u target rhsExp : ℝ) ≤
      (cachedBatchFromOriginsCost p l 0 L s t u target rhsExp : ℝ)+
        500*B*L*(executionWidth p l target rhsExp)+
        (preparedOriginAdvanceCost V span (executionWidth p l target rhsExp) B+
          2*(span*executionWidth p l target rhsExp)+2*B+10 : ℕ)+
        D*N*((B : ℝ)*((L : ℝ)+(2^l : ℕ))+span+1)*(p : ℝ)^(129/128 : ℝ)+19 := by
  obtain ⟨D,hD,hfast⟩ := handedReplicaInteriorBatch_fast_le cl cw cr cV
  refine ⟨D+600*cw,by positivity,?_⟩
  intro p l N B V span L s t u target rhsExp hp hB hL hl hw hr hV
  let w := executionWidth p l target rhsExp
  let M := (p : ℝ)^(129/128 : ℝ)
  have hwpos : 1 ≤ w := by dsimp [w,executionWidth]; omega
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpow : (p : ℝ) ≤ M := Real.self_le_rpow_of_one_le hpR (by norm_num)
  have hwidth : (w : ℝ) ≤ (cw : ℝ)*M :=
    (by exact_mod_cast hw : (w : ℝ) ≤ (cw : ℝ)*p).trans
      (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg cw))
  have hc : (prepareReplicaInteriorCacheCost N B L w : ℝ) ≤ 500*((N : ℝ)+1)*B*L*w := by
    have hb : prepareReplicaInteriorCacheCost N B L w ≤ 500*(N+1)*B*L*w := by
      simpa only [Nat.mul_assoc] using prepareReplicaInteriorCacheCost_le N B L w hB hL hwpos
    exact_mod_cast hb
  have hg : (sharedPackedReplicaGatherCost V N span L w B : ℝ) ≤
      (preparedOriginAdvanceCost V span w B+2*(span*w)+2*B+10 : ℕ)+
        100*(N : ℝ)*((B : ℝ)*L*w+span*w+1) := by
    have hb := sharedPackedReplicaGatherCost_le V N span L w B hB hL hwpos
    exact_mod_cast hb
  have hn := hfast p l N B L s t u target rhsExp hp hL hl hw hr hV
  have ht := gatheredTraffic_le N B L (2^l : ℕ) span w cw M
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (by exact_mod_cast hwpos) hwidth
  have hX : (B : ℝ)*((L : ℝ)+(2^l : ℕ)) ≤ (B : ℝ)*((L : ℝ)+(2^l : ℕ))+span+1 := by
    have hs := Nat.cast_nonneg (α := ℝ) span
    linarith only [hs]
  have hnScale := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hX (show 0 ≤ D*(N : ℝ) by positivity))
    (Real.rpow_nonneg (Nat.cast_nonneg p) (129/128 : ℝ))
  have hsum := add_le_add (add_le_add hc hg) hn
  change ((prepareReplicaInteriorCacheCost N B L w+sharedPackedReplicaGatherCost V N span L w B+
    (generatedPrefixHandoffCost (N*B) L w+cachedBatchFromOriginsCost p l (N*B) L s t u target rhsExp) : ℕ) : ℝ) ≤ _
  dsimp only [M] at ht
  push_cast at hsum ht hnScale ⊢
  dsimp only [w] at hsum ht hnScale ⊢
  nlinarith only [hsum,ht,hnScale]

end IntegerMultBounds.MathlibTM2.Cost
