module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaWeightFactoryCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGatheredReplicaInteriorFast
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedGatheredReplicaInteriorBatch

/-! The actual generated-page caller keeps numerical page construction shared.
Only native replica-header work is added to its repeated fast-time charge. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

def generatedGatheredReplicaInteriorBatchCost (p l N B V span L s t u target rhsExp : ℕ) : ℕ :=
  generateReplicaWeightPageCost N (2^15*p) s t u (executionPrecision p l target rhsExp)
    L (executionWidth p l target rhsExp) B+
      gatheredReplicaInteriorBatchCost p l N B V span L s t u target rhsExp

private theorem replicaHeader_le (N X M : ℝ) (hN : 0 ≤ N) (hX : 1 ≤ X) (hM : 1 ≤ M) :
    2*N ≤ 2*N*X*M := by
  have hX0 : 0 ≤ X := by linarith
  have hx := mul_le_mul_of_nonneg_left hX (show 0 ≤ 2*N by positivity)
  have hm := mul_le_mul_of_nonneg_left hM (show 0 ≤ 2*N*X by positivity)
  nlinarith only [hx,hm]

theorem generatedGatheredReplicaInteriorBatch_fast_le (cl cw cr cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p l N B V span L s t u target rhsExp : ℕ,
      1 ≤ p → 1 ≤ B → 1 ≤ L → l ≤ cl*p → executionWidth p l target rhsExp ≤ cw*p →
      2^l ≤ cr*p → weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
        (executionWidth p l target rhsExp) t u ≤ cV*p →
      (generatedGatheredReplicaInteriorBatchCost p l N B V span L s t u target rhsExp : ℝ) ≤
      ((generateReplicaWeightPageCost 0 (2^15*p) s t u (executionPrecision p l target rhsExp)
          L (executionWidth p l target rhsExp) B+
        cachedBatchFromOriginsCost p l 0 L s t u target rhsExp : ℕ) : ℝ)+
        500*B*L*(executionWidth p l target rhsExp)+
        (preparedOriginAdvanceCost V span (executionWidth p l target rhsExp) B+
          2*(span*executionWidth p l target rhsExp)+2*B+10 : ℕ)+
        D*N*((B : ℝ)*((L : ℝ)+(2^l : ℕ))+span+1)*(p : ℝ)^(129/128 : ℝ)+19 := by
  obtain ⟨D,hD,hfast⟩ := gatheredReplicaInteriorBatch_fast_le cl cw cr cV
  refine ⟨D+2,by positivity,?_⟩
  intro p l N B V span L s t u target rhsExp hp hB hL hl hw hr hV
  have hc := hfast p l N B V span L s t u target rhsExp hp hB hL hl hw hr hV
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hMp : (1 : ℝ) ≤ (p : ℝ)^(129/128 : ℝ) :=
    hpR.trans (Real.self_le_rpow_of_one_le hpR (by norm_num))
  have hX : (1 : ℝ) ≤ (B : ℝ)*((L : ℝ)+(2^l : ℕ))+span+1 := by
    have hx : (0 : ℝ) ≤ (B : ℝ)*((L : ℝ)+(2^l : ℕ))+span := by positivity
    linarith only [hx]
  have hh := replicaHeader_le N ((B : ℝ)*((L : ℝ)+(2^l : ℕ))+span+1)
    ((p : ℝ)^(129/128 : ℝ)) (Nat.cast_nonneg N) hX hMp
  unfold generatedGatheredReplicaInteriorBatchCost
  rw [generateReplicaWeightPageCost_replicas]
  push_cast at hc hh ⊢
  nlinarith only [hc,hh]

end IntegerMultBounds.MathlibTM2.Cost
