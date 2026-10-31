module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHandedReplicaInteriorBatch
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaInteriorFast

/-! The generated handoff preserves the same-key interior fast envelope. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem handedReplicaInteriorBatch_fast_le (cl cw cr cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p l N B L s t u target rhsExp : ℕ,
      1 ≤ p → 1 ≤ L → l ≤ cl*p → executionWidth p l target rhsExp ≤ cw*p →
      2^l ≤ cr*p → weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
        (executionWidth p l target rhsExp) t u ≤ cV*p →
      ((generatedPrefixHandoffCost (N*B) L (executionWidth p l target rhsExp)+
        cachedBatchFromOriginsCost p l (N*B) L s t u target rhsExp : ℕ) : ℝ) ≤
      (cachedBatchFromOriginsCost p l 0 L s t u target rhsExp : ℝ)+
        D*(N : ℝ)*B*((L : ℝ)+(2^l : ℕ))*(p : ℝ)^(129/128 : ℝ)+19 := by
  obtain ⟨D,hD,hfast⟩ := replicaInteriorBatch_fast_le cl cw cr cV
  refine ⟨D+36*cw,by positivity,?_⟩
  intro p l N B L s t u target rhsExp hp hL hl hw hr hV
  let w := executionWidth p l target rhsExp
  let M := (p : ℝ)^(129/128 : ℝ)
  have hwpos : 1 ≤ w := by dsimp [w,executionWidth]; omega
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpow : (p : ℝ) ≤ M := Real.self_le_rpow_of_one_le hpR (by norm_num)
  have hwidth : (w : ℝ) ≤ (cw : ℝ)*M := by
    calc
      _ ≤ (cw : ℝ)*p := by exact_mod_cast hw
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg cw)
  have hhand : (generatedPrefixHandoffCost (N*B) L w : ℝ) ≤ 36*(N : ℝ)*B*L*w+19 := by
    have hb : generatedPrefixHandoffCost (N*B) L w ≤ 36*N*B*L*w+19 := by
      simpa only [Nat.mul_assoc] using generatedPrefixHandoffCost_le (N*B) L w hL hwpos
    exact_mod_cast hb
  have hwScale := mul_le_mul_of_nonneg_left hwidth
    (show 0 ≤ (36 : ℝ)*N*B*L by positivity)
  have hR : (L : ℝ) ≤ (L : ℝ)+(2^l : ℕ) := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hRScale := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hR (show 0 ≤ (36 : ℝ)*cw*N*B by positivity))
    (Real.rpow_nonneg (Nat.cast_nonneg p) (129/128 : ℝ))
  have hhandFast : (generatedPrefixHandoffCost (N*B) L w : ℝ) ≤
      (36*cw : ℝ)*N*B*((L : ℝ)+(2^l : ℕ))*M+19 := by
    dsimp only [M] at *
    nlinarith only [hhand,hwScale,hRScale]
  have hnative := hfast p l N B L s t u target rhsExp hp hL hl hw hr hV
  have hsum := add_le_add hhandFast hnative
  push_cast at hsum ⊢
  dsimp only [M] at hsum
  nlinarith only [hsum]

end IntegerMultBounds.MathlibTM2.Cost
