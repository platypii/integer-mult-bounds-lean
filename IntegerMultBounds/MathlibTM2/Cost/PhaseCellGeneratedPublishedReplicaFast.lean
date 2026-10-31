module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeneratedGatheredReplicaInteriorFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPublishedReplicaTraffic
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPublishedGatheredReplica

/-! The complete generated solve/publication trace retains the fast interior
exponent. Publication adds shared setup and linear local packed movement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem generatedPublishedGatheredReplica_fast_le (cl cw cr cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p l N B V span L s t u target rhsExp : ℕ,
      1 ≤ p → 1 ≤ B → 1 ≤ L → l ≤ cl*p → executionWidth p l target rhsExp ≤ cw*p →
      2^l ≤ cr*p → weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
        (executionWidth p l target rhsExp) t u ≤ cV*p →
      (generatedPublishedGatheredReplicaCost p l N B V span L s t u target rhsExp : ℝ) ≤
      ((generateReplicaWeightPageCost 0 (2^15*p) s t u (executionPrecision p l target rhsExp)
          L (executionWidth p l target rhsExp) B+
        cachedBatchFromOriginsCost p l 0 L s t u target rhsExp+
        preparedGatheredPublicationCost 0 V span L (executionWidth p l target rhsExp) B : ℕ) : ℝ)+
        500*B*L*(executionWidth p l target rhsExp)+
        (preparedOriginAdvanceCost V span (executionWidth p l target rhsExp) B+
          2*(span*executionWidth p l target rhsExp)+2*B+10 : ℕ)+
        D*N*((B : ℝ)*((L : ℝ)+(2^l : ℕ))+span+1)*(p : ℝ)^(129/128 : ℝ)+19 := by
  obtain ⟨D,hD,hfast⟩ := generatedGatheredReplicaInteriorBatch_fast_le cl cw cr cV
  refine ⟨D+73*(cw+1),by positivity,?_⟩
  intro p l N B V span L s t u target rhsExp hp hB hL hl hw hr hV
  let w := executionWidth p l target rhsExp
  let X : ℝ := (B : ℝ)*((L : ℝ)+(2^l : ℕ))+span+1
  let M : ℝ := (p : ℝ)^(129/128 : ℝ)
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpM : (p : ℝ) ≤ M := Real.self_le_rpow_of_one_le hpR (by norm_num)
  have hX : (span : ℝ)+1 ≤ X := by
    dsimp only [X]
    have hh : (0 : ℝ) ≤ (B : ℝ)*((L : ℝ)+(2^l : ℕ)) := by positivity
    linarith
  have hv : span*w+1 ≤ (cw+1)*(span+1)*p := by
    have hh := Nat.mul_le_mul_left span hw
    have hh' := Nat.add_le_add hh hp
    dsimp only [w]
    nlinarith only [hh',Nat.zero_le (span*p),Nat.zero_le (cw*p)]
  have hvR : ((span*w+1 : ℕ) : ℝ) ≤ ((cw+1)*(span+1)*p : ℕ) := by exact_mod_cast hv
  have hvM : ((span*w+1 : ℕ) : ℝ) ≤ (cw+1)*X*M := by
    calc
      _ ≤ (cw+1)*((span : ℝ)+1)*p := by simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] using hvR
      _ ≤ (cw+1)*X*p := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hX (by positivity)) (by positivity)
      _ ≤ (cw+1)*X*M := mul_le_mul_of_nonneg_left hpM (by dsimp only [X]; positivity)
  have htraffic := mul_le_mul_of_nonneg_left hvM (show (0 : ℝ) ≤ 73*N by positivity)
  have hc := hfast p l N B V span L s t u target rhsExp hp hB hL hl hw hr hV
  have hpub := preparedGatheredPublicationCost_le_shared N V span L w B
  have hpubR : (preparedGatheredPublicationCost N V span L w B : ℝ) ≤
      preparedGatheredPublicationCost 0 V span L w B+73*N*(span*w+1) := by exact_mod_cast hpub
  change ((generatedGatheredReplicaInteriorBatchCost p l N B V span L s t u target rhsExp+
    preparedGatheredPublicationCost N V span L w B : ℕ) : ℝ) ≤ _
  dsimp only [X,M,w] at htraffic hpubR
  push_cast at hc htraffic hpubR ⊢
  nlinarith only [hc,htraffic,hpubR]

end IntegerMultBounds.MathlibTM2.Cost
