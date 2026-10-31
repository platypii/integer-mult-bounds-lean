module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaInteriorBatch
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaInteriorFast

/-! The installed replica cache and dimension transition preserve the combined
interior batch's fast envelope. One numerical page remains a shared input. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem prepareReplicaInteriorCacheCost_le (N B L w : ℕ) (hB : 1 ≤ B) (hL : 1 ≤ L) (hw : 1 ≤ w) :
    prepareReplicaInteriorCacheCost N B L w ≤ 500*(N+1)*(B*L*w) := by
  let volume := B*L*w
  have hvol : 1 ≤ volume := by dsimp [volume]; exact Nat.mul_le_mul (Nat.mul_le_mul hB hL) hw
  have hBL : B*L ≤ volume := Nat.le_mul_of_pos_right _ hw
  have hBV : B ≤ volume := (Nat.le_mul_of_pos_right B hL).trans hBL
  have hLV : L ≤ volume := (Nat.le_mul_of_pos_left L hB).trans hBL
  have hwV : w ≤ volume := Nat.le_mul_of_pos_left w (by nlinarith only [hB,hL])
  have hscale : volume ≤ (N+1)*volume := Nat.le_mul_of_pos_left _ (by omega)
  have hN : N ≤ (N+1)*volume := (Nat.le_mul_of_pos_right N hvol).trans (Nat.mul_le_mul_right volume (by omega))
  have hNB : N*B ≤ (N+1)*volume := (Nat.mul_le_mul_left N hBV).trans (Nat.mul_le_mul_right volume (by omega))
  have hdim : prepareReplicaSolverDimensionsCost N B L w ≤ 100*(N+1)*volume := by
    have hBL' := hBL.trans hscale
    have hL' := hLV.trans hscale
    have hB' := hBV.trans hscale
    have hw' := hwV.trans hscale
    have hOne := hvol.trans hscale
    unfold prepareReplicaSolverDimensionsCost
    rw [Nat.mul_assoc]
    omega
  have hc := replicaWeightCacheCost_le N B L w hw
  change replicaWeightCacheCost N B L w ≤ 200*(N+1)*(volume+1) at hc
  have hcopy : replicaWeightCacheCost N B L w ≤ 400*(N+1)*volume := by
    have hv : volume+1 ≤ 2*volume := by omega
    have hs := Nat.mul_le_mul_left (200*(N+1)) hv
    exact hc.trans (by convert hs using 1; ring)
  change replicaWeightCacheCost N B L w+prepareReplicaSolverDimensionsCost N B L w ≤ _
  calc
    _ ≤ 400*(N+1)*volume+100*(N+1)*volume := Nat.add_le_add hcopy hdim
    _ = _ := by dsimp only [volume]; ring

private theorem installedBill_le (startup D N B L R M E : ℝ)
    (hD : 0 ≤ D) (hN : 0 ≤ N) (hB : 0 ≤ B) (hL : 0 ≤ L) (hR : 0 ≤ R) (hM : 0 ≤ M) (hE : 0 ≤ E) :
    E*(N+1)*B*L*M+(startup+D*N*B*(L+R)*M) ≤
      startup+(D+E)*(N+1)*B*(L+R)*M := by
  have hDR := mul_nonneg (mul_nonneg (mul_nonneg hD hB) (add_nonneg hL hR)) hM
  have hER := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hE (by linarith : 0 ≤ N+1)) hB) hR) hM
  nlinarith only [hDR,hER]

theorem preparedReplicaInteriorBatch_fast_le (cl cw cr cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p l N B L s t u target rhsExp : ℕ,
      1 ≤ p → 1 ≤ B → 1 ≤ L → l ≤ cl*p → executionWidth p l target rhsExp ≤ cw*p →
      2^l ≤ cr*p → weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
        (executionWidth p l target rhsExp) t u ≤ cV*p →
      ((prepareReplicaInteriorCacheCost N B L (executionWidth p l target rhsExp)+
        cachedBatchFromOriginsCost p l (N*B) L s t u target rhsExp : ℕ) : ℝ) ≤
      (cachedBatchFromOriginsCost p l 0 L s t u target rhsExp : ℝ)+
        D*((N+1 : ℕ) : ℝ)*B*((L : ℝ)+(2^l : ℕ))*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨D,hD,hfast⟩ := replicaInteriorBatch_fast_le cl cw cr cV
  refine ⟨D+500*cw,by positivity,?_⟩
  intro p l N B L s t u target rhsExp hp hB hL hl hw hr hV
  let w := executionWidth p l target rhsExp
  let M := (p : ℝ)^(129/128 : ℝ)
  have hwpos : 1 ≤ w := by dsimp [w,executionWidth]; omega
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpow : (p : ℝ) ≤ M := Real.self_le_rpow_of_one_le hpR (by norm_num)
  have hwidth : (w : ℝ) ≤ (cw : ℝ)*M := by
    calc
      _ ≤ (cw : ℝ)*p := by exact_mod_cast hw
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg cw)
  have hsetup : (prepareReplicaInteriorCacheCost N B L w : ℝ) ≤
      500*((N+1 : ℕ) : ℝ)*B*L*w  := by
    have hb : prepareReplicaInteriorCacheCost N B L w ≤ 500*(N+1)*B*L*w := by
      simpa only [Nat.mul_assoc] using prepareReplicaInteriorCacheCost_le N B L w hB hL hwpos
    exact_mod_cast hb
  have hsetupFast := hsetup.trans (mul_le_mul_of_nonneg_left hwidth (by positivity : 0 ≤ (500 : ℝ)*((N+1 : ℕ) : ℝ)*B*L))
  have hnative := hfast p l N B L s t u target rhsExp hp hL hl hw hr hV
  have hsum := add_le_add hsetupFast hnative
  have hbill := installedBill_le (cachedBatchFromOriginsCost p l 0 L s t u target rhsExp)
    D N B L (2^l : ℕ) M (500*cw) hD (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
  dsimp only [M] at hsum hbill
  push_cast at hsum hbill ⊢
  exact hsum.trans (by convert hbill using 1; ring)

end IntegerMultBounds.MathlibTM2.Cost
