module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedResidualBatch
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPreparedResidual

/-! The executed prepared batch pays one control setup and linear repeated row-bandwidth work. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem preparedResidualBatchCost_le (q N W replicas : ℕ) (hW : 1 ≤ W) :
    preparedResidualBatchCost q (2*q+8) N W replicas ≤
      1200*(replicas+1)*(N+1)*W*(rmulCost (2*q+8)+(2*q+8)+1) := by
  let w := 2*q+8
  let G := rmulCost w+w+1
  let F := (N+1)*W*G
  have hWG : w+1 ≤ W*G := (by dsimp [G]; omega : w+1 ≤ G).trans
    (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right G hW)
  have hF := Nat.mul_le_mul_left (N+1) hWG
  have hstart : N*(6*w+9)+16 ≤ 50*F := by dsimp [F] at *; nlinarith only [hF]
  have hextra : 22*N*w+25 ≤ 50*F := by dsimp [F] at *; nlinarith only [hF]
  have hsolve : preparedResidualSolveCost q (2*q+8) N W ≤ 1000*F := by
    simpa only [F,G,Nat.mul_assoc] using preparedResidualSolveCost_le q N W hW
  have hslope : preparedResidualSolveCost q (2*q+8) N W+22*N*w+25 ≤ 1050*F := by omega
  change N*(6*w+9)+16+replicas*(preparedResidualSolveCost q (2*q+8) N W+22*N*w+25) ≤ _
  calc
    _ ≤ 50*F+replicas*(1050*F) := Nat.add_le_add hstart (Nat.mul_le_mul_left replicas hslope)
    _ = (50+1050*replicas)*F := by ring
    _ ≤ (1200*(replicas+1))*F := Nat.mul_le_mul_right F (by omega)
    _ = _ := by dsimp [F,G]; ring

theorem preparedResidualBatch_fast_le (cw : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q N W replicas : ℕ, 1 ≤ p → 2*q+8 ≤ cw*p → 1 ≤ W →
      (preparedResidualBatchCost q (2*q+8) N W replicas : ℝ) ≤
        C*((replicas+1 : ℕ) : ℝ)*((N+1 : ℕ) : ℝ)*(W : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨K,hK,hproduct⟩ := chirp_rmul_le cw
  refine ⟨1200*(K+(cw : ℝ)+1),by positivity,?_⟩
  intro p q N W replicas hp hwidth hW
  let w := 2*q+8
  have hw : 1 ≤ w := by dsimp [w]; omega
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPow : (p : ℝ) ≤ (p : ℝ)^(129/128 : ℝ) := Real.self_le_rpow_of_one_le hp1 (by norm_num)
  have hOne : (1 : ℝ) ≤ (p : ℝ)^(129/128 : ℝ) := Real.one_le_rpow hp1 (by norm_num)
  have hwidthR : (w : ℝ) ≤ (cw : ℝ)*(p : ℝ) := by exact_mod_cast hwidth
  have hwPow := hwidthR.trans (mul_le_mul_of_nonneg_left hpPow (Nat.cast_nonneg cw))
  have hscalar : ((rmulCost w+w+1 : ℕ) : ℝ) ≤ (K+(cw : ℝ)+1)*(p : ℝ)^(129/128 : ℝ) := by
    push_cast
    simpa only [add_mul,one_mul] using add_le_add (add_le_add (hproduct p w hp hw hwidth) hwPow) hOne
  have hkernel : (preparedResidualBatchCost q (2*q+8) N W replicas : ℝ) ≤
      1200*((replicas+1 : ℕ) : ℝ)*((N+1 : ℕ) : ℝ)*(W : ℝ)*((rmulCost w+w+1 : ℕ) : ℝ) := by
    exact_mod_cast preparedResidualBatchCost_le q N W replicas hW
  calc
    _ ≤ 1200*((replicas+1 : ℕ) : ℝ)*((N+1 : ℕ) : ℝ)*(W : ℝ)*
        ((K+(cw : ℝ)+1)*(p : ℝ)^(129/128 : ℝ)) := hkernel.trans (mul_le_mul_of_nonneg_left hscalar (by positivity))
    _ = _ := by ring

theorem preparedResidualBatch_selected_fast_le (cl ct cN cB : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p l target N band replicas : ℕ, 1 ≤ p → l ≤ cl*p → target ≤ ct*p →
      Nat.size N ≤ cN*p → Nat.size (2*band+1) ≤ cB*p →
      (preparedResidualBatchCost (4*inverseExecutionExponent p l target N band) (8*inverseExecutionExponent p l target N band+8) N (12*band+1) replicas : ℝ) ≤
        C*((replicas+1 : ℕ) : ℝ)*((N+1 : ℕ) : ℝ)*((12*band+1 : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := preparedResidualBatch_fast_le (16*cl+8*ct+8*cN+8*cB+680)
  refine ⟨C,hC,?_⟩
  intro p l target N band replicas hp hl ht hN hB
  have hw := inverseExecutionWidth_le p l target N band cl ct cN cB hp hl ht hN hB
  have heq : 2*(4*inverseExecutionExponent p l target N band)+8 =
      8*inverseExecutionExponent p l target N band+8 := by omega
  simpa only [heq] using hfast p (4*inverseExecutionExponent p l target N band) N (12*band+1)
    replicas hp (by omega) (by omega)

end IntegerMultBounds.MathlibTM2.Cost
