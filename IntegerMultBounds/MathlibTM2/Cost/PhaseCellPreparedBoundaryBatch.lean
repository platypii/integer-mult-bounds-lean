module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryBatch
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPreparedBoundary

/-! The executed prepared batch pays one control setup and linear repeated row-bandwidth work. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem preparedBoundaryBatchCost_eq (w N W replicas : ℕ) :
    preparedBoundaryBatchCost w N W replicas = N*(6*w+9)+16+
      replicas*(N*(preparedBoundaryRowCost w W+22*w)+12*W*w+75) := by
  rw [preparedBoundaryBatchCost,preparedBoundarySolveCost_eq]
  ring

theorem preparedBoundaryBatchCost_le (w N W replicas : ℕ) (hW : 1 ≤ W) :
    preparedBoundaryBatchCost w N W replicas ≤
      600*(replicas+1)*(N+1)*W*(rmulCost w+w+1) := by
  let G := rmulCost w+w+1
  let F := (N+1)*W*G
  have hWG : w+1 ≤ W*G := (by dsimp [G]; omega : w+1 ≤ G).trans
    (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right G hW)
  have hF := Nat.mul_le_mul_left (N+1) hWG
  have hstart : N*(6*w+9)+16 ≤ 50*F := by dsimp [F] at *; nlinarith only [hF]
  have hextra : 22*N*w+25 ≤ 50*F := by dsimp [F] at *; nlinarith only [hF]
  have hsolve : preparedBoundarySolveCost w N W ≤ 400*F := by
    simpa only [F,G,Nat.mul_assoc] using preparedBoundarySolveCost_le w N W hW
  have hslope : preparedBoundarySolveCost w N W+22*N*w+25 ≤ 450*F := by omega
  change N*(6*w+9)+16+replicas*(preparedBoundarySolveCost w N W+22*N*w+25) ≤ _
  calc
    _ ≤ 50*F+replicas*(450*F) := Nat.add_le_add hstart (Nat.mul_le_mul_left replicas hslope)
    _ = (50+450*replicas)*F := by ring
    _ ≤ (600*(replicas+1))*F := Nat.mul_le_mul_right F (by omega)
    _ = _ := by dsimp [F,G]; ring

theorem preparedBoundaryBatch_fast_le (cw : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p w N W replicas : ℕ, 1 ≤ p → 1 ≤ w → w ≤ cw*p → 1 ≤ W →
      (preparedBoundaryBatchCost w N W replicas : ℝ) ≤
        C*((replicas+1 : ℕ) : ℝ)*((N+1 : ℕ) : ℝ)*(W : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨K,hK,hproduct⟩ := chirp_rmul_le cw
  refine ⟨600*(K+(cw : ℝ)+1),by positivity,?_⟩
  intro p w N W replicas hp hw hwidth hW
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPow : (p : ℝ) ≤ (p : ℝ)^(129/128 : ℝ) := Real.self_le_rpow_of_one_le hp1 (by norm_num)
  have hOne : (1 : ℝ) ≤ (p : ℝ)^(129/128 : ℝ) := Real.one_le_rpow hp1 (by norm_num)
  have hwidthR : (w : ℝ) ≤ (cw : ℝ)*(p : ℝ) := by exact_mod_cast hwidth
  have hwPow := hwidthR.trans (mul_le_mul_of_nonneg_left hpPow (Nat.cast_nonneg cw))
  have hscalar : ((rmulCost w+w+1 : ℕ) : ℝ) ≤ (K+(cw : ℝ)+1)*(p : ℝ)^(129/128 : ℝ) := by
    push_cast
    simpa only [add_mul,one_mul] using add_le_add (add_le_add (hproduct p w hp hw hwidth) hwPow) hOne
  have hkernel : (preparedBoundaryBatchCost w N W replicas : ℝ) ≤
      600*((replicas+1 : ℕ) : ℝ)*((N+1 : ℕ) : ℝ)*(W : ℝ)*((rmulCost w+w+1 : ℕ) : ℝ) := by
    exact_mod_cast preparedBoundaryBatchCost_le w N W replicas hW
  calc
    _ ≤ 600*((replicas+1 : ℕ) : ℝ)*((N+1 : ℕ) : ℝ)*(W : ℝ)*
        ((K+(cw : ℝ)+1)*(p : ℝ)^(129/128 : ℝ)) := hkernel.trans (mul_le_mul_of_nonneg_left hscalar (by positivity))
    _ = _ := by ring

theorem preparedBoundaryBatch_selected_fast_le (cl ct cN cB : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p l target N band replicas : ℕ, 1 ≤ p → l ≤ cl*p → target ≤ ct*p →
      Nat.size N ≤ cN*p → Nat.size (2*band+1) ≤ cB*p →
      (preparedBoundaryBatchCost (8*inverseExecutionExponent p l target N band+8) N (12*band+1) replicas : ℝ) ≤
        C*((replicas+1 : ℕ) : ℝ)*((N+1 : ℕ) : ℝ)*((12*band+1 : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := preparedBoundaryBatch_fast_le (16*cl+8*ct+8*cN+8*cB+680)
  refine ⟨C,hC,?_⟩
  intro p l target N band replicas hp hl ht hN hB
  exact hfast p _ N (12*band+1) replicas hp (by omega)
    (inverseExecutionWidth_le p l target N band cl ct cN cB hp hl ht hN hB) (by omega)

end IntegerMultBounds.MathlibTM2.Cost
