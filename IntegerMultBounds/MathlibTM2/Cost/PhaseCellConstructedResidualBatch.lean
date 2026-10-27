module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConstructedResidualBatch
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPreparedResidualBatch

/-! One actual computed factor setup plus fast repeated solves; setup is never multiplied by the replica count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem constructedResidualBatch_selected_allowance (cl ct cG : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p u l target s t a b replicas : ℕ, ∀ [NeZero s],
      1 ≤ p → s < t → PhaseCellBand.width p u ≤ s → l ≤ cl*p → target ≤ ct*p → Nat.size (2*s+1) ≤ cG*p →
      let B := haloBoundary s t (PhaseCellBand.width p u) a b
      let solveTarget := boundaryRecoveryTarget p (target+1)
      let q := executionPrecision p l (initialSchurTarget p u (boundaryTableBits p solveTarget 2 B.card) 2) 2
      let w := executionWidth p l (initialSchurTarget p u (boundaryTableBits p solveTarget 2 B.card) 2) 2
      ((constructedBoundaryFactorCost p u l s t a b solveTarget 2+
        preparedResidualBatchCost q w B.card (12*PhaseCellBand.width p u+1) replicas : ℕ) : ℝ) ≤
      (constructedBoundaryFactorCost p u l s t a b solveTarget 2 : ℝ)+
        C*((replicas+1 : ℕ) : ℝ)*((haloBoundaryCountBound s t (PhaseCellBand.width p u) a b+1 : ℕ) : ℝ)*
          ((12*PhaseCellBand.width p u+1 : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := preparedResidualBatch_selected_fast_le cl ct cG cG
  refine ⟨C,hC,?_⟩
  intro p u l target s t a b replicas _ hp hst hband hl ht hgeometry
  dsimp only
  let band := PhaseCellBand.width p u
  let N := (haloBoundary s t band a b).card
  have hN : N ≤ s := by
    have hh := Finset.card_le_univ (haloBoundary s t band a b)
    rwa [ZMod.card] at hh
  have hNlog : Nat.size N ≤ cG*p := (Nat.size_le_size (hN.trans (by omega : s ≤ 2*s+1))).trans hgeometry
  have hBlog : Nat.size (2*band+1) ≤ cG*p := (Nat.size_le_size (by omega : 2*band+1 ≤ 2*s+1)).trans hgeometry
  have hh := hfast p l target N band replicas hp hl ht hNlog hBlog
  have hrows : ((N+1 : ℕ) : ℝ) ≤ ((haloBoundaryCountBound s t band a b+1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right (haloBoundary_card_bound hst band a b) 1
  have hrepeat := hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrows (mul_nonneg hC (Nat.cast_nonneg _))) (Nat.cast_nonneg _)) (by positivity))
  have hwidth : executionWidth p l
      (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N) 2) 2 =
      8*inverseExecutionExponent p l target N band+8 := by
    simp only [executionWidth,← inverseExecutionExponent_eq]
    rfl
  have hprecision : executionPrecision p l
      (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N) 2) 2 =
      4*inverseExecutionExponent p l target N band := by
    simp only [executionPrecision, ← inverseExecutionExponent_eq]
    rfl
  rw [Nat.cast_add,hwidth,hprecision]
  exact add_le_add (le_refl _) hrepeat

end IntegerMultBounds.MathlibTM2.Cost
