module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseRoundBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInverseBatchCaller

/-! Normalization is absorbed by a fixed multiple of the existing raw batch allowances. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

private theorem roundCost_components (W E K M G p : ℕ) (hE : 2 ≤ E)
    (hK : 4*Nat.size (4*p)+52 ≤ K) (hM : 24*E+11*W+6 ≤ M)
    (n : ℕ) (hG : 4*(n*(8*E+8)) ≤ G) :
    (K+4*Nat.size (4*p)+52)*tblC W 0+16*(8*E+8)+44*W+38+
      n*(14*(8*E+8)+23) ≤ 8*(K*tblC W 0+M+G) := by
  have hs : (K+4*Nat.size (4*p)+52)*tblC W 0 ≤ 2*(K*tblC W 0) := by
    have h := Nat.mul_le_mul_right (tblC W 0) (show K+4*Nat.size (4*p)+52 ≤ 2*K by omega)
    simpa only [Nat.mul_assoc] using h
  have hm : 16*(8*E+8)+44*W+38 ≤ 8*M := by omega
  have hn : n*(14*(8*E+8)+23) ≤ 8*G := by
    have hcoef : 14*(8*E+8)+23 ≤ 32*(8*E+8) := by omega
    have h := Nat.mul_le_mul_left n hcoef
    nlinarith only [h,hG]
  nlinarith only [hs,hm,hn]

private theorem inverseRound_components (W p u l target s t a b G N : ℕ) [NeZero s]
    (hG : 4*(N*s*(8*inverseExecutionExponent p l target
      (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)+8)) ≤ G) :
    inverseRoundBatchCost W p u l target s t a b (N*s) ≤
      8*(inverseScalarAtoms p s t u a b*tblC W 0+
        inverseMasterCopyCost W (inverseMasterValues p u l target s t a b)+G) := by
  let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
  have hE : 2 ≤ E := by dsimp [E,inverseExecutionExponent]; omega
  have hsize := Nat.size_le_size (show 4*p ≤ 8*p by omega)
  have hK : 4*Nat.size (4*p)+52 ≤ inverseScalarAtoms p s t u a b := by
    dsimp only [inverseScalarAtoms,inversePrecisionAtoms]
    omega
  have hm : 24*E+11*W+6 ≤ inverseMasterCopyCost W (inverseMasterValues p u l target s t a b) := by
    have h := List.le_sum_of_mem (List.mem_map.mpr
      ⟨(2 : Fin 10),List.mem_finRange _,rfl⟩)
        (xs := (List.finRange 10).map (fun i => 6*inverseMasterValues p u l target s t a b i+11*W+6))
    change 6*(4*E)+11*W+6 ≤ _ at h
    dsimp only [inverseMasterCopyCost]
    omega
  exact roundCost_components W E _ _ G p hE hK hm (N*s) hG

theorem inverseRoundBatchCost_le_callerCost (A W p u l target s t a b N : ℕ) [NeZero s] :
    inverseRoundBatchCost W p u l target s t a b (N*s) ≤
      8*familyInverseBatchCallerCost A W p u l s t a b target N := by
  have hG : 4*(N*s*(8*inverseExecutionExponent p l target
      (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)+8)) ≤
      generatedClosedFamilyComplexBatchCost A p u l s t a b target N := by
    dsimp only [generatedClosedFamilyComplexBatchCost,executionWidth]
    simp only [←inverseExecutionExponent_eq]
    omega
  have h := inverseRound_components W p u l target s t a b _ N hG
  unfold familyInverseBatchCallerCost
  omega

theorem inverseRoundBatchCost_le_callerStock (A W p u l target s t a b N : ℕ) [NeZero s] :
    inverseRoundBatchCost W p u l target s t a b (N*s) ≤
      8*familyInverseBatchCallerStockCost A W p u l s t a b target N := by
  have hG : 4*(N*s*(8*inverseExecutionExponent p l target
      (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)+8)) ≤
      generatedClosedFamilyComplexBatchStockCost A p u l s t a b target N := by
    dsimp only [generatedClosedFamilyComplexBatchStockCost,generatedFactorFamilyComplexBatchStockCost,
      generatedCouplingFamilyComplexBatchStockCost,generatedFamilyComplexBatchStockCost,
      familyComplexBatchStockCost,executionWidth]
    simp only [←inverseExecutionExponent_eq]
    omega
  have h := inverseRound_components W p u l target s t a b _ N hG
  unfold familyInverseBatchCallerStockCost
  omega

end IntegerMultBounds.MathlibTM2.Cost
