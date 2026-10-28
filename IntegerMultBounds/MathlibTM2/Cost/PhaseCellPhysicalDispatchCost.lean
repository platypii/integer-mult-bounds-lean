module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawBatchBankStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedRawBatchKeys
import Mathlib.Tactic.Linarith

/-! Physical descriptor traffic is absorbed by a fixed multiple of the raw batch ledger. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem familyInverseBatchCallerCost_input_le (A W p u l s t a b target replicas : ℕ) [NeZero s] :
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
      (haloBoundary s t (PhaseCellBand.width p u) a b).card
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    W+replicas*s*w+replicas+1 ≤ familyInverseBatchCallerCost A W p u l s t a b target replicas := by
  dsimp only
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
    (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  have hclosed : replicas*s*w+replicas+1 ≤ generatedClosedFamilyComplexBatchCost A p u l s t a b target replicas := by
    dsimp only [generatedClosedFamilyComplexBatchCost,w,bits]
    omega
  have hatoms : 1 ≤ inverseScalarAtoms p s t u a b := by
    dsimp only [inverseScalarAtoms,inversePrecisionAtoms]
    omega
  have htable : W ≤ tblC W 0 := by
    unfold tblC
    nlinarith only [Nat.zero_le (W*W)]
  have hprod : tblC W 0 ≤ inverseScalarAtoms p s t u a b*tblC W 0 :=
    Nat.le_mul_of_pos_left _ hatoms
  change W+replicas*s*w+replicas+1 ≤ _
  unfold familyInverseBatchCallerCost
  omega

noncomputable def physicalFamilyDispatchCost (T A W p u l s t a b target replicas : ℕ) [NeZero s]
    (work : Fin 303 → Fin T) (words : Fin 303 → List (Fin (A+4))) : ℕ :=
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
    (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  takeDescriptorBankCost (placedDescriptorFields work words)+
    familyInverseBatchCallerCost A W p u l s t a b target replicas+
    (6*(replicas*s*w)+2*(∑ i, (words i).length)+611)

theorem physicalFamilyDispatchCost_le {T A W p u l s t a b target replicas : ℕ} [NeZero s]
    (work : Fin 303 → Fin T) (words : Fin 303 → List (Fin (A+4)))
    (hstock : (∑ i, (words i).length) ≤ 303*(replicas*s*
      executionWidth p l (initialSchurTarget p u
        (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
          (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+W+replicas)) :
    physicalFamilyDispatchCost T A W p u l s t a b target replicas work words ≤
      16000*familyInverseBatchCallerCost A W p u l s t a b target replicas := by
  have hinput := familyInverseBatchCallerCost_input_le A W p u l s t a b target replicas
  dsimp only at hinput hstock
  unfold physicalFamilyDispatchCost
  rw [takePlacedDescriptorBankCost_eq]
  dsimp only
  omega

end IntegerMultBounds.MathlibTM2.Cost
