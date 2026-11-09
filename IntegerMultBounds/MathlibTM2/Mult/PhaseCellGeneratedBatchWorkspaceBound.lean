module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBatchSetupStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarSetupCostBound
import Mathlib.Tactic.Ring

/-! Shared inverse setup separates one arithmetic reserve from coefficient and page volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.Schoenhage.Schedule

theorem generatedBatchSetupWorkspace_zero_le_components
    (C P N q s t u band l L : ℕ) :
    let W := integerSetupWidth P q (N+1) 0
    let V := coefficientWorkspaceWidth P W t u band L
    let T := weightWorkspaceWidth P q (2*q+8) t u
    generatedBatchSetupWorkspace C P N q s t u band l L 0 ≤
      C*rmulCost W+3*prepareCost 0 W+
      100000*(V+T+1)^2+
      100000*(P*N+P+N+q+s+t+u+band+l+L+1)*(V+W+T+1)+
      100000*(C+1)*(L+1)^2*(W+q+1) := by
  have ht := (topN_facts (show 1 ≤ integerSetupWidth P q (N+1) 0 by
    unfold integerSetupWidth; omega)).2.1
  dsimp only
  unfold generatedBatchSetupWorkspace batchWeightedSetupWorkspace sharedBatchWeightSetupWorkspace
    sharedWeightInitWorkspace retainedWeightStepWorkspace retainedWeightPageWorkspace
    batchInverseSetupWorkspace headerGeneratorSetupWorkspace numericalGeneratorSetupWorkspace
    factorFactoryWorkspace packedGeneratorSetupWorkspace generatorSetupWorkspace
    generatedEncodedColumnWorkspace generatedIntegerColumnWorkspace columnEncodingWorkspace
    prepareIntegerIterationsWorkspace integerIterationWorkspace preparedIntegerStepWorkspace
    consumeIntegerRowWorkspace realWeightWorkspace reversedColumnWorkspace
  dsimp only
  rw [integerReciprocalWorkspace_eq]
  unfold coefficientWidthCost prepareCoefficientHeadersCost weightHeadersCost pairLayoutCost
    prepareBatchRuntimeCost releaseConstructionCost prepareBatchGeneratorPageWorkspace
    prepareBatchGeneratorPageCost packGeneratorsCost constructFactorPageCost factorRowStepCost
    packWeightBatchCost coefficientHeadersLinearCost tblC releaseFactorPageCost replicateGeneratorsCost
    swapBatchPayloadCost installBatchHeadersCost weightWidthCost
  have hdrop := Nat.mul_le_mul_left q (Nat.sub_le L 1)
  ring_nf at ht hdrop ⊢
  omega

@[irreducible] def generatedBatchSetupBudget (C P N q s t u band l L : ℕ) : ℕ :=
  let W := integerSetupWidth P q (N+1) 0
  let V := coefficientWorkspaceWidth P W t u band L
  let T := weightWorkspaceWidth P q (2*q+8) t u
  C*rmulCost W+60300*((2*W).size+1)*(W+1)^2+
    100000*(V+T+1)^2+
    100000*(P*N+P+N+q+s+t+u+band+l+L+1)*(V+W+T+1)+
    100000*(C+1)*(L+1)^2*(W+q+1)

private theorem triple_header {b d e : ℕ} (h : b ≤ 20100*d*e) : 3*b ≤ 60300*d*e := by
  ring_nf at h ⊢
  omega

private theorem replace_setup {x a b c d e f : ℕ} (h : x ≤ a+3*b+c+d+e) (hb : 3*b ≤ f) :
    x ≤ a+f+c+d+e := by omega

theorem generatedBatchSetupWorkspace_zero_le_budget
    (C P N q s t u band l L : ℕ) :
    generatedBatchSetupWorkspace C P N q s t u band l L 0 ≤
      generatedBatchSetupBudget C P N q s t u band l L := by
  have h := generatedBatchSetupWorkspace_zero_le_components C P N q s t u band l L
  have hw : 1 ≤ integerSetupWidth P q (N+1) 0 := by unfold integerSetupWidth; omega
  have hc := triple_header
    (prepareCost_le_header_square 0 (integerSetupWidth P q (N+1) 0) hw (by omega))
  unfold generatedBatchSetupBudget
  dsimp only at h ⊢
  exact replace_setup h hc

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
