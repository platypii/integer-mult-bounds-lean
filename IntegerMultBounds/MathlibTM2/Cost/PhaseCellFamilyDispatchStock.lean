module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyDispatchTrace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedFamilyStockCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFamilyDispatchKeys

/-! A ready dispatch needs headers, one setup/scratch bill and linear live batch stock. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def familyDispatchHeaderCost {s A : ℕ} [NeZero s]
    (p l t : ℕ) (r : FamilyDispatchInput s A) : ℕ :=
  let W := inverseCallerWordWidth p r.u l r.target s t
  inverseScalarAtoms p s t r.u r.a r.b*tblC W 0+
    inverseMasterCopyCost W (inverseMasterValues p r.u l r.target s t r.a r.b)+
    inverseReleaseCost W (inverseMasterValues p r.u l r.target s t r.a r.b)

theorem familyDispatchHeaderCost_width_le {s A : ℕ} [NeZero s]
    (p l t : ℕ) (r : FamilyDispatchInput s A) :
    inverseCallerWordWidth p r.u l r.target s t+1 ≤ familyDispatchHeaderCost p l t r := by
  let W := inverseCallerWordWidth p r.u l r.target s t
  have hatoms : 1 ≤ inverseScalarAtoms p s t r.u r.a r.b := by
    dsimp only [inverseScalarAtoms,inversePrecisionAtoms]
    omega
  have htable : W+1 ≤ tblC W 0 := by
    unfold tblC
    nlinarith only [Nat.zero_le (W*W)]
  have hprod : tblC W 0 ≤ inverseScalarAtoms p s t r.u r.a r.b*tblC W 0 := Nat.le_mul_of_pos_left _ hatoms
  change W+1 ≤ _
  change W+1 ≤ inverseScalarAtoms p s t r.u r.a r.b*tblC W 0+
    inverseMasterCopyCost W (inverseMasterValues p r.u l r.target s t r.a r.b)+
    inverseReleaseCost W (inverseMasterValues p r.u l r.target s t r.a r.b)
  omega

theorem familyDispatchInput_stock_le {T A s : ℕ} [NeZero s] {p l t : ℕ} {d : ℝ}
    (hst : s < t) (work : Fin 303 → Fin T) (r : FamilyDispatchInput s A) (hr : FamilyDispatchReady p l t d r) :
    r.stock p l t work ≤ 16000*familyDispatchHeaderCost p l t r+
      generatedFamilyComplexSetupCostBound A p r.u l s t r.a r.b r.target+
      familyComplexBatchStepCost A p r.u l s t r.a r.b r.target+
      16000*(r.inputs.length*s*r.width p l t) := by
  let W := inverseCallerWordWidth p r.u l r.target s t
  let w := r.width p l t
  let N := r.inputs.length
  let H := familyDispatchHeaderCost p l t r
  let setup := generatedFamilyComplexSetupCostBound A p r.u l s t r.a r.b r.target
  let K := familyComplexBatchStepCost A p r.u l s t r.a r.b r.target
  have hbank := familyInverseBatch_bank_stock_le r.rawBank r.inputs [] r.scalarWidth hr.scalarWidth
    hr.scalars hr.blank (by simpa only [FamilyDispatchInput.rawBank,List.append_nil] using hr.source) hr.count
  have hsum : (∑ i, (r.words i).length) ≤ 303*(N*s*w+W+N) := by
    simpa only [FamilyDispatchInput.rawBank,hr.outputBlank,List.length_nil,Nat.add_zero] using hbank
  have hH : W+1 ≤ H := familyDispatchHeaderCost_width_le p l t r
  have hw : 1 ≤ w := by dsimp only [w,FamilyDispatchInput.width,executionWidth]; omega
  have hs : 1 ≤ s := Nat.pos_of_ne_zero (NeZero.ne _)
  have hN : N ≤ N*s*w := (Nat.le_mul_of_pos_right N hs).trans (Nat.le_mul_of_pos_right (N*s) hw)
  have hclosed : generatedClosedFamilyComplexBatchStockCost A p r.u l s t r.a r.b r.target N ≤ setup+K+36*N*s*w :=
    generatedClosedFamilyComplexBatchStockCost_le hst A p r.u l r.a r.b r.target N
  have hraw : familyInverseBatchCallerStockCost A W p r.u l s t r.a r.b r.target N ≤ H+setup+K+36*N*s*w := by
    calc
      _ = H+generatedClosedFamilyComplexBatchStockCost A p r.u l s t r.a r.b r.target N := by
        dsimp only [H,familyDispatchHeaderCost,familyInverseBatchCallerStockCost,W]
        ac_rfl
      _ ≤ H+(setup+K+36*N*s*w) := Nat.add_le_add_left hclosed _
      _ = _ := by ring
  change r.stock p l t work ≤ 16000*H+setup+K+16000*(N*s*w)
  unfold FamilyDispatchInput.stock
  rw [takePlacedDescriptorBankCost_eq]
  change 23*(∑ i, (r.words i).length)+24*303+1+
    familyInverseBatchCallerStockCost A W p r.u l s t r.a r.b r.target N+
    (6*(N*s*w)+2*(∑ i, (r.words i).length)+611) ≤ _
  simp only [Nat.mul_assoc] at hsum hN hraw ⊢
  omega

end IntegerMultBounds.MathlibTM2.Cost
