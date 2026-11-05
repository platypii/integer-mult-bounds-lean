module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellBoundaryPublicationCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateBoundaryCounts

/-! Generate the three boundary controls with one uniform slot estimate. All
nonlinear work is shared scalar table work; stream traffic remains linear. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellMatrix

theorem exportSlotBoundaryCountCost_le (slot : Fin 3) (D s width w : ℕ)
    (hw : 0 < width) (hword : 1 ≤ w) (hroom : 3*width < s) :
    exportSlotBoundaryCountCost slot D s width w ≤ 16*tblC D 0+106*D+21*s*w+119 := by
  have hwidth : width ≤ s := by omega
  have hwidthw := Nat.mul_le_mul_right w hwidth
  have hwidthSmall := hwidth.trans (Nat.le_mul_of_pos_right s hword)
  have hskip := Nat.mul_le_mul_right w (boundaryCropStart_le s width hw hroom slot)
  have hlength : coreLength s width (boundaryCropIndex s width slot) ≤ s :=
    (Nat.min_le_right _ _).trans (Nat.sub_le _ _)
  have hlengthw := Nat.mul_le_mul_right w hlength
  unfold exportSlotBoundaryCountCost
  split <;> nlinarith only [hwidthw,hwidthSmall,hskip,hlengthw,Nat.zero_le (tblC D 0)]

theorem boundaryCountExportCost_le (D s width w : ℕ)
    (hw : 0 < width) (hword : 1 ≤ w) (hroom : 3*width < s) :
    boundaryCountExportCost D s width w ≤ 48*tblC D 0+318*D+63*s*w+358 := by
  have h₀ := exportSlotBoundaryCountCost_le 0 D s width w hw hword hroom
  have h₁ := exportSlotBoundaryCountCost_le 1 D s width w hw hword hroom
  have h₂ := exportSlotBoundaryCountCost_le 2 D s width w hw hword hroom
  simp only [boundaryCountExportCost,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  simp only [Nat.mul_assoc] at h₀ h₁ h₂ ⊢
  omega

def boundaryControlTimeBound (p D s : ℕ) : ℕ :=
  48*tblC D 0+324*D+63*s*(2*p+13)+(4*D+10)*(2*p+13)+368

def boundaryControlStockBound (p D s : ℕ) : ℕ :=
  144*tblC D 0+962*D+189*s*(2*p+13)+1082

theorem boundaryControlCosts_le (p D s width : ℕ) (hw : 0 < width) (hroom : 3*width < s) :
    ((((2*p+13)*(4*D+10)+4*D+8)+boundaryCountExportCost D s width (2*p+13)+(2*D+2) ≤
      boundaryControlTimeBound p D s)) ∧
    (2*(4*D+4)+3*boundaryCountExportCost D s width (2*p+13) ≤ boundaryControlStockBound p D s) := by
  have hc := boundaryCountExportCost_le D s width (2*p+13) hw (by omega) hroom
  unfold boundaryControlTimeBound boundaryControlStockBound
  constructor <;> nlinarith only [hc]

end IntegerMultBounds.MathlibTM2.Cost
