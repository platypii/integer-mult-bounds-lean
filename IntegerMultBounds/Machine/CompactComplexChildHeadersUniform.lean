import IntegerMultBounds.Machine.CompactComplexRecursiveChildHeaders

/-! The physical child-header costs are uniform over every canonical root and
descendant, independently of the selected role's row count and payload size.
Internal and scalar leaves are both paid from the original global dimension. -/
namespace IntegerMultBounds.Machine.CompactComplexChildHeadersUniform
noncomputable section
open CompactComplexRecursiveGeometry
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageHeadersData (initial originalValues)
open CompactChildHeadersArithmetic (scheduleCost)
open Networks.BinaryRowProgram (Op)
variable {s : Shape} (rho : Fin s.chunk) {left k : ℕ}
  (hactive : s.active ≤ s.axes) (pair : Op (Fin arity)) (slot : Fin arity) (rows : ℕ)

def constant : ℕ := 100000*(2*arity+5)^2

private theorem scaled_square (A x : ℕ) :
    100000*((2*A+5)*(x+1))^2 = (100000*(2*A+5)^2)*(x+1)^2 := by
  rw [mul_pow,Nat.mul_assoc]

private theorem constant_dominates (A : ℕ) : 10000*(A+4) ≤ 100000*(2*A+5)^2 := by
  nlinarith

private theorem linear_absorbed (A x : ℕ) :
    10000*((A+4)*(x+1)) ≤ (100000*(2*A+5)^2)*(x+1)^2 := by
  have hc := constant_dominates A
  have hs : x+1 ≤ (x+1)^2 := by nlinarith
  calc
    _ = (10000*(A+4))*(x+1) := (Nat.mul_assoc _ _ _).symm
    _ ≤ (100000*(2*A+5)^2)*(x+1) := Nat.mul_le_mul_right _ hc
    _ ≤ (100000*(2*A+5)^2)*(x+1)^2 := Nat.mul_le_mul_left _ hs

theorem internal_cost (visit : Visit s.active left (k+2)) :
    scheduleCost (CompactComplexChildHeadersData.schedule slot)
      (initial (CompactComplexChildHeadersData.parent rho visit hactive pair) rows) ≤
      constant*(s.axes+1)^2 := by
  have hb := CompactComplexChildHeadersBudget.cost_le slot
    (initial (CompactComplexChildHeadersData.parent rho visit hactive pair) rows)
    s.active arity (arity^(k+1)) left (s.active-(left+arity^(k+2)))
    rfl rfl rfl rfl rfl
  have hf := visit.fits
  have hpow : arity^(k+1) ≤ arity^(k+2) := by
    exact Nat.pow_le_pow_right (by decide : 0<arity) (by omega)
  have hw : arity^(k+1) ≤ s.axes := by omega
  have hl : left ≤ s.axes := by omega
  have hr : s.active-(left+arity^(k+2)) ≤ s.axes :=
    (Nat.sub_le _ _).trans hactive
  have hs := slot.isLt
  have hsum : s.active+arity+arity^(k+1)+left+(s.active-(left+arity^(k+2)))+slot.val+1 ≤
      (2*arity+5)*(s.axes+1) := by nlinarith
  calc
    _ ≤ 100000*(s.active+arity+arity^(k+1)+left+(s.active-(left+arity^(k+2)))+slot.val+1)^2 := hb
    _ ≤ 100000*((2*arity+5)*(s.axes+1))^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 2)
    _ = constant*(s.axes+1)^2 := scaled_square arity s.axes

include hactive in
theorem leaf_cost (v : ActivePrefixStageParameters.Stage s) :
    scheduleCost (CompactComplexLeafHeadersData.schedule slot.val) (initial v rows) ≤
      constant*(s.axes+1)^2 := by
  have hb := CompactComplexLeafHeadersData.cost_le slot.val s.active v.left v.right
    (initial v rows) rfl rfl rfl
  have hf := v.activeAxes
  have hl : v.left ≤ s.axes := by omega
  have hr : v.right ≤ s.axes := by omega
  have hs := slot.isLt
  have hsum : s.active+v.left+v.right+slot.val+1 ≤
      (arity+4)*(s.axes+1) := by nlinarith
  calc
    _ ≤ 10000*(s.active+v.left+v.right+slot.val+1) := hb
    _ ≤ 10000*((arity+4)*(s.axes+1)) := Nat.mul_le_mul_left _ hsum
    _ ≤ constant*(s.axes+1)^2 := linear_absorbed arity s.axes

end
end IntegerMultBounds.Machine.CompactComplexChildHeadersUniform
