import IntegerMultBounds.Machine.NativePolynomialStageHeaders
import IntegerMultBounds.Machine.CompactNativeRoleHeaderBudget

/-! Codec payload synthesis and restoration are paid from the genuine native
polynomial volume. All original controller allowances are derived from Stage;
no already-expanded payload descriptor or metadata cost witness is assumed. -/
namespace IntegerMultBounds.Machine.NativePolynomialStageHeaderBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactNativeRoleTransferBudget (volume)
open NativePolynomialStageShape (shape payload width)
open NativePolynomialStageHeaders (cost prepared restore)
open ButterflyAxisHeadersArithmetic (scheduleCost)

/-- The encoded stage volume is precisely three times the existing symbol
volume; enlarging the header does not enlarge the physical native word. -/
theorem expanded_volume (s : Shape) (rows ell p : ℕ) :
    rows*(shape s ell p).recordWidth=3*volume rows s ell p := by
  rw [NativePolynomialStageShape.volume]
  unfold volume CompactNativeRoleOriginal.symbols CompactNativeRoleOriginal.inner
    ActivePrefixStageNativePolynomial.symbols width CompactNativeRoleHeaders.recordWidth
  ring

theorem payload_le (s : Shape) (rows ell p : ℕ) (hr : 0<rows) :
    payload s ell p≤3*volume rows s ell p := by
  have hp : 0<rows*2^s.bits := Nat.mul_pos hr (pow_pos (by decide) _)
  have h := Nat.le_mul_of_pos_left (payload s ell p) hp
  have he := expanded_volume s rows ell p
  unfold Shape.recordWidth at he
  rw [NativePolynomialStageShape.bits] at he
  change rows*(2^s.bits*payload s ell p)=3*volume rows s ell p at he
  nlinarith

theorem scalar_le {s : Shape} (v : Stage s) (rows ell p : ℕ)
    (hr : 0<rows) (hA : 0<s.axes) (hG : 0<s.guard) (hK : 0<s.chunk) (hpay : s.payload=1) :
    CompactSpectatorLeafSetupBudget.scalar s rows ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val≤
      18*volume rows s ell p := by
  have hg := CompactNativeRoleControllerBudget.geometry_bounds v rows ell p hr hA hG hK hpay
  have hc := CompactNativeRoleControllerBudget.controller_bounds v rows ell p hr hG hK
  have hb := (CompactNativeRoleHeaderBudget.values_le s rows ell p hr).1
  have hv : 0<volume rows s ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  have g0 := hg 0
  have g1 := hg 1
  have g2 := hg 2
  have g3 := hg 3
  have g4 := hg 4
  have g5 := hg 5
  have g6 := hg 6
  have g7 := hg 7
  have g8 := hg 8
  have c0 := hc 0
  have c1 := hc 1
  have c2 := hc 2
  have c3 := hc 3
  have c4 := hc 4
  have c5 := hc 5
  simp only [CompactNativeRoleControllerBudget.geometry,CompactNativeRoleControllerBudget.controller,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at *
  unfold CompactSpectatorLeafSetupBudget.scalar
  omega

def constant := FixedBasePowerDescriptor.constant 2+2000000

/-- Both actual descriptor lifecycles cost only a fixed native-volume factor. -/
theorem lifecycle_linear {s : Shape} (v : Stage s) (rows ell p : ℕ)
    (hr : 0<rows) (hA : 0<s.axes) (hG : 0<s.guard) (hK : 0<s.chunk) (hpay : s.payload=1) :
    cost s rows ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val+
      scheduleCost restore (prepared s rows ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val)≤
        constant*volume rows s ell p := by
  have hH : 0<s.H := Nat.mul_pos hA hG
  have hg := CompactSpectatorLeafSetupBudget.geometry_cost s rows ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val hH hK
  have hs := scalar_le v rows ell p hr hA hG hK hpay
  have hrest := NativePolynomialStageHeaders.rest_cost_bound s rows ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val
  have hclean := NativePolynomialStageHeaders.restore_cost_bound s rows ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val
  have hv := CompactNativeRoleHeaderBudget.values_le s rows ell p hr
  have hp := payload_le s rows ell p hr
  have hV : 0<volume rows s ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  have hpow := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) hv.2.2.2.1
  unfold cost constant
  rw [hpay] at hrest hclean
  nlinarith

end
end IntegerMultBounds.Machine.NativePolynomialStageHeaderBudget
