import IntegerMultBounds.Machine.CompactScalarAllowances
import IntegerMultBounds.Machine.ButterflyIndependentGuardHeaders

/-! Actual multiplier scalars bound the enlarged initial native signed record
width. One selected chunk-axis means one bit rho+i*K, not K butterfly passes;
all D*K address bits nevertheless remain in the literal coefficient stream. -/
namespace IntegerMultBounds.Machine.CompactFallbackScalars
noncomputable section
open Sizes Parameters

def precision (n : ℕ) := 6*b n
def binaryDimension (n D : ℕ) := D*K n
def width (n D : ℕ) := precision n+4*binaryDimension n D+4
def polynomialCount (n : ℕ) := 2^ℓ n
def coefficientCount (n D : ℕ) := 2^(binaryDimension n D)*polynomialCount n
def nativePayload (n D : ℕ) := 2*(width n D+1)*polynomialCount n

theorem dimension_square (n : ℕ) : d n*d n≤b n := by
  have hb : (1:ℝ)≤b n := by exact_mod_cast one_le_b n
  have hd : (d n:ℝ)≤(b n:ℝ)^epsilon := Nat.floor_le (by positivity)
  have hs : (d n:ℝ)^2≤(b n:ℝ) := by
    calc
      (d n:ℝ)^2≤((b n:ℝ)^epsilon)^2 := pow_le_pow_left₀ (by positivity) hd 2
      _=(b n:ℝ)^(epsilon*2) := by rw [Real.rpow_mul (by positivity),Real.rpow_two]
      _≤(b n:ℝ)^1 := Real.rpow_le_rpow_of_exponent_le hb (by norm_num [epsilon])
      _=(b n:ℝ) := Real.rpow_one _
  exact_mod_cast (show (d n:ℝ)*(d n:ℝ)≤(b n:ℝ) by nlinarith)

theorem binaryDimension_le (n D : ℕ) (hD : D≤d n) : binaryDimension n D≤b n :=
  (Nat.mul_le_mul hD (CompactScalarAllowances.chunk_le_dimension n)).trans (dimension_square n)

theorem width_bounds (n D : ℕ) (hD : D≤d n) : b n≤width n D ∧ width n D≤14*b n := by
  have hb := one_le_b n
  have hd := binaryDimension_le n D hD
  unfold width precision
  omega

theorem width_reservation (n D : ℕ) :
    ButterflyGuard.width (ButterflyIndependentGuardHeaders.reservation (binaryDimension n D) (precision n))
      (binaryDimension n D)=width n D := by
  rw [ButterflyIndependentGuardHeaders.width_eq]
  rfl

theorem payload_bounds (n D : ℕ) (hD : D≤d n) :
    6*b n*polynomialCount n≤nativePayload n D ∧ nativePayload n D≤30*b n*polynomialCount n := by
  have hb := one_le_b n
  have hw := width_bounds n D hD
  have hlo : 6*b n≤2*(width n D+1) := by unfold width precision; omega
  have hhi : 2*(width n D+1)≤30*b n := by omega
  exact ⟨Nat.mul_le_mul_right _ hlo,Nat.mul_le_mul_right _ hhi⟩

theorem full_volume (n D : ℕ) :
    coefficientCount n D*(2*(width n D+1))=2^(D*K n)*nativePayload n D := by
  unfold coefficientCount binaryDimension nativePayload
  ring

end
end IntegerMultBounds.Machine.CompactFallbackScalars
