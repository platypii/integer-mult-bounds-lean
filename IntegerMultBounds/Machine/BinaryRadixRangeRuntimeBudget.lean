import IntegerMultBounds.Machine.ArbitraryWidthOriginalTotalRun
import IntegerMultBounds.Machine.BinaryRadixRootEncoding

/-! Runtime-budget assembly for the actual radix machine and paid binary
range wrapper. This module bounds costs; machine composition is separate. -/
namespace IntegerMultBounds.Machine.BinaryRadixRangeRuntimeBudget
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open ArbitraryWidthHighLayout (originalDescriptor)

def rootDescriptor (P G B u : ℕ) := originalDescriptor P (RadixRangeDescriptors.exponent prime u) G B
def originalVolume (P G B u : ℕ) := RadixRangePadding.volume P (2^u) G B
def rootCost (P G B u : ℕ) (rh : Fin 6 → List Bool) :=
  ArbitraryWidthOriginalTotalRun.cost (rootDescriptor P G B u) rh

theorem root_positive (P G B u : ℕ) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) :
    (rootDescriptor P G B u).Positive :=
  ⟨hP,by change 0 < 1; decide,by change 0 < 1; decide,hG,hB⟩

theorem root_volume_bound (P G B u : ℕ) :
    volume prime (rootDescriptor P G B u) ≤ (prime*prime)*originalVolume P G B u := by
  rw [rootDescriptor,BinaryRadixRootEncoding.volume_eq]
  exact BinaryRadixRangePrepare.volume_bound prime P G B u Shared50ModularControl.prime_prime.two_le

theorem width_power_bound (u : ℕ) :
    ((max 1 (RadixRangeDescriptors.exponent prime u) : ℕ) : ℝ)^Parameters.tau ≤
      ((max 1 u : ℕ) : ℝ)^Parameters.tau := by
  apply Real.rpow_le_rpow (Nat.cast_nonneg _)
  · exact_mod_cast max_le_max_left 1 (RadixRangeDescriptors.exponent_le prime u Shared50ModularControl.prime_prime.two_le)
  · exact Shared50RecursiveBudgetBound.exponent_range.1.le

theorem root_uniform_bound : ∃ C : ℝ, 0 < C ∧ ∀ (P G B u : ℕ) (rh : Fin 6 → List Bool),
    0 < P → 0 < G → 0 < B → RecursiveDimensionBank.Headers (rootDescriptor P G B u) rh →
    (rootCost P G B u rh : ℝ) ≤ C*(originalVolume P G B u : ℝ)*((max 1 u : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := ArbitraryWidthOriginalTotalRun.uniform_bound
  have hprime : 0 < ((prime*prime : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos Shared50ModularControl.prime_prime.pos Shared50ModularControl.prime_prime.pos
  refine ⟨C*((prime*prime : ℕ) : ℝ),mul_pos hC hprime,?_⟩
  intro P G B u rh hP hG hB hrh
  have hb := hbound (rootDescriptor P G B u) rh (root_positive P G B u hP hG hB) hrh
  have hv : (volume prime (rootDescriptor P G B u) : ℝ) ≤
      ((prime*prime : ℕ) : ℝ)*(originalVolume P G B u : ℝ) := by
    exact_mod_cast root_volume_bound P G B u
  have hp := width_power_bound u
  have hrpow : 0 ≤ ((max 1 (RadixRangeDescriptors.exponent prime u) : ℕ) : ℝ)^Parameters.tau :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hscaled := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hC.le) hrpow
  have hco : 0 ≤ C*(((prime*prime : ℕ) : ℝ)*(originalVolume P G B u : ℝ)) :=
    mul_nonneg hC.le (mul_nonneg hprime.le (Nat.cast_nonneg _))
  have hwidth := mul_le_mul_of_nonneg_left hp hco
  change (rootCost P G B u rh : ℝ) ≤ _ at hb
  change (rootCost P G B u rh : ℝ) ≤ _
  calc
    _ ≤ C*(volume prime (rootDescriptor P G B u) : ℝ)*
        ((max 1 (RadixRangeDescriptors.exponent prime u) : ℕ) : ℝ)^Parameters.tau := hb
    _ ≤ C*(((prime*prime : ℕ) : ℝ)*(originalVolume P G B u : ℝ))*
        ((max 1 (RadixRangeDescriptors.exponent prime u) : ℕ) : ℝ)^Parameters.tau := hscaled
    _ ≤ C*(((prime*prime : ℕ) : ℝ)*(originalVolume P G B u : ℝ))*
        ((max 1 u : ℕ) : ℝ)^Parameters.tau := hwidth
    _ = _ := by ring

def overheadCoefficient := BinaryRadixRangePrepare.prepareConstant prime+80+54+BinaryRadixRangePrepare.finishConstant prime

def combinedCost (P G B u : ℕ) (rh : Fin 6 → List Bool) :=
  overheadCoefficient*originalVolume P G B u+rootCost P G B u rh+4

theorem uniform_bound : ∃ C : ℝ, 0 < C ∧ ∀ (P G B u : ℕ) (rh : Fin 6 → List Bool),
    0 < P → 0 < G → 0 < B → RecursiveDimensionBank.Headers (rootDescriptor P G B u) rh →
    (combinedCost P G B u rh : ℝ) ≤ C*(originalVolume P G B u : ℝ)*((max 1 u : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := root_uniform_bound
  have ho : 0 ≤ (overheadCoefficient : ℝ) := Nat.cast_nonneg _
  refine ⟨C+(overheadCoefficient : ℝ)+4,by linarith,?_⟩
  intro P G B u rh hP hG hB hrh
  have hb := hbound P G B u rh hP hG hB hrh
  have hVnat := lt_of_lt_of_le (Nat.two_pow_pos u) (BinaryRadixRangePrepare.range_le_volume P G B u hP hG hB)
  have hV : 1 ≤ (originalVolume P G B u : ℝ) := by exact_mod_cast hVnat
  have hp : 1 ≤ ((max 1 u : ℕ) : ℝ)^Parameters.tau := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 u) Shared50RecursiveBudgetBound.exponent_range.1.le
  have hVP : 1 ≤ (originalVolume P G B u : ℝ)*((max 1 u : ℕ) : ℝ)^Parameters.tau := by nlinarith
  have hlin := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (overheadCoefficient : ℝ)*(originalVolume P G B u : ℝ) from mul_nonneg ho (Nat.cast_nonneg _))
  unfold combinedCost
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith only [hb,hVP,hlin]

end
end IntegerMultBounds.Machine.BinaryRadixRangeRuntimeBudget
