import IntegerMultBounds.Machine.ArbitraryWidthHighExchangeJoin
import IntegerMultBounds.Machine.ArbitraryWidthHighSeparateShared
import IntegerMultBounds.Machine.ArbitraryWidthHighPaddedBudget
import IntegerMultBounds.Machine.ArbitraryWidthHighBudget

/-! Arithmetic assembly of the fully paid high-width stage budgets. This is
not an execution oracle: physical stage composition is a separate theorem.
The complete actual piece cost appears literally, including its controls. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighCost
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open ArbitraryWidthHighPrepare (highDepth)
open ArbitraryWidthHighLayout (originalDescriptor)
open ArbitraryWidthHighPaddedBudget (descriptor)

def movementCoefficient : ℕ := ArbitraryWidthHighExchangeJoin.coefficient+
  RadixHighBlockSeparateRun.coefficient prime

def cost (K P e G B : ℕ) (hs : Fin 6 → List Bool) : ℕ :=
  movementCoefficient*(highDepth prime e+1)*volume prime (originalDescriptor P e G B)+
  826*volume prime (descriptor P e G B)+
  ArbitraryWidthPieceRun.cost (descriptor P e G B) hs+
  K*volume prime (originalDescriptor P e G B)+5

def coefficient (K : ℕ) : ℝ :=
  (movementCoefficient : ℝ)*ArbitraryWidthHighBudget.constant prime Parameters.tau+
  2*ArbitraryWidthPieceCost.coefficient+(K : ℝ)+1657

theorem coefficient_positive (K : ℕ) : 0 < coefficient K := by
  have hc := ArbitraryWidthHighBudget.constant_positive prime Parameters.tau
    Shared50ModularControl.prime_prime.two_le Shared50RecursiveBudgetBound.exponent_range.1
  have hp := ArbitraryWidthPieceCost.coefficient_positive
  have hm : 0 ≤ (movementCoefficient : ℝ)*ArbitraryWidthHighBudget.constant prime Parameters.tau :=
    mul_nonneg (Nat.cast_nonneg _) hc.le
  have hk : 0 ≤ (K : ℝ) := Nat.cast_nonneg _
  unfold coefficient
  linarith only [hm,hp,hk]

/-- Every paid linear metadata coefficient and all high/low movement budgets
fit the unchanged certified exponent against the original full array volume. -/
theorem bound (K P e G B : ℕ) (hs : Fin 6 → List Bool)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hr : highDepth prime e < e)
    (hv : RecursiveDimensionBank.Headers (descriptor P e G B) hs) :
    (cost K P e G B hs : ℝ) ≤ coefficient K*
      (volume prime (originalDescriptor P e G B) : ℝ)*(e : ℝ)^Parameters.tau := by
  let V := volume prime (originalDescriptor P e G B)
  have hpositive : (originalDescriptor P e G B).Positive := ⟨hP,(by change 0 < 1; decide),(by change 0 < 1; decide),hG,hB⟩
  have hV : 0 < V := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le _ hpositive
  have he : 0 < e := by omega
  have hpower : 1 ≤ (e : ℝ)^Parameters.tau := Real.one_le_rpow (by exact_mod_cast he)
    Shared50RecursiveBudgetBound.exponent_range.1.le
  have hmovement := ArbitraryWidthHighBudget.movement_bound prime e V movementCoefficient Parameters.tau
    Shared50ModularControl.prime_prime.two_le he Shared50RecursiveBudgetBound.exponent_range.1
  have hpiece := ArbitraryWidthHighPaddedBudget.piece_cost P e G B hs hP hG hB hr hv
  have hpad : (volume prime (descriptor P e G B) : ℝ) ≤ 2*(V : ℝ) := by
    exact_mod_cast ArbitraryWidthHighPaddedBudget.volume_le P e G B hr.le
  have hVreal : (1 : ℝ) ≤ V := by exact_mod_cast hV
  have hlinear := mul_le_mul_of_nonneg_left hpower
    (show 0 ≤ ((K : ℝ)+1657)*(V : ℝ) from mul_nonneg (by positivity) (Nat.cast_nonneg _))
  unfold cost coefficient
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  change (movementCoefficient : ℝ)*((highDepth prime e : ℝ)+1)*(V : ℝ)+
    826*(volume prime (descriptor P e G B) : ℝ)+
    (ArbitraryWidthPieceRun.cost (descriptor P e G B) hs : ℝ)+(K : ℝ)*(V : ℝ)+5 ≤ _
  dsimp only [V] at hmovement hpad hlinear hVreal ⊢
  nlinarith only [hmovement,hpiece,hpad,hlinear,hVreal]

end
end IntegerMultBounds.Machine.ArbitraryWidthHighCost
