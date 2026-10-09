import IntegerMultBounds.Machine.ArbitraryWidthHighCommonDispatch

/-! The genuine high/fallback runtime dispatch preserves the certified
exponent uniformly; a fixed mathematical cutoff bounds the fallback widths. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighCommonDispatchCost
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open ArbitraryWidthHighPrepare (highDepth rounded)
open ArbitraryWidthHighCommonDispatch (guard cost)

def fallbackCoefficient (cutoff : ℕ) := ArbitraryWidthElementary.coefficient*(cutoff+1)+116
def selectorCoefficient (cutoff : ℕ) := 21*ArbitraryWidthHighMetadataBudget.constant prime cutoff+1

def coefficient (cutoff : ℕ) : ℝ := ArbitraryWidthHighPreparedRun.coefficient+
  (fallbackCoefficient cutoff : ℝ)+(selectorCoefficient cutoff : ℝ)

theorem coefficient_positive (cutoff : ℕ) : 0 < coefficient cutoff := by
  have h := ArbitraryWidthHighPreparedRun.coefficient_positive
  unfold coefficient
  positivity

/-- The actual descriptor comparison and its branch-entry transition are
linear in the original array volume, including bounded-width exceptions. -/
theorem selector_bound (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ highDepth prime n ∧ highDepth prime n < n)
    (d : Descriptor) (hs : Fin 6 → List Bool) (hp : d.Positive)
    (hv : RecursiveDimensionBank.Headers d hs) :
    ArbitraryWidthHighBranch.cost (ArbitraryWidthHighPrepare.words prime d.width 2) (hs 3)+1 ≤
      selectorCoefficient cutoff*volume prime d := by
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le d hp
  have hc := ArbitraryWidthHighCommonSelector.cost_bound prime cutoff d hs
    Shared50ModularControl.prime_prime.two_le hp hv (fun n hn => (hcut n hn).2.le)
  unfold selectorCoefficient
  nlinarith

theorem fallback_bound (cutoff : ℕ) (d : Descriptor) (hp : d.Positive) (he : d.width ≤ cutoff) :
    ArbitraryWidthHighCommonFallbackBody.cost d ≤ fallbackCoefficient cutoff*volume prime d := by
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le d hp
  have hm := Nat.mul_le_mul_right (volume prime d)
    (Nat.mul_le_mul_left ArbitraryWidthElementary.coefficient (Nat.add_le_add_right he 1))
  unfold ArbitraryWidthHighCommonFallbackBody.cost fallbackCoefficient
  nlinarith

/-- A single fixed coefficient bounds the actual selected runtime for every
positive-width original layout. Both branches include their private-header
setup and cleanup; the selector itself runs and erases its flag. -/
theorem bound (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ highDepth prime n ∧ highDepth prime n < n)
    (d : Descriptor) (hs : Fin 6 → List Bool) (hp : d.Positive)
    (hv : RecursiveDimensionBank.Headers d hs) (he : 0 < d.width) :
    (cost d hs : ℝ) ≤ coefficient cutoff*(volume prime d : ℝ)*(d.width : ℝ)^Parameters.tau := by
  have hpower : 1 ≤ (d.width : ℝ)^Parameters.tau := Real.one_le_rpow (by exact_mod_cast he)
    Shared50RecursiveBudgetBound.exponent_range.1.le
  have hsel : ((ArbitraryWidthHighBranch.cost (ArbitraryWidthHighPrepare.words prime d.width 2) (hs 3)+1 : ℕ) : ℝ) ≤
      (selectorCoefficient cutoff : ℝ)*(volume prime d : ℝ) := by
    exact_mod_cast selector_bound cutoff hcut d hs hp hv
  have hsel' := mul_le_mul_of_nonneg_left hpower
    (show 0 ≤ (selectorCoefficient cutoff : ℝ)*(volume prime d : ℝ) by positivity)
  have hhigh : 0 ≤ ArbitraryWidthHighPreparedRun.coefficient*(volume prime d : ℝ)*(d.width : ℝ)^Parameters.tau := by
    have hc := ArbitraryWidthHighPreparedRun.coefficient_positive
    positivity
  have hfall : 0 ≤ (fallbackCoefficient cutoff : ℝ)*(volume prime d : ℝ)*(d.width : ℝ)^Parameters.tau := by positivity
  by_cases hg : guard d
  · have hb := ArbitraryWidthHighCommonHighBody.cost_bound d hs hp hv hg.2
    unfold cost
    rw [ite_eq_left hg]
    simp only [Nat.cast_add,Nat.cast_one] at hsel ⊢
    unfold coefficient
    nlinarith only [hsel,hsel',hb,hfall]
  · have hw : d.width ≤ cutoff := by
      by_contra hn
      exact hg (hcut d.width (by omega))
    have hb : (ArbitraryWidthHighCommonFallbackBody.cost d : ℝ) ≤
        (fallbackCoefficient cutoff : ℝ)*(volume prime d : ℝ) := by
      exact_mod_cast fallback_bound cutoff d hp hw
    have hb' := mul_le_mul_of_nonneg_left hpower
      (show 0 ≤ (fallbackCoefficient cutoff : ℝ)*(volume prime d : ℝ) by positivity)
    unfold cost
    rw [ite_eq_right hg]
    simp only [Nat.cast_add,Nat.cast_one] at hsel ⊢
    unfold coefficient
    nlinarith only [hsel,hsel',hb,hb',hhigh]

/-- The finite fallback cutoff exists for the actual runtime highDepth
selector, so the genuine combined dispatch has one uniform certified bound. -/
theorem uniform_bound : ∃ C : ℝ, 0 < C ∧ ∀ (d : Descriptor) (hs : Fin 6 → List Bool),
    d.Positive → RecursiveDimensionBank.Headers d hs → 0 < d.width →
    (cost d hs : ℝ) ≤ C*(volume prime d : ℝ)*(d.width : ℝ)^Parameters.tau := by
  obtain ⟨cutoff,hcut⟩ := ArbitraryWidthHighGuard.bounded_fallback prime Shared50ModularControl.prime_prime.two_le
  exact ⟨coefficient cutoff,coefficient_positive cutoff,fun d hs hp hv he => bound cutoff hcut d hs hp hv he⟩

end
end IntegerMultBounds.Machine.ArbitraryWidthHighCommonDispatchCost
