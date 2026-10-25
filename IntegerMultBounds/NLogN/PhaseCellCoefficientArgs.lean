module

public import IntegerMultBounds.NLogN.PhaseCellIntegerGenerators
public import Mathlib.Data.Rat.Floor

/-! # Unreduced natural arguments for the coefficient table machine

The exponential routine depends only on its rational argument, through a single
rounded pi multiple. No gcd or rational-normalization program is needed on tape.
-/

@[expose] public section

namespace IntegerMultBounds.NLogN.PhaseCellIntegerGenerators

open IntegerMultBounds.Resampling

theorem expPiNat_ratio (neg : Bool) (P a b c d : ℕ)
    (h : (a : ℚ) / b = (c : ℚ) / d) :
    WeightNat.expPiNat neg P a b = WeightNat.expPiNat neg P c d := by
  have hdiv (r : ℕ) : r * a / b = r * c / d := by
    have hQ : ((r * a : ℕ) : ℚ) / b = ((r * c : ℕ) : ℚ) / d := by
      push_cast
      simpa only [mul_div_assoc] using congrArg (fun x : ℚ => (r : ℚ) * x) h
    have hf := congrArg (fun x : ℚ => ⌊x⌋) hQ
    rw [Rat.floor_natCast_div_natCast, Rat.floor_natCast_div_natCast] at hf
    change ((r * a / b : ℕ) : ℤ) = ((r * c / d : ℕ) : ℤ) at hf
    exact_mod_cast hf
  unfold WeightNat.expPiNat
  rw [hdiv]

theorem correctedNumerator_ratio (P a b c d : ℕ)
    (h : (a : ℚ) / b = (c : ℚ) / d) :
    PhaseCellExpSample.numerator P a b = PhaseCellExpSample.numerator P c d := by
  unfold PhaseCellExpSample.numerator
  rw [expPiNat_ratio true P a b c d h]

/-- The natural Gaussian numerator is a product of the actual input dimensions. -/
theorem gaussianArg_ratio (s t u k : ℕ) :
    ((u * t * k ^ 2 : ℕ) : ℚ) / s =
      ((PhaseCellConcreteCoefficients.gaussianArg s t u k).aa : ℚ) /
        (PhaseCellConcreteCoefficients.gaussianArg s t u k).b := by
  have hq := PhaseCellRationalArgs.natural_encoding (PhaseCellRationalArgs.gaussianQ s t u k)
    (PhaseCellRationalArgs.gaussianQ_nonneg s t u k)
  change _ = ((PhaseCellRationalArgs.gaussianQ s t u k).num.toNat : ℚ) /
    (PhaseCellRationalArgs.gaussianQ s t u k).den
  rw [hq]
  simp only [PhaseCellRationalArgs.gaussianQ, Nat.cast_mul, Nat.cast_pow, Int.cast_natCast]
  ring

/-- The table machine may evaluate the unreduced argument directly. -/
theorem coefficientNumerator_gaussian {P s t u band k : ℕ} (hk : k ≠ 0) (hband : k ≤ band) :
    coefficientNumerator P s t u band k =
      (PhaseCellExpSample.numerator P (u * t * k ^ 2) s : ℤ) := by
  simp only [coefficientNumerator, hk, ite_false, hband, ite_true]
  rw [correctedNumerator_ratio P (u * t * k ^ 2) s _ _ (gaussianArg_ratio s t u k)]

/-- The uncorrected negative exponential fits with two guard bits. -/
theorem expPiNat_neg_lt_pow {P V : ℕ} (hP : 13 ≤ P) (hV : P + 2 ≤ V)
    (a b : ℕ) (hb : 0 < b) : WeightNat.expPiNat true P a b < 2 ^ V := by
  have he := (abs_le.mp (PhaseCellExpSample.raw_error P a b hP hb)).2
  have hx : Real.exp (-(Real.pi * a / b)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    apply neg_nonpos.mpr
    positivity
  have hpow : (0 : ℝ) < 2 ^ P := by positivity
  have hone : (1 : ℝ) ≤ 2 ^ P := one_le_pow₀ (by norm_num)
  have hxmul := mul_le_mul_of_nonneg_left hx hpow.le
  have hsmall : (WeightNat.expPiNat true P a b : ℝ) < (2 : ℝ) ^ (P + 2) := by
    rw [pow_add]
    norm_num
    nlinarith
  have hnat : WeightNat.expPiNat true P a b < 2 ^ (P + 2) := by exact_mod_cast hsmall
  exact hnat.trans_le (Nat.pow_le_pow_right (by decide) hV)

end IntegerMultBounds.NLogN.PhaseCellIntegerGenerators
