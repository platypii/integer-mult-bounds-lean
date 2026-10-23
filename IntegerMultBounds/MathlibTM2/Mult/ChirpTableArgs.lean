module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpRing
public import IntegerMultBounds.Resampling.WeightNat
import Mathlib.Algebra.Order.Floor.Ring

/-! # Integer arguments for executable chirp coefficient tables

All three chirp factors are exponentials of rational multiples of pi when the resampling
parameter is a natural number. Compute their nonnegative numerators and denominators in
integers/naturals, including the block's floor offset, before using the existing evaluator.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.NLogN

/-- The cyclic window start, computed by natural division and signed subtraction. -/
def chirpStart (s t m k0 : ℕ) : ℤ := ((s * k0 / t : ℕ) : ℤ) - m

/-- The signed distance numerator `t(j0+a)-s k0`. -/
def chirpDelta (s t m k0 : ℕ) (a : ℤ) : ℤ :=
  (t : ℤ) * (chirpStart s t m k0 + a) - s * k0

def chirpSquare (s t m k0 : ℕ) (a : ℤ) : ℕ := (chirpDelta s t m k0 a ^ 2).toNat

def chirpGN (s t m k0 a : ℕ) : ℕ := (t - s) * chirpSquare s t m k0 a

def chirpKN (s t m k0 : ℕ) (a : ℤ) : ℕ := s * chirpSquare s t m k0 a

def chirpKD (t α : ℕ) : ℕ := t ^ 3 * α ^ 2

def chirpEN (s t b : ℕ) : ℕ := s * (t - s) * b ^ 2

def chirpED (t α : ℕ) : ℕ := t ^ 2 * α ^ 2

/-- The integer-computed start is exactly the analytic floor offset. -/
theorem chirpStart_eq (s t m k0 : ℕ) : chirpStart s t m k0 = blockIn s t m k0 := by
  unfold chirpStart blockIn
  rw [show (s : ℝ) * k0 / t = ((s * k0 : ℕ) : ℝ) / (t : ℕ) by push_cast; ring,
    Int.floor_div_natCast, Int.floor_natCast]
  push_cast
  rfl

theorem chirpDelta_cast (s t m k0 : ℕ) (a : ℤ) :
    (chirpDelta s t m k0 a : ℝ) = (t : ℝ) * ((blockIn s t m k0 : ℝ) + a) - s * k0 := by
  simp only [chirpDelta, chirpStart_eq, Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_natCast]

theorem chirpSquare_cast (s t m k0 : ℕ) (a : ℤ) :
    (chirpSquare s t m k0 a : ℝ) = ((t : ℝ) * ((blockIn s t m k0 : ℝ) + a) - s * k0) ^ 2 := by
  have h : ((chirpSquare s t m k0 a : ℕ) : ℤ) = chirpDelta s t m k0 a ^ 2 :=
    Int.toNat_of_nonneg (sq_nonneg _)
  have hc : (chirpSquare s t m k0 a : ℝ) = ((chirpDelta s t m k0 a ^ 2 : ℤ) : ℝ) := by
    exact_mod_cast h
  rw [hc, Int.cast_pow, chirpDelta_cast]

/-- The input table is one negative exponential with natural arguments. -/
theorem chirpG_eq_expPi (s t α m k0 a : ℕ) (hs : 0 < s) (hst : s < t) (hα : 0 < α) :
    chirpG s t (α : ℝ) m k0 a =
      Real.exp (-(Real.pi * (chirpGN s t m k0 a : ℝ) / (chirpKD t α : ℝ))) := by
  have hs0 : (s : ℝ) ≠ 0 := by positivity
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
  have hα0 : (α : ℝ) ≠ 0 := by positivity
  simp only [chirpG, chirpGN, chirpKD, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hst.le,
    chirpSquare_cast, Int.cast_natCast, chirpLam, chirpSig, chirpTheta, chirpY]
  congr 1
  field_simp
  ring

/-- The shifted kernel table uses the same denominator as the input table. -/
theorem chirpK_eq_expPi (s t α m k0 : ℕ) (a : ℤ) (hs : 0 < s) (ht : 0 < t) (hα : 0 < α) :
    chirpK s t (α : ℝ) m k0 a =
      Real.exp (-(Real.pi * (chirpKN s t m k0 a : ℝ) / (chirpKD t α : ℝ))) := by
  have hs0 : (s : ℝ) ≠ 0 := by positivity
  have ht0 : (t : ℝ) ≠ 0 := by positivity
  have hα0 : (α : ℝ) ≠ 0 := by positivity
  simp only [chirpK, chirpKN, chirpKD, Nat.cast_mul, Nat.cast_pow, chirpSquare_cast,
    chirpLam, chirpSig, chirpY]
  congr 1
  field_simp
  ring

/-- The growing output factor is one positive exponential with natural arguments. -/
theorem chirpE_eq_expPi (s t α b : ℕ) (hs : 0 < s) (hst : s < t) (hα : 0 < α) :
    chirpE s t (α : ℝ) b = Real.exp (Real.pi * (chirpEN s t b : ℝ) / (chirpED t α : ℝ)) := by
  have hs0 : (s : ℝ) ≠ 0 := by positivity
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
  have hα0 : (α : ℝ) ≠ 0 := by positivity
  simp only [chirpE, chirpEN, chirpED, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hst.le,
    chirpLam, chirpSig, chirpTheta]
  congr 1
  field_simp

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
