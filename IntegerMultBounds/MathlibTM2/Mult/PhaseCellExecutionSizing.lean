module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedRun

/-! # A controller-compatible precision choice for executed cell arithmetic

A working precision divisible by four lets quarter-counting recover the
normalization exponent while paying the amplified interior-stage error. The larger source
allowance preserves the given RHS bound and satisfies every proved cell error
and final word-width requirement. Uniform line-cost matching remains open.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

/-- Declared source allowance, including room for stage accuracy. -/
def sourceExponent (l j rhsExp : ℕ) : ℕ := rhsExp + 2 * l + j + 5

def executionExponent (p l j rhsExp : ℕ) : ℕ := inputExponent p (sourceExponent l j rhsExp)

def executionPrecision (p l j rhsExp : ℕ) : ℕ := 4 * executionExponent p l j rhsExp

def executionStagePrecision (p l j rhsExp : ℕ) : ℕ := 2 * executionExponent p l j rhsExp

def executionWidth (p l j rhsExp : ℕ) : ℕ := 8 * executionExponent p l j rhsExp + 8

theorem execution_precision_bound (p l j rhsExp : ℕ) :
    inputExponent p (sourceExponent l j rhsExp) + 2 * l + j + 5 ≤ executionPrecision p l j rhsExp := by
  unfold executionPrecision executionExponent inputExponent sourceExponent
  omega

theorem execution_width_bound (p l j rhsExp : ℕ) :
    executionPrecision p l j rhsExp + inputExponent p (sourceExponent l j rhsExp) + 2 * l + 6 ≤
      executionWidth p l j rhsExp := by
  unfold executionWidth executionPrecision executionExponent inputExponent sourceExponent
  omega

theorem execution_input_width (p l j rhsExp : ℕ) :
    executionPrecision p l j rhsExp + executionExponent p l j rhsExp + 4 ≤ executionWidth p l j rhsExp := by
  unfold executionPrecision executionWidth
  omega

/-- Stage accuracy exceeds normalization by enough bits to pay the interior
magnitude and row-length amplification, with seven guard bits. -/
theorem execution_error_bits (p l j rhsExp : ℕ) :
    executionExponent p l j rhsExp + l + j + 7 ≤ executionStagePrecision p l j rhsExp := by
  unfold executionStagePrecision executionExponent inputExponent sourceExponent
  omega

theorem execution_stage_bound (p l j rhsExp : ℕ) :
    inputExponent p (sourceExponent l j rhsExp) + 2 * l + executionStagePrecision p l j rhsExp + 5 ≤
      executionPrecision p l j rhsExp := by
  unfold executionPrecision executionStagePrecision executionExponent inputExponent sourceExponent
  omega

/-- Pay the complete rounded-cell error, including its normalization factor.
The ambient parameter is not replaced by a halo length in any line estimate. -/
theorem cell_error_budget {L l b cExp stage j : ℕ} (hL : L ≤ 2 ^ l) (hc : cExp ≤ b)
    (hbits : b + l + j + 7 ≤ stage) :
    1 / (2 : ℝ) ^ stage + 64 * L * (1 / (2 : ℝ) ^ stage) * (2 : ℝ) ^ b +
      2 * (1 / (2 : ℝ) ^ stage + (2 : ℝ) ^ cExp * (1 / (2 : ℝ) ^ stage)) ≤
        1 / (2 : ℝ) ^ j := by
  have hL' : (L : ℝ) ≤ (2 : ℝ) ^ l := by exact_mod_cast hL
  have hc' : (2 : ℝ) ^ cExp ≤ (2 : ℝ) ^ b := pow_le_pow_right₀ (by norm_num) hc
  have hb : (1 : ℝ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  have hl : (1 : ℝ) ≤ 2 ^ l := one_le_pow₀ (by norm_num)
  have hprod : (1 : ℝ) ≤ (2 : ℝ) ^ l * (2 : ℝ) ^ b := by nlinarith
  have hbp : (2 : ℝ) ^ b ≤ (2 : ℝ) ^ l * (2 : ℝ) ^ b := by nlinarith
  have hLP : (L : ℝ) * (2 : ℝ) ^ b ≤ (2 : ℝ) ^ l * (2 : ℝ) ^ b :=
    mul_le_mul_of_nonneg_right hL' (by positivity)
  have hnum : 3 + 64 * (L : ℝ) * (2 : ℝ) ^ b + 2 * (2 : ℝ) ^ cExp ≤ (2 : ℝ) ^ (b + l + 7) := by
    calc
      _ ≤ 128 * (2 : ℝ) ^ l * (2 : ℝ) ^ b := by nlinarith
      _ = _ := by simp only [pow_add]; norm_num; ring
  have hdiv : (3 + 64 * (L : ℝ) * (2 : ℝ) ^ b + 2 * (2 : ℝ) ^ cExp) / (2 : ℝ) ^ stage ≤
      1 / (2 : ℝ) ^ j := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    calc
      _ ≤ (2 : ℝ) ^ (b + l + 7) * (2 : ℝ) ^ j :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
      _ ≤ 1 * (2 : ℝ) ^ stage := by
        rw [← pow_add, one_mul]
        apply pow_le_pow_right₀ (by norm_num)
        omega
  convert hdiv using 1; ring

theorem execution_cell_error (p l j rhsExp L : ℕ) (hpad : L + L ≤ 2 ^ l + 1) :
    let η := 1 / (2 : ℝ) ^ executionStagePrecision p l j rhsExp
    η + 64 * L * η * (2 : ℝ) ^ executionExponent p l j rhsExp +
      2 * (η + (2 : ℝ) ^ sourceExponent l j rhsExp * η) ≤ 1 / (2 : ℝ) ^ j := by
  have hpow : 0 < (2 : ℕ) ^ l := by positivity
  apply cell_error_budget (L := L) (l := l) (b := executionExponent p l j rhsExp)
    (cExp := sourceExponent l j rhsExp) (stage := executionStagePrecision p l j rhsExp) (j := j)
    (by omega : L ≤ 2 ^ l) ?_ (execution_error_bits p l j rhsExp)
  unfold executionExponent inputExponent
  omega

/-- The actual-arithmetic validity theorem accepts the quarter-count precision choice,
without a new stage-error assumption or a stronger bound on the actual RHS. -/
theorem executedRun_sized_valid {A M L s t p u l j rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hA : 4 ≤ A) (hp : 0 < p) (hst : s ≤ t) (hu : 1 ≤ u) (hαu : α ^ 2 = (u : ℝ))
    (hθ : 0 < (t : ℝ) / s - 1) (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1)) (hbudget : α ^ 2 * d ≤ p)
    (hL : 0 < L) (hpad : L + L ≤ 2 ^ l + 1) (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < M, ∀ k, ‖value (executionPrecision p l j rhsExp) (C n k)‖ ≤ (2 : ℝ) ^ rhsExp)
    (n : Fin M) (tail : List (Fin (A + 4))) :
    (executedRun s t p u (executionPrecision p l j rhsExp) l (executionWidth p l j rhsExp) M L (executionStagePrecision p l j rhsExp)
      (sourceExponent l j rhsExp) lo C n tail).Valid s t p u (lo n) L
      (fun k => (value (executionPrecision p l j rhsExp) (C n k)).re) (1 / (2 : ℝ) ^ executionStagePrecision p l j rhsExp)
      ((2 : ℝ) ^ executionExponent p l j rhsExp) := by
  apply executedRun_valid hA (execution_width_bound p l j rhsExp) hp hst hu hαu hθ hgap hbudget
    hL (execution_stage_bound p l j rhsExp) hpad lo C ?_ n tail
  intro m hm k
  exact (hC m hm k).trans (pow_le_pow_right₀ (by norm_num) (by unfold sourceExponent; omega))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
