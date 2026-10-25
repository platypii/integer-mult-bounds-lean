module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardPrecision
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Choose the forward window and bound its growing factor

Use m=α(⌊√p⌋+1) and Γ=32p. The window covers the Gaussian truncation scale,
its growth stays linear in p, and both positive-exponential gates follow.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.NLogN

def chirpForwardWindow (p α : ℕ) : ℕ := α * (Nat.sqrt p + 1)

def chirpForwardGrowth (p : ℕ) : ℕ := 32 * p

def chirpForwardRingLog (p α : ℕ) : ℕ := Nat.clog 2 (7 * chirpForwardWindow p α)

/-- The selected window covers the required pα² scale and has controlled square. -/
theorem chirpForwardWindow_sq (p α : ℕ) (hp : 1 ≤ p) :
    p * α ^ 2 ≤ chirpForwardWindow p α ^ 2 ∧
      chirpForwardWindow p α ^ 2 ≤ 4 * p * α ^ 2 := by
  have hs : 1 ≤ Nat.sqrt p := by have := Nat.sqrt_pos.mpr hp; omega
  have hlo := Nat.lt_succ_sqrt' p
  have hhi := Nat.sqrt_le' p
  have hroot : (Nat.sqrt p + 1) ^ 2 ≤ 4 * p := by nlinarith
  constructor
  · unfold chirpForwardWindow
    rw [mul_pow]
    nlinarith [Nat.mul_le_mul_right (α ^ 2) (Nat.le_of_lt hlo)]
  · unfold chirpForwardWindow
    rw [mul_pow]
    nlinarith [Nat.mul_le_mul_right (α ^ 2) hroot]

/-- The window stays linear in p whenever α²≤p, as required by the outer precision budget. -/
theorem chirpForwardWindow_le (p α : ℕ) (hαp : α ^ 2 ≤ p) :
    chirpForwardWindow p α ≤ 2 * p := by
  have ha : α ≤ Nat.sqrt p := Nat.le_sqrt'.mpr hαp
  have hs := Nat.sqrt_le' p
  have hs' := Nat.sqrt_le_self p
  unfold chirpForwardWindow
  nlinarith [Nat.mul_le_mul_right (Nat.sqrt p + 1) ha]

/-- The selected ring length holds every linear-convolution record. -/
theorem chirpForwardRingLog_good (p α : ℕ) :
    7 * chirpForwardWindow p α ≤ 2 ^ chirpForwardRingLog p α := Nat.le_pow_clog (by decide) _

/-- The positive-exponential numerator has a p-linear relative bound throughout the window. -/
theorem chirpForwardWindow_argument (s t α p b : ℕ) (hst : s ≤ t) (hp : 1 ≤ p)
    (hb : b < chirpForwardWindow p α) :
    chirpEN s t b ≤ 4 * p * chirpED t α := by
  have hst2 : s * (t - s) ≤ t ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hst (Nat.sub_le t s)
  have hb2 : b ^ 2 ≤ chirpForwardWindow p α ^ 2 := Nat.pow_le_pow_left (by omega) _
  calc
    _ ≤ t ^ 2 * chirpForwardWindow p α ^ 2 := Nat.mul_le_mul hst2 hb2
    _ ≤ t ^ 2 * (4 * p * α ^ 2) := Nat.mul_le_mul_left _ (chirpForwardWindow_sq p α hp).2
    _ = _ := by unfold chirpED; ring

/-- Bound the real exponent without a floating-point certificate. -/
theorem chirpForwardWindow_exponent (s t α p b : ℕ) (hst : s ≤ t) (hp : 1 ≤ p)
    (ht : 0 < t) (hα : 0 < α) (hb : b < chirpForwardWindow p α) :
    Real.pi * (chirpEN s t b : ℝ) / (chirpED t α : ℝ) ≤ 16 * p := by
  have hd : (0 : ℝ) < chirpED t α := by unfold chirpED; positivity
  have hn : (chirpEN s t b : ℝ) ≤ 4 * p * (chirpED t α : ℝ) := by
    exact_mod_cast chirpForwardWindow_argument s t α p b hst hp hb
  apply (div_le_iff₀ hd).mpr
  have hπ : Real.pi ≤ 4 := Real.pi_lt_four.le
  nlinarith [mul_nonneg (by linarith : 0 ≤ 4 - Real.pi) (by positivity : (0 : ℝ) ≤ chirpEN s t b)]

/-- The selected Γ bounds every growing E factor in the generated row. -/
theorem chirpForwardGrowth_good (s t α p b : ℕ) (hs : 0 < s) (hst : s < t)
    (hα : 0 < α) (hp : 1 ≤ p) (hb : b < chirpForwardWindow p α) :
    chirpE s t (α : ℝ) b ≤ 2 ^ chirpForwardGrowth p := by
  rw [chirpE_eq_expPi s t α b hs hst hα]
  calc
    _ ≤ Real.exp (16 * (p : ℝ)) := Real.exp_le_exp.mpr
      (chirpForwardWindow_exponent s t α p b hst.le hp (by omega) hα hb)
    _ = (Real.exp 1) ^ (16 * p) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 (16 * p)
    _ ≤ (4 : ℝ) ^ (16 * p) := pow_le_pow_left₀ (Real.exp_pos _).le
      (Real.exp_one_lt_three.le.trans (by norm_num)) _
    _ = 2 ^ chirpForwardGrowth p := by
      unfold chirpForwardGrowth
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
      congr 1
      omega

/-- Integer evaluator gates hold for the full generated E row at the selected precision. -/
theorem chirpForwardWindow_machineGate (s t α p l b : ℕ) (hst : s ≤ t) (hp : 1 ≤ p)
    (hb : b < chirpForwardWindow p α) :
    4 * chirpEN s t b ≤
      (chirpForwardPrecision p (chirpForwardGrowth p) l - chirpForwardGrowth p - 1) * chirpED t α := by
  have hn := chirpForwardWindow_argument s t α p b hst hp hb
  have hq : 16 * p ≤ chirpForwardPrecision p (chirpForwardGrowth p) l - chirpForwardGrowth p - 1 := by
    unfold chirpForwardPrecision chirpForwardGrowth
    omega
  calc
    _ ≤ (16 * p) * chirpED t α := by nlinarith
    _ ≤ _ := Nat.mul_le_mul_right _ hq

/-- The selected ring exponent is at most p+4, so all output widths remain linear. -/
theorem chirpForwardRingLog_le (p α : ℕ) (hαp : α ^ 2 ≤ p) :
    chirpForwardRingLog p α ≤ p + 4 := by
  apply Nat.clog_le_of_le_pow
  have hm := chirpForwardWindow_le p α hαp
  have hp : p ≤ 2 ^ p := Nat.lt_two_pow_self.le
  have hpow : 2 ^ (p + 4) = 16 * 2 ^ p := by rw [pow_add]; ring
  rw [hpow]
  omega

/-- Precision and both signed word widths have fixed linear bounds in p. -/
theorem chirpForwardWidths_le (p α : ℕ) (hp : 1 ≤ p) (hαp : α ^ 2 ≤ p) :
    let l := chirpForwardRingLog p α
    let Γ := chirpForwardGrowth p
    let q := chirpForwardPrecision p Γ l
    q ≤ 83 * p ∧ q + l + Γ + 5 ≤ 125 * p ∧ p + l + Γ + 5 ≤ 43 * p := by
  have hl := chirpForwardRingLog_le p α hαp
  dsimp [chirpForwardPrecision, chirpForwardGrowth]
  omega

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
