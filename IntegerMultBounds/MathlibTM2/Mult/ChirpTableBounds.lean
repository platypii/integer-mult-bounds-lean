module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableEmit
import Mathlib.Analysis.Real.Pi.Bounds

/-! # One word-size envelope for chirp table generation

Bound dimensions and row indices by `B`. The same polynomial envelope pays for all
argument intermediates and the exponential evaluator's scaled numerator.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- A common executable word-size and evaluator-precision gate. -/
structure ChirpTableSize (W q B : ℕ) : Prop where
  base : 1 ≤ B
  precision : 13 ≤ q
  word : 13 * q + 8 ≤ W
  budget : 4 * B ^ 8 * 2 ^ (5 * q + 2) < 2 ^ W

theorem ChirpTableSize.cap {W q B : ℕ} (h : ChirpTableSize W q B)
    (c k : ℕ) (hc : c ≤ 4) (hk : k ≤ 8) : c * B ^ k < 2 ^ W := by
  calc c * B ^ k ≤ 4 * B ^ 8 := Nat.mul_le_mul hc (Nat.pow_le_pow_right h.base hk)
    _ = (4 * B ^ 8) * 1 := by omega
    _ ≤ (4 * B ^ 8) * 2 ^ (5 * q + 2) := Nat.mul_le_mul_left _ (Nat.two_pow_pos _)
    _ < 2 ^ W := h.budget

theorem chirpDistanceSquare_le {B s t offset k0 a : ℕ} (hB : 1 ≤ B)
    (hs : s ≤ B) (ht : t ≤ B) (ho : offset ≤ B) (hk : k0 ≤ B) (ha : a ≤ B) :
    chirpDistanceSquare s t offset k0 a ≤ 4 * B ^ 6 := by
  have hB2 : B ≤ B ^ 2 := by
    calc B = B ^ 1 := by simp
      _ ≤ B ^ 2 := Nat.pow_le_pow_right hB (by decide)
  have hsk : s * k0 ≤ B ^ 2 := by
    calc s * k0 ≤ B * B := Nat.mul_le_mul hs hk
      _ = _ := by ring
  have hto : t * offset ≤ B ^ 2 := by
    calc t * offset ≤ B * B := Nat.mul_le_mul ht ho
      _ = _ := by ring
  have hadd : s * k0 / t + a ≤ 2 * B ^ 2 := by have := Nat.div_le_self (s * k0) t; omega
  have hP : t * (s * k0 / t + a) ≤ 2 * B ^ 3 := by
    calc _ ≤ B * (2 * B ^ 2) := Nat.mul_le_mul ht hadd
      _ = _ := by ring
  have hN : s * k0 + t * offset ≤ 2 * B ^ 3 := by
    have hpow := Nat.pow_le_pow_right hB (by decide : 2 ≤ 3)
    omega
  have hd : (if t * (s * k0 / t + a) < s * k0 + t * offset then
      s * k0 + t * offset - t * (s * k0 / t + a)
    else t * (s * k0 / t + a) - (s * k0 + t * offset)) ≤ 2 * B ^ 3 := by
    split_ifs <;> omega
  unfold chirpDistanceSquare
  calc _ ≤ (2 * B ^ 3) ^ 2 := Nat.pow_le_pow_left hd 2
    _ = _ := by ring

/-- All concrete no-overflow inequalities consumed by the negative argument program. -/
structure ChirpArgumentBounds (W : ℕ) (kernel : Bool) (s t α offset k0 a : ℕ) : Prop where
  ordered : s ≤ t
  dimT : t < 2 ^ W
  one : 1 < 2 ^ W
  originProduct : s * k0 < 2 ^ W
  shiftedIndex : s * k0 / t + a < 2 ^ W
  positiveDistance : t * (s * k0 / t + a) < 2 ^ W
  offsetProduct : t * offset < 2 ^ W
  negativeDistance : s * k0 + t * offset < 2 ^ W
  distanceSquare : chirpDistanceSquare s t offset k0 a < 2 ^ W
  numerator : chirpArgumentN kernel s t offset k0 a < 2 ^ W
  tSquared : t * t < 2 ^ W
  tCubed : t * t * t < 2 ^ W
  alphaSquared : α * α < 2 ^ W
  denominator : t * t * t * (α * α) < 2 ^ W

/-- The single size envelope discharges every argument-program overflow check. -/
theorem ChirpTableSize.arguments {W q B : ℕ} (h : ChirpTableSize W q B)
    (kernel : Bool) (s t α offset k0 a : ℕ) (hst : s ≤ t)
    (hs : s ≤ B) (ht : t ≤ B) (hα : α ≤ B) (ho : offset ≤ B) (hk : k0 ≤ B) (ha : a ≤ B) :
    ChirpArgumentBounds W kernel s t α offset k0 a := by
  have hB2 : B ≤ B ^ 2 := by
    calc B = B ^ 1 := by simp
      _ ≤ B ^ 2 := Nat.pow_le_pow_right h.base (by decide)
  have hsk : s * k0 ≤ B ^ 2 := by
    calc _ ≤ B * B := Nat.mul_le_mul hs hk
      _ = _ := by ring
  have hto : t * offset ≤ B ^ 2 := by
    calc _ ≤ B * B := Nat.mul_le_mul ht ho
      _ = _ := by ring
  have hadd : s * k0 / t + a ≤ 2 * B ^ 2 := by have := Nat.div_le_self (s * k0) t; omega
  have hP : t * (s * k0 / t + a) ≤ 2 * B ^ 3 := by
    calc _ ≤ B * (2 * B ^ 2) := Nat.mul_le_mul ht hadd
      _ = _ := by ring
  have hN : s * k0 + t * offset ≤ 2 * B ^ 2 := by omega
  have hsq := chirpDistanceSquare_le h.base hs ht ho hk ha
  have hfactor : (if kernel then s else t - s) ≤ B := by split <;> omega
  have hnum : chirpArgumentN kernel s t offset k0 a ≤ 4 * B ^ 7 := by
    unfold chirpArgumentN
    calc _ ≤ B * (4 * B ^ 6) := Nat.mul_le_mul hfactor hsq
      _ = _ := by ring
  have ht2 : t * t ≤ B ^ 2 := by
    calc _ ≤ B * B := Nat.mul_le_mul ht ht
      _ = _ := by ring
  have ht3 : t * t * t ≤ B ^ 3 := by
    calc _ ≤ B ^ 2 * B := Nat.mul_le_mul ht2 ht
      _ = _ := by ring
  have hα2 : α * α ≤ B ^ 2 := by
    calc _ ≤ B * B := Nat.mul_le_mul hα hα
      _ = _ := by ring
  have hden : t * t * t * (α * α) ≤ B ^ 5 := by
    calc _ ≤ B ^ 3 * B ^ 2 := Nat.mul_le_mul ht3 hα2
      _ = _ := by ring
  refine ⟨hst, ht.trans_lt ?_, ?_, hsk.trans_lt ?_, hadd.trans_lt ?_, hP.trans_lt ?_,
    hto.trans_lt ?_, hN.trans_lt ?_, hsq.trans_lt ?_, hnum.trans_lt ?_, ht2.trans_lt ?_,
    ht3.trans_lt ?_, hα2.trans_lt ?_, hden.trans_lt ?_⟩
  · simpa using h.cap 1 1 (by decide) (by decide)
  · simpa using h.cap 1 0 (by decide) (by decide)
  · simpa using h.cap 1 2 (by decide) (by decide)
  · exact h.cap 2 2 (by decide) (by decide)
  · exact h.cap 2 3 (by decide) (by decide)
  · simpa using h.cap 1 2 (by decide) (by decide)
  · exact h.cap 2 2 (by decide) (by decide)
  · exact h.cap 4 6 (by decide) (by decide)
  · exact h.cap 4 7 (by decide) (by decide)
  · simpa using h.cap 1 2 (by decide) (by decide)
  · simpa using h.cap 1 3 (by decide) (by decide)
  · simpa using h.cap 1 2 (by decide) (by decide)
  · simpa using h.cap 1 5 (by decide) (by decide)

/-- The same envelope also pays for the evaluator's numerator scaling. -/
theorem ChirpTableSize.negativeNumerator {W q B : ℕ} (h : ChirpTableSize W q B)
    (kernel : Bool) (s t offset k0 a : ℕ)
    (hs : s ≤ B) (ht : t ≤ B) (ho : offset ≤ B) (hk : k0 ≤ B) (ha : a ≤ B) :
    chirpArgumentN kernel s t offset k0 a * 2 ^ (5 * q + 2) < 2 ^ W := by
  have hsq := chirpDistanceSquare_le h.base hs ht ho hk ha
  have hf : (if kernel then s else t - s) ≤ B := by split <;> omega
  have hn : chirpArgumentN kernel s t offset k0 a ≤ 4 * B ^ 8 := by
    unfold chirpArgumentN
    calc _ ≤ B * (4 * B ^ 6) := Nat.mul_le_mul hf hsq
      _ = 4 * B ^ 7 := by ring
      _ ≤ 4 * B ^ 8 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right h.base (by decide))
  exact (Nat.mul_le_mul_right _ hn).trans_lt h.budget

/-- An explicit word width, linear in precision and in the dimension bit length. -/
def chirpTableWord (q B : ℕ) : ℕ := 13 * q + 8 + 8 * B.size + 4

theorem chirpTableWord_size (q B : ℕ) (hq : 13 ≤ q) (hB : 1 ≤ B) :
    ChirpTableSize (chirpTableWord q B) q B := by
  refine ⟨hB, hq, by unfold chirpTableWord; omega, ?_⟩
  have hp : B ^ 8 < (2 ^ B.size) ^ 8 := Nat.pow_lt_pow_left (Nat.lt_size_self B) (by decide)
  have he : 4 * (2 ^ B.size) ^ 8 * 2 ^ (5 * q + 2) = 2 ^ (8 * B.size + 5 * q + 4) := by
    rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    omega
  calc
    _ < 4 * (2 ^ B.size) ^ 8 * 2 ^ (5 * q + 2) :=
      Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left hp (by decide)) (Nat.two_pow_pos _)
    _ = 2 ^ (8 * B.size + 5 * q + 4) := he
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold chirpTableWord; omega)

/-- All no-overflow checks consumed by the positive output argument generator. -/
structure ChirpOutputBounds (W s t α b : ℕ) : Prop where
  ordered : s ≤ t
  dimT : t < 2 ^ W
  indexSquared : b * b < 2 ^ W
  difference : s * (t - s) < 2 ^ W
  numerator : s * (t - s) * (b * b) < 2 ^ W
  tSquared : t * t < 2 ^ W
  alphaSquared : α * α < 2 ^ W
  denominator : t * t * (α * α) < 2 ^ W

theorem ChirpTableSize.output {W q B : ℕ} (h : ChirpTableSize W q B)
    (s t α b : ℕ) (hst : s ≤ t) (hs : s ≤ B) (ht : t ≤ B) (hα : α ≤ B) (hb : b ≤ B) :
    ChirpOutputBounds W s t α b := by
  have hb2 : b * b ≤ B ^ 2 := by
    calc _ ≤ B * B := Nat.mul_le_mul hb hb
      _ = _ := by ring
  have hdiff : s * (t - s) ≤ B ^ 2 := by
    calc _ ≤ B * B := Nat.mul_le_mul hs ((Nat.sub_le _ _).trans ht)
      _ = _ := by ring
  have hn : s * (t - s) * (b * b) ≤ B ^ 4 := by
    calc _ ≤ B ^ 2 * B ^ 2 := Nat.mul_le_mul hdiff hb2
      _ = _ := by ring
  have ht2 : t * t ≤ B ^ 2 := by
    calc _ ≤ B * B := Nat.mul_le_mul ht ht
      _ = _ := by ring
  have hα2 : α * α ≤ B ^ 2 := by
    calc _ ≤ B * B := Nat.mul_le_mul hα hα
      _ = _ := by ring
  have hden : t * t * (α * α) ≤ B ^ 4 := by
    calc _ ≤ B ^ 2 * B ^ 2 := Nat.mul_le_mul ht2 hα2
      _ = _ := by ring
  refine ⟨hst, ht.trans_lt ?_, hb2.trans_lt ?_, hdiff.trans_lt ?_, hn.trans_lt ?_,
    ht2.trans_lt ?_, hα2.trans_lt ?_, hden.trans_lt ?_⟩
  · simpa using h.cap 1 1 (by decide) (by decide)
  · simpa using h.cap 1 2 (by decide) (by decide)
  · simpa using h.cap 1 2 (by decide) (by decide)
  · simpa using h.cap 1 4 (by decide) (by decide)
  · simpa using h.cap 1 2 (by decide) (by decide)
  · simpa using h.cap 1 2 (by decide) (by decide)
  · simpa using h.cap 1 4 (by decide) (by decide)

theorem ChirpTableSize.outputNumerator {W q B : ℕ} (h : ChirpTableSize W q B)
    (s t b : ℕ) (hs : s ≤ B) (ht : t ≤ B) (hb : b ≤ B) :
    chirpEN s t b * 2 ^ (5 * q + 2) < 2 ^ W := by
  have hn : chirpEN s t b ≤ B ^ 4 := by
    unfold chirpEN
    calc
      _ ≤ B * B * B ^ 2 := Nat.mul_le_mul (Nat.mul_le_mul hs ((Nat.sub_le _ _).trans ht))
        (Nat.pow_le_pow_left hb 2)
      _ = _ := by ring
  have hcap : chirpEN s t b ≤ 4 * B ^ 8 := by
    calc _ ≤ B ^ 4 := hn
      _ = 1 * B ^ 4 := by omega
      _ ≤ _ := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_right h.base (by decide))
  exact (Nat.mul_le_mul_right _ hcap).trans_lt h.budget

/-- A natural rational-exponent gate sufficient for the positive evaluator's machine bound. -/
theorem chirp_positive_guard (q a b : ℕ) (hq : 2 ≤ q) (h4 : 4 * a < q * b) :
    IntegerMultBounds.Resampling.WeightNat.piN q * a / b < q * 2 ^ (5 * q) := by
  have hpi := IntegerMultBounds.MathlibTM2.Fast.TableVM.tbl_piN_lt q hq
  apply Nat.div_lt_of_lt_mul
  calc
    _ ≤ (4 * 2 ^ (5 * q)) * a := Nat.mul_le_mul_right _ hpi.le
    _ = (4 * a) * 2 ^ (5 * q) := by ring
    _ < (q * b) * 2 ^ (5 * q) := Nat.mul_lt_mul_of_pos_right h4 (Nat.two_pow_pos _)
    _ = _ := by ring

/-- One integer gate implies the positive evaluator's machine guard. -/
theorem chirp_positive_machine_gate (q a b : ℕ) (hq : 13 ≤ q) (hb : 0 < b)
    (h : 4 * a ≤ (q - 1) * b) :
    IntegerMultBounds.Resampling.WeightNat.piN q * a / b < q * 2 ^ (5 * q) := by
  apply chirp_positive_guard q a b (by omega)
  exact h.trans_lt (Nat.mul_lt_mul_of_pos_right (by omega : q - 1 < q) hb)

/-- The same integer gate implies the real exponent-range condition in the error theorem. -/
theorem chirp_positive_error_gate (q a b : ℕ) (hq : 13 ≤ q) (hb : 0 < b)
    (h : 4 * a ≤ (q - 1) * b) : Real.pi * a / b ≤ (q : ℝ) - 1 := by
  have hc : (4 : ℝ) * a ≤ ((q : ℝ) - 1) * b := by
    have hc : ((4 * a : ℕ) : ℝ) ≤ (((q - 1) * b : ℕ) : ℝ) := by exact_mod_cast h
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one] using hc
  apply (div_le_iff₀ (by exact_mod_cast hb : (0 : ℝ) < b)).2
  exact (mul_le_mul_of_nonneg_right Real.pi_lt_four.le (Nat.cast_nonneg a)).trans hc

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
