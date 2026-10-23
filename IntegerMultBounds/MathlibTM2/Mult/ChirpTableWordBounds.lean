module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableHost
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvDecode

/-! # Signed decoding of emitted chirp tables

The exponential error bounds also bound the nonnegative numerators. Two guard bits at the
relevant precision ensure exact signed decoding of the emitted words, including after an
arbitrary pre-existing output suffix.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.Resampling
  IntegerMultBounds.Spec.SignedRingProduct

theorem expPiNat_neg_le (q a b : ℕ) (hq : 13 ≤ q) (hb : 0 < b) :
    WeightNat.expPiNat true q a b ≤ 2 ^ q + 2 := by
  have h := WeightTable.expPi_neg_err q a b hq hb
  rw [WeightNat.expPi_eq_nat true q a b hq] at h
  simp only [Int.cast_natCast] at h
  have hexp : Real.exp (-(Real.pi * a / b)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hprod := mul_le_mul_of_nonneg_left hexp (by positivity : (0 : ℝ) ≤ 2 ^ q)
  have hn : (WeightNat.expPiNat true q a b : ℝ) ≤ (2 : ℝ) ^ q + 2 := by
    have hu := (abs_le.mp h).2
    nlinarith
  exact_mod_cast hn

theorem expPiNat_pos_le (q a b Γ : ℕ) (hq : 13 ≤ q) (hb : 0 < b)
    (hx : Real.pi * a / b ≤ (q : ℝ) - 1) (hΓ : Real.exp (Real.pi * a / b) ≤ 2 ^ Γ) :
    WeightNat.expPiNat false q a b ≤ 2 ^ (q + Γ) + 2 := by
  have h := WeightTable.expPi_pos_err q a b hq hb hx
  rw [WeightNat.expPi_eq_nat false q a b hq] at h
  simp only [Int.cast_natCast] at h
  have hprod := mul_le_mul_of_nonneg_left hΓ (by positivity : (0 : ℝ) ≤ 2 ^ q)
  rw [← pow_add] at hprod
  have hn : (WeightNat.expPiNat false q a b : ℝ) ≤ (2 : ℝ) ^ (q + Γ) + 2 := by
    have hu := (abs_le.mp h).2
    linarith
  exact_mod_cast hn

/-- A nonnegative numerator with this error allowance fits the signed word. -/
theorem decodeWord_nat {A : ℕ} (hA : 4 ≤ A) (p w n : ℕ) (hp : 1 ≤ p) (hw : p + 3 ≤ w)
    (hn : n ≤ 2 ^ p + 2) :
    decodeWord (csyms A w (⟨(n : ℤ), 0⟩ : GaussianInt)) = ⟨(n : ℤ), 0⟩ := by
  have htwo : 2 ≤ 2 ^ p := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hp
  have hsum : 2 ^ p + 2 ≤ 2 ^ (p + 1) := by rw [pow_succ]; omega
  have hlt : n < 2 ^ (w - 1) := (hn.trans hsum).trans_lt
    (Nat.pow_lt_pow_right (by decide) (by omega))
  have hlow : -(2 : ℤ) ^ (w - 1) ≤ (n : ℤ) :=
    (neg_nonpos.mpr (by positivity)).trans (Nat.cast_nonneg n)
  have hre := compValue_compWord (by omega : 1 ≤ w) hlow (by exact_mod_cast hlt)
  have him := compValue_compWord (by omega : 1 ≤ w)
    (neg_nonpos.mpr (by positivity) : -(2 : ℤ) ^ (w - 1) ≤ 0)
    (by positivity : (0 : ℤ) < 2 ^ (w - 1))
  rw [decodeWord_csyms hA, hre, him]

/-- Locate a generated table entry in its forward output stream. -/
theorem chirpEntryStream_word {A : ℕ} (w N : ℕ) (f : ℕ → ℕ)
    (tail : List (Fin (A + 4))) (j : ℕ) (hj : j < N) :
    ((chirpEntryStream A w N f ++ tail).drop (j * w)).take w =
      csyms A w (⟨(f j : ℤ), 0⟩ : GaussianInt) := by
  unfold chirpEntryStream
  rw [cstream_word w _ tail j (by simpa using hj)]
  simp

/-- Signed decoding recovers generated table numerators without modular aliasing. -/
theorem chirpEntryStream_decode {A : ℕ} (hA : 4 ≤ A) (p w N : ℕ) (f : ℕ → ℕ)
    (hp : 1 ≤ p) (hw : p + 3 ≤ w) (hbound : ∀ j < N, f j ≤ 2 ^ p + 2)
    (tail : List (Fin (A + 4))) (j : ℕ) (hj : j < N) :
    decodeWord (((chirpEntryStream A w N f ++ tail).drop (j * w)).take w) = ⟨(f j : ℤ), 0⟩ := by
  rw [chirpEntryStream_word w N f tail j hj]
  exact decodeWord_nat hA p w (f j) hp hw (hbound j hj)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
