module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableBounds
public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardWindow

/-! # An explicit table word size for both evaluator precisions

Use 13q+8 size(B)+16 bits. The polynomial argument envelope fits by integer
power comparisons, and lowering precision preserves the same bank allocation.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

def chirpForwardTableWord (q B : ℕ) : ℕ := 13 * q + 8 * Nat.size B + 16

/-- The chosen word size pays every intermediate in the finite table evaluator. -/
theorem chirpForwardTableWord_size (q B : ℕ) (hq : 13 ≤ q) (hB : 1 ≤ B) :
    ChirpTableSize (chirpForwardTableWord q B) q B := by
  refine ⟨hB, hq, by unfold chirpForwardTableWord; omega, ?_⟩
  have hBpow : B ^ 8 ≤ 2 ^ (8 * Nat.size B) := by
    calc
      _ ≤ (2 ^ Nat.size B) ^ 8 := Nat.pow_le_pow_left (Nat.lt_size_self B).le _
      _ = _ := by rw [← pow_mul, Nat.mul_comm (Nat.size B)]
  calc
    _ ≤ 4 * 2 ^ (8 * Nat.size B) * 2 ^ (5 * q + 2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hBpow)
    _ = 2 ^ (8 * Nat.size B + 5 * q + 4) := by
      simp only [pow_add]
      ring
    _ < _ := Nat.pow_lt_pow_right (by decide) (by unfold chirpForwardTableWord; omega)

/-- One physical word size supports every smaller evaluator precision. -/
theorem ChirpTableSize.lowerPrecision {W q r B : ℕ} (h : ChirpTableSize W q B)
    (hr : 13 ≤ r) (hrq : r ≤ q) : ChirpTableSize W r B := by
  refine ⟨h.base, hr, by have := h.word; omega, ?_⟩
  exact (Nat.mul_le_mul_left (4 * B ^ 8)
    (Nat.pow_le_pow_right (by decide) (by omega : 5 * r + 2 ≤ 5 * q + 2))).trans_lt h.budget

/-- Full and normalized-E precision fit the same table bank, with enough emitted-word width. -/
theorem chirpForwardTableWord_good (p Γ l B : ℕ) (hB : 1 ≤ B) :
    let q := chirpForwardPrecision p Γ l
    let W := chirpForwardTableWord q B
    ChirpTableSize W q B ∧ ChirpTableSize W (q - Γ) B ∧ q + l + Γ + 5 ≤ W := by
  let q := chirpForwardPrecision p Γ l
  have hq : 13 ≤ q := by dsimp [q, chirpForwardPrecision]; omega
  have hqΓ : 13 ≤ q - Γ := by dsimp [q, chirpForwardPrecision]; omega
  have hfull := chirpForwardTableWord_size q B hq hB
  refine ⟨hfull, hfull.lowerPrecision hqΓ (Nat.sub_le _ _), ?_⟩
  dsimp [chirpForwardTableWord, chirpForwardPrecision]
  omega

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
