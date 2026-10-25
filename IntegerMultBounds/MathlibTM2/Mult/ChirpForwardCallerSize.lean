module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardTableSize
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBlockCount

/-! # One selected bank width pays the forward caller's volume and address gates -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

def chirpForwardCallerBase (s t p : ℕ) : ℕ := max s (t + 125 * p)

/-- Table scheduling must cover the padded last block, which may extend beyond t. -/
theorem chirpForwardCaller_tableBounds (s t p α : ℕ) (_hp : 1 ≤ p)
    (ht : 1 ≤ t) (hαp : α ^ 2 ≤ p) :
    let m := chirpForwardWindow p α
    let B := chirpForwardCallerBase s t p
    chirpBlockCount t m ≤ B ∧ chirpBlockCount t m * m ≤ B ∧ 4 * m + 1 ≤ B := by
  have hb : t + 125 * p ≤ chirpForwardCallerBase s t p := le_max_right _ _
  have hm := chirpForwardWindow_le p α hαp
  have hM : chirpBlockCount t (chirpForwardWindow p α) ≤ t := by
    unfold chirpBlockCount
    have := Nat.div_le_self (t - 1) (chirpForwardWindow p α)
    omega
  have hMm := chirpBlockCount_mul_le t (chirpForwardWindow p α)
  dsimp only
  omega

/-- The evaluator's existing word size also dominates every quadratic caller volume. -/
theorem chirpForwardTableWord_quadratic (q B : ℕ) :
    1024 * (B + 1) ^ 2 < 2 ^ chirpForwardTableWord q B := by
  have hB : (B + 1) ^ 2 ≤ 2 ^ (2 * Nat.size B) := by
    calc
      _ ≤ (2 ^ Nat.size B) ^ 2 := Nat.pow_le_pow_left (Nat.lt_size_self B) _
      _ = _ := by rw [← pow_mul, Nat.mul_comm (Nat.size B)]
  calc
    _ ≤ 1024 * 2 ^ (2 * Nat.size B) := Nat.mul_le_mul_left _ hB
    _ = 2 ^ (10 + 2 * Nat.size B) := by rw [pow_add]; norm_num
    _ < _ := Nat.pow_lt_pow_right (by decide) (by unfold chirpForwardTableWord; omega)

/-- Every caller-side scalar, window volume, crop volume and multiplier-size gate fits. -/
theorem chirpForwardCaller_fits (s t p α : ℕ) (hp : 1 ≤ p) (hαp : α ^ 2 ≤ p) :
    let m := chirpForwardWindow p α
    let l := chirpForwardRingLog p α
    let Γ := chirpForwardGrowth p
    let q := chirpForwardPrecision p Γ l
    let w := q + l + Γ + 5
    let wo := p + l + Γ + 5
    let B := chirpForwardCallerBase s t p
    let W := chirpForwardTableWord q B
    (∀ i : Fin 4, (![p, α, s, t] : Fin 4 → ℕ) i < 2 ^ Nat.size B) ∧
      Nat.size B ≤ W ∧ 125 * p < 2 ^ W ∧ w ≤ W ∧
      s ≤ B ∧ t ≤ B ∧ α ≤ B ∧ m ≤ B ∧
      s + 3 * m + 1 < 2 ^ W ∧ (s + 3 * m + 1) * w < 2 ^ W ∧
      t + m < 2 ^ W ∧ s * (t + m) < 2 ^ W ∧
      t * wo < 2 ^ W ∧ q + 1 < 2 ^ W ∧ 3 * m + 1 < 2 ^ W ∧
      4 * m < 2 ^ W ∧ 4 * w + 2 < 2 ^ W := by
  dsimp only
  let B := chirpForwardCallerBase s t p
  let q := chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α)
  have hs : s ≤ B := le_max_left _ _
  have hbase : t + 125 * p ≤ B := le_max_right _ _
  have ht : t ≤ B := by omega
  have hpB : 125 * p ≤ B := by omega
  have hp' : p ≤ B := by omega
  have hα : α ≤ B := (by nlinarith [Nat.le_mul_self α] : α ≤ p).trans hp'
  have hm : chirpForwardWindow p α ≤ B := (chirpForwardWindow_le p α hαp).trans (by omega)
  have hw := chirpForwardWidths_le p α hp hαp
  have hq : q ≤ B := hw.1.trans (by omega)
  have hwB : q + chirpForwardRingLog p α + chirpForwardGrowth p + 5 ≤ B := hw.2.1.trans hpB
  have hwo : p + chirpForwardRingLog p α + chirpForwardGrowth p + 5 ≤ B := hw.2.2.trans (by omega)
  have hquad := chirpForwardTableWord_quadratic q B
  have hsmall : B < 2 ^ chirpForwardTableWord q B := by nlinarith [sq_nonneg (B : ℤ)]
  have hprod₁ := Nat.mul_le_mul (show s + 3 * chirpForwardWindow p α + 1 ≤ 4 * B + 1 by omega) hwB
  have hprod₂ := Nat.mul_le_mul hs (show t + chirpForwardWindow p α ≤ 2 * B by omega)
  have hprod₃ := Nat.mul_le_mul ht hwo
  refine ⟨?_, ?_, hpB.trans_lt hsmall, (chirpForwardTableWord_good p (chirpForwardGrowth p)
    (chirpForwardRingLog p α) B (by omega)).2.2, hs, ht, hα, hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hp'.trans_lt (Nat.lt_size_self B)
    · exact hα.trans_lt (Nat.lt_size_self B)
    · exact hs.trans_lt (Nat.lt_size_self B)
    · exact ht.trans_lt (Nat.lt_size_self B)
  · unfold chirpForwardTableWord
    omega
  all_goals nlinarith [Nat.zero_le B]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
