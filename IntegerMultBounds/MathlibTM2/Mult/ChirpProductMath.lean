module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpProduct
public import IntegerMultBounds.MathlibTM2.Mult.ChirpRing

/-! # The executed correlation block agrees with the analytic chirp stage

The operand-production interface is explicit: decoded numerator records must equal the
halved chirp input and shifted kernel. Under that interface the returned tape, rescaled by
`4r`, is exactly `chirpRingCorr`, so the established forward-map error analysis applies.
This theorem does not supply coefficient tables or gather the overlapping input windows.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast

variable {s t : ℕ}

/-- Exact analytic meaning of the actual word returned at output offset `b`. -/
theorem correlationTape_chirpRingCorr {A : ℕ} (hA : 4 ≤ A) (p l w m : ℕ)
    (hw : p + 2 ≤ w) (hm : 1 ≤ m) (hl : 7 * m ≤ 2 ^ l)
    (x y : List GaussianInt) (hxy : x.length + y.length ≤ 2 ^ l + 1)
    (hX : ∀ z ∈ x, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hY : ∀ z ∈ y, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (rd : ℂ → ℂ) (gt : ℕ → ℕ → ℝ) (kt : ℕ → ℤ → ℝ) (u : ZMod s → ℂ) (n : ℕ)
    (hx : ∀ i : Fin (2 ^ l), value p (block x i) = chirpRecIn (t := t) m rd gt u n i)
    (hy : ∀ i : Fin (2 ^ l), value p (block y i) = chirpRecK m kt n i)
    (tail : List (Fin (A + 4))) (b : ℕ) (hb : b < m) :
    (4 * (2 ^ l : ℕ) : ℂ) * value p (decodeWord
      (((Fast.cstream A w (correlationCoeffs m (List.ofFn (coeff p l x y))) ++ tail).drop
        (b * w)).take w)) = chirpRingCorr (t := t) p m l rd gt kt u (n * m) b := by
  rw [correlationTape_coeff hA p l w m hw (by omega) x y hxy hX hY tail b hb]
  let X := fun (_ : ℕ) => recOf (2 ^ l) (block x)
  let Y := fun (_ : ℕ) => recOf (2 ^ l) (block y)
  let c : Fin (2 ^ l) := ⟨4 * m - 1 - b, by omega⟩
  have hpoint := rp_pwC_grid p X Y 0 c
  rw [rpOut_block p l x y hxy] at hpoint
  change SynthErr.pwC p (rpGrid p X) (rpGrid p Y) 0 c = value p (coeff p l x y c) at hpoint
  rw [← hpoint]
  have hx' : rpGrid p X 0 = recOf (2 ^ l) (chirpRecIn (t := t) m rd gt u n) := by
    funext i
    exact hx i
  have hy' : rpGrid p Y 0 = recOf (2 ^ l) (chirpRecK m kt n) := by
    funext i
    exact hy i
  unfold chirpRingCorr
  rw [Nat.mul_div_cancel n (by omega)]
  simp only [Nat.mod_eq_of_lt (show 4 * m - 1 - b < 2 ^ l by omega)]
  rw [SynthErr.pwC_apply, SynthErr.pwC_apply, hx', hy']
  simp only [c, Nat.cast_pow, Nat.cast_ofNat]

/-- Forward correlation error for the decoded tape, under the operand-production interface. -/
theorem correlationTape_chirpCorr_err {A : ℕ} (hA : 4 ≤ A) (p l w m : ℕ)
    (hw : p + 2 ≤ w) (hm : 1 ≤ m) (hl : 7 * m ≤ 2 ^ l)
    (x y : List GaussianInt) (hxy : x.length + y.length ≤ 2 ^ l + 1)
    (hX : ∀ z ∈ x, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hY : ∀ z ∈ y, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (rd : ℂ → ℂ) (gt : ℕ → ℕ → ℝ) (kt : ℕ → ℤ → ℝ) (u : ZMod s → ℂ) (n : ℕ)
    (hx : ∀ i : Fin (2 ^ l), value p (block x i) = chirpRecIn (t := t) m rd gt u n i)
    (hy : ∀ i : Fin (2 ^ l), value p (block y i) = chirpRecK m kt n i)
    (tail : List (Fin (A + 4))) (b : ℕ) (hb : b < m) :
    ‖(4 * (2 ^ l : ℕ) : ℂ) * value p (decodeWord
      (((Fast.cstream A w (correlationCoeffs m (List.ofFn (coeff p l x y))) ++ tail).drop
        (b * w)).take w)) - chirpCorr (t := t) m rd gt kt u (n * m) b‖ ≤
      8 * (2 : ℝ) ^ l / (2 : ℝ) ^ p := by
  rw [correlationTape_chirpRingCorr hA p l w m hw hm hl x y hxy hX hY
    rd gt kt u n hx hy tail b hb]
  exact chirpRingCorr_err p m l hm hl rd gt kt u n b hb

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
