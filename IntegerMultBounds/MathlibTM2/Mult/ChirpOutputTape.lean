module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputIndex
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputDecode
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputFormula

/-! # Structural scalar semantics of the complete output tape -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast

/-- Finishing the tape realizes the scalar output formula at each retained index. -/
theorem chirpOutputTape_word {A p q : ℕ} (hA : 4 ≤ A) (hpq : p ≤ q)
    (l Γ w t : ℕ) (hw : q + 3 ≤ w)
    (blocks : List (List GaussianInt)) (es : List ℤ) (a : ℤ) (hes0 : 1 ≤ es.length)
    (hlen : ∀ xs ∈ blocks, xs.length = es.length)
    (hxs : ∀ c ∈ blocks.flatten, ‖value (q + 1) c‖ ≤ 1)
    (hes : ∀ e ∈ es, |(e : ℝ) / 2 ^ q| ≤ 2) (ha : |(a : ℝ) / 2 ^ q| ≤ 1)
    (tail : List (Fin (A + 4))) (k : ℕ) (hkt : k < t) (hk : k < blocks.flatten.length) :
    value p (decodeWord (((cstream A (p + l + Γ + 5)
      (((chirpOutputNumerators q l Γ blocks es a).take t).map (tdivN (q - p))) ++ tail).drop
        (k * (p + l + Γ + 5))).take (p + l + Γ + 5))) =
      value p (chirpOutputWord p q l Γ
        (decodeWord (((cstream A w blocks.flatten ++ []).drop (k * w)).take w))
        (es[k % es.length]'(Nat.mod_lt _ (by omega))) a) := by
  have hknums : k < (chirpOutputNumerators q l Γ blocks es a).length := by
    rw [chirpOutputNumerators_length q l Γ blocks es a hlen]
    exact hk
  rw [chirpOutputFinished_coeff hA hpq l Γ t _
    (chirpOutputNumerators_norm q l Γ blocks es a hxs hes ha) tail k hkt hknums]
  rw [chirpOutputNumerators_getElem q l Γ blocks es a hes0 hlen k hk]
  have hfit : Fits w blocks.flatten[k] := by
    apply fits_of_norm_value_bound _ 1 (hxs _ (List.getElem_mem hk))
    simpa only [mul_one] using (pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2)
      (by omega : q + 1 < w - 1))
  rw [cstream_word w _ [] k hk, decodeWord_of_fits hA (by omega) _ hfit]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
