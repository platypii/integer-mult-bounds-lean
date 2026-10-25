module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardData
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputTape

/-! # The returned forward tape agrees with the computed analytic map

The scalar chirp bridge applies at every original output index. Row-periodic E
lookup and final signed decoding are proved for the exact returned integer list.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast

/-- Read the executed output representation as the computed-factor forward map. -/
theorem chirpForwardTape_value {s t A : ℕ} [NeZero s] [NeZero t]
    (hA : 4 ≤ A) (hst : s < t) (α p q l Γ m : ℕ)
    (hα : 0 < α) (hpq : p ≤ q) (hΓq : Γ ≤ q) (hq : 13 ≤ q - Γ)
    (hm : 0 < m) (hl : 7 * m ≤ 2 ^ l)
    (hgate : ∀ b < m, Real.pi * (chirpEN s t b : ℝ) / (chirpED t α : ℝ) ≤ (q - Γ : ℕ) - 1)
    (hΓ : ∀ b < m, chirpE s t (α : ℝ) b ≤ 2 ^ Γ)
    (u : ZMod s → GaussianInt) (hu : ∀ j, ‖value q (u j)‖ ≤ 1)
    (tail : List (Fin (A + 4))) (k : ZMod t) :
    value p (decodeWord (((cstream A (p + l + Γ + 5) (chirpForwardOutput s t α p q l Γ m u) ++ tail).drop
      (k.val * (p + l + Γ + 5))).take (p + l + Γ + 5))) =
      chirpAR (s := s) (t := t) p (q + 1) m l Γ (rhoC q)
        (fun k0 a => (chirpTableG s t α q m k0 a : ℝ) / 2 ^ q)
        (fun k0 a => (chirpTableK s t α q m k0 a : ℝ) / 2 ^ q)
        (fun _ b => (chirpTableE s t α (q - Γ) b : ℝ) / 2 ^ q)
        ((chirpNormalization q α : ℝ) / 2 ^ q) (fun j => value q (u j)) k := by
  have hrows : ∀ xs ∈ chirpForwardRows s t α q l m u,
      xs.length = (chirpOutputFactors s t α q Γ m).length := by
    simpa only [chirpOutputFactors_length] using chirpForwardRows_length s t α q l m u hl
  have hkflat : k.val < (chirpForwardRows s t α q l m u).flatten.length := by
    rw [chirpForwardRows, chirpCorrelationRows_flatten, correlationStream_length _ _ (by omega)]
    exact k.val_lt.trans_le (chirpBlockCount_mul_ge t m hm)
  rw [chirpForwardOutput, chirpForwardNumerators]
  rw [chirpOutputTape_word hA hpq l Γ (q + 3) t (by omega)
    (chirpForwardRows s t α q l m u) (chirpOutputFactors s t α q Γ m) (chirpNormalization q α)
    (by simp only [chirpOutputFactors_length]; omega) hrows
    (chirpGeneratedCorrelationRows_norm hst α q l _ m hα (by omega) hl u hu)
    (chirpOutputFactors_bound s t α q Γ m (NeZero.pos s) hst hα hΓq hq hgate hΓ)
    (chirpNormalization_abs_le_one q α) tail k.val k.val_lt hkflat]
  rw [chirpForwardRows, chirpCorrelationRows_flatten]
  simp only [chirpOutputFactors, List.length_map, List.length_range,
    List.getElem_map, List.getElem_range]
  simpa only [Int.cast_natCast] using chirpOutputWord_chirpAR hA hst α p q l (q + 3) m Γ
    hα (by omega) hpq (by omega) hm hl u hu
    (fun b => (chirpTableE s t α (q - Γ) b : ℤ)) (chirpNormalization q α) [] k

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
