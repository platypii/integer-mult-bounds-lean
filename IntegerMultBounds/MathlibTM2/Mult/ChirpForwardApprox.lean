module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardValue
public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardPrecision

/-! # Approximation guarantee for the actual returned integer forward tape -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast

noncomputable def chirpForwardDecoded (A s t α p q l Γ m : ℕ) (u : ZMod s → GaussianInt) : ZMod t → ℂ :=
  fun k => value p (decodeWord (((cstream A (p + l + Γ + 5)
    (chirpForwardOutput s t α p q l Γ m u) ++ []).drop
      (k.val * (p + l + Γ + 5))).take (p + l + Γ + 5)))

/-- The real tape's error bound uses the explicit linear precision, with no accumulated-error hypotheses. -/
theorem chirpForwardDecoded_error {s t A : ℕ} [NeZero s] [NeZero t]
    (hA : 4 ≤ A) (hst : s < t) (α p l Γ m : ℕ)
    (hα : 1 ≤ α) (hαp : (α : ℝ) ^ 2 ≤ p)
    (hm : (p : ℝ) * (α : ℝ) ^ 2 ≤ (m : ℝ) ^ 2) (hm1 : 1 ≤ m) (hl : 7 * m ≤ 2 ^ l)
    (hgate : ∀ b < m, Real.pi * (chirpEN s t b : ℝ) / (chirpED t α : ℝ) ≤
      (chirpForwardPrecision p Γ l - Γ : ℕ) - 1)
    (hΓ : ∀ b < m, chirpE s t (α : ℝ) b ≤ 2 ^ Γ)
    (u : ZMod s → GaussianInt)
    (hu : ∀ j, ‖value (chirpForwardPrecision p Γ l) (u j)‖ ≤ 1) :
    2 ^ p * ‖chirpForwardDecoded A s t α p (chirpForwardPrecision p Γ l) l Γ m u -
      resampA s t (α : ℝ) (fun j => value (chirpForwardPrecision p Γ l) (u j))‖ ≤ 4 := by
  let q := chirpForwardPrecision p Γ l
  have hpq : p ≤ q := by dsimp [q, chirpForwardPrecision]; omega
  have hΓq : Γ ≤ q := by dsimp [q, chirpForwardPrecision]; omega
  have hq : 13 ≤ q - Γ := by dsimp [q, chirpForwardPrecision]; omega
  have hdata : chirpForwardDecoded A s t α p q l Γ m u =
      chirpAR (s := s) (t := t) p (q + 1) m l Γ (rhoC q)
        (fun k0 a => (chirpTableG s t α q m k0 a : ℝ) / 2 ^ q)
        (fun k0 a => (chirpTableK s t α q m k0 a : ℝ) / 2 ^ q)
        (fun _ b => (chirpTableE s t α (q - Γ) b : ℝ) / 2 ^ q)
        ((chirpNormalization q α : ℝ) / 2 ^ q) (fun j => value q (u j)) := by
    funext k
    exact chirpForwardTape_value hA hst α p q l Γ m (by omega) hpq hΓq hq hm1 hl hgate hΓ u hu [] k
  obtain ⟨hζ, hEη, hsm⟩ := chirpForwardPrecision_gates p Γ l m (by omega)
  have hinput : ‖fun j => value q (u j)‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg (by norm_num)).mpr hu
  have herr := chirpComputed_approx hst α p q m l Γ hα hαp hm hm1 hl hΓq hq hgate hΓ
    (by simpa only [chirpForwardCorrelationError, chirpForwardEta] using hζ)
    (by simpa only [chirpForwardProductError, chirpForwardCorrelationError, chirpForwardEta] using hEη)
    (by simpa only [chirpForwardFinalError, chirpForwardProductError,
      chirpForwardCorrelationError, chirpForwardEta] using hsm)
    (fun j => value q (u j)) hinput
  change 2 ^ p * ‖chirpForwardDecoded A s t α p q l Γ m u - _‖ ≤ 4
  rw [hdata]
  exact herr

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
