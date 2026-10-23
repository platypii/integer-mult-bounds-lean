module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputFormula

/-! # Forward approximation using only computed chirp factors

All G/K/E and normalization errors are discharged. The remaining inequalities are
explicit precision and window-size gates for the final forward contract.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Resampling

/-- The computed-factor analytic map satisfies the forward approximation contract. -/
theorem chirpComputed_approx {s t : ℕ} [NeZero s] [NeZero t]
    (hst : s < t) (α p q m l Γ : ℕ) (hα : 1 ≤ α) (hαp : (α : ℝ) ^ 2 ≤ p)
    (hm : (p : ℝ) * (α : ℝ) ^ 2 ≤ (m : ℝ) ^ 2) (hm1 : 1 ≤ m) (hl : 7 * m ≤ 2 ^ l)
    (hΓq : Γ ≤ q) (hq : 13 ≤ q - Γ)
    (hgate : ∀ b < m, Real.pi * (chirpEN s t b : ℝ) / (chirpED t α : ℝ) ≤ (q - Γ : ℕ) - 1)
    (hΓ : ∀ b < m, chirpE s t (α : ℝ) b ≤ 2 ^ Γ)
    (hζ : 8 * 2 ^ l / (2 : ℝ) ^ (q + 1) + (3 * m + 1) * (4 * (2 / (2 : ℝ) ^ (q - Γ))) ≤ 3 * m + 1)
    (hEη : 2 ^ Γ * ((6 * (m : ℝ) + 3) * (2 / (2 : ℝ) ^ (q - Γ)) +
      (8 * 2 ^ l / (2 : ℝ) ^ (q + 1) + (3 * m + 1) * (4 * (2 / (2 : ℝ) ^ (q - Γ))))) ≤ 1)
    (hsm : 2 ^ p * ((2 / (2 : ℝ) ^ (q - Γ)) + (2 / (2 : ℝ) ^ (q - Γ)) * (3 * m + 2) +
      1 / 2 * (2 ^ Γ * ((6 * m + 3) * (2 / (2 : ℝ) ^ (q - Γ)) +
        (8 * 2 ^ l / (2 : ℝ) ^ (q + 1) + (3 * m + 1) * (4 * (2 / (2 : ℝ) ^ (q - Γ))))))) ≤ 1 / 2) :
    ApproxMap p
      (chirpAR (s := s) (t := t) p (q + 1) m l Γ (rhoC q)
        (fun k0 a => (chirpTableG s t α q m k0 a : ℝ) / 2 ^ q)
        (fun k0 a => (chirpTableK s t α q m k0 a : ℝ) / 2 ^ q)
        (fun _ b => (chirpTableE s t α (q - Γ) b : ℝ) / 2 ^ q)
        ((chirpNormalization q α : ℝ) / 2 ^ q)) (resampA s t (α : ℝ)) 4 := by
  have hα0 : 0 < α := by omega
  have hq0 : 13 ≤ q := by omega
  have hη : 2 / (2 : ℝ) ^ q ≤ 2 / (2 : ℝ) ^ (q - Γ) := by
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le q Γ))
  apply chirpAR_approx hst (by exact_mod_cast hα) hαp hm hm1 hl (rhoC q)
    (2 / (2 : ℝ) ^ (q - Γ))
    (fun z => (norm_rhoC_sub_le_two q z).trans hη) (chirpTable_eta_le _ hq)
    _ _ _ _
  · intro k0 a
    exact (chirpTableG_err s t α q m k0 a (NeZero.pos s) hst hα0 hq0).trans hη
  · intro k0 a
    exact (chirpTableK_err s t α q m k0 a (NeZero.pos s) (NeZero.pos t) hα0 hq0).trans hη
  · intro k0 b hb
    exact chirpOutputE_err s t α q Γ b (NeZero.pos s) hst hα0 hΓq hq (hgate b hb)
  · exact (chirpNormalization_err q α hα0).trans
      ((div_le_div_of_nonneg_right (by norm_num) (by positivity)).trans hη)
  · exact hΓ
  · exact hζ
  · exact hEη
  · exact hsm

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
