module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpComputedApprox

/-! # One explicit precision closes all three accumulated forward-error gates

The extra precision is p+2Γ+l+13. Only m≤2^l is needed for the error ledger;
window geometry and the positive-exponential gate are separate sizing facts.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.NLogN

def chirpForwardPrecision (p Γ l : ℕ) : ℕ := p + 2 * Γ + l + 13

noncomputable def chirpForwardEta (q Γ : ℕ) : ℝ := 2 / (2 : ℝ) ^ (q - Γ)

noncomputable def chirpForwardCorrelationError (q l Γ m : ℕ) : ℝ :=
  8 * 2 ^ l / (2 : ℝ) ^ (q + 1) + (3 * m + 1) * (4 * chirpForwardEta q Γ)

noncomputable def chirpForwardProductError (q l Γ m : ℕ) : ℝ :=
  2 ^ Γ * ((6 * (m : ℝ) + 3) * chirpForwardEta q Γ + chirpForwardCorrelationError q l Γ m)

noncomputable def chirpForwardFinalError (p q l Γ m : ℕ) : ℝ :=
  2 ^ p * (chirpForwardEta q Γ + chirpForwardEta q Γ * (3 * m + 2) +
    1 / 2 * chirpForwardProductError q l Γ m)

/-- Structural error accounting, independent of how the working precision was chosen. -/
theorem chirpForwardError_gates (p q l Γ m : ℕ) (hm : m ≤ 2 ^ l)
    (hsmall : (2 : ℝ) ^ p * 2 ^ Γ * 2 ^ l * chirpForwardEta q Γ ≤ 1 / 4096) :
    chirpForwardCorrelationError q l Γ m ≤ 3 * m + 1 ∧
      chirpForwardProductError q l Γ m ≤ 1 ∧ chirpForwardFinalError p q l Γ m ≤ 1 / 2 := by
  let η := chirpForwardEta q Γ
  let L : ℝ := 2 ^ l
  let G : ℝ := 2 ^ Γ
  let P : ℝ := 2 ^ p
  have hη : 0 ≤ η := by dsimp [η, chirpForwardEta]; positivity
  have hL : 1 ≤ L := one_le_pow₀ (by norm_num)
  have hG : 1 ≤ G := one_le_pow₀ (by norm_num)
  have hP : 1 ≤ P := one_le_pow₀ (by norm_num)
  have hmL : (m : ℝ) ≤ L := by
    dsimp [L]
    exact_mod_cast hm
  have hc : 8 * L / (2 : ℝ) ^ (q + 1) ≤ 4 * L * η := by
    have hd : (2 : ℝ) ^ (q - Γ) ≤ 2 ^ (q + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    calc
      _ ≤ 8 * L / (2 : ℝ) ^ (q - Γ) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hd
      _ = _ := by dsimp [η, chirpForwardEta]; ring
  have hz : chirpForwardCorrelationError q l Γ m ≤ 20 * L * η := by
    dsimp [chirpForwardCorrelationError]
    change 8 * L / (2 : ℝ) ^ (q + 1) + (3 * m + 1) * (4 * η) ≤ _
    nlinarith [mul_nonneg (by linarith : 0 ≤ L - m) hη,
      mul_nonneg (by linarith : 0 ≤ L - 1) hη]
  have he : chirpForwardProductError q l Γ m ≤ 29 * G * L * η := by
    change G * ((6 * m + 3) * η + chirpForwardCorrelationError q l Γ m) ≤ _
    calc
      _ ≤ G * (9 * L * η + 20 * L * η) :=
        mul_le_mul_of_nonneg_left (by
          nlinarith [mul_nonneg (by linarith : 0 ≤ L - m) hη,
            mul_nonneg (by linarith : 0 ≤ L - 1) hη]) (by positivity)
      _ = _ := by ring
  have hLη : L * η ≤ P * G * L * η := by
    have hPG : 1 ≤ P * G := one_le_mul_of_one_le_of_one_le hP hG
    nlinarith [mul_nonneg (by linarith : 0 ≤ P * G - 1) (mul_nonneg (by positivity : 0 ≤ L) hη)]
  have hGLη : G * L * η ≤ P * G * L * η := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ P - 1)
      (mul_nonneg (mul_nonneg (by positivity : 0 ≤ G) (by positivity : 0 ≤ L)) hη)]
  have hfinal : chirpForwardFinalError p q l Γ m ≤ 41 / 2 * (P * G * L * η) := by
    change P * (η + η * (3 * m + 2) + 1 / 2 * chirpForwardProductError q l Γ m) ≤ _
    have hterm : η + η * (3 * m + 2) ≤ 6 * L * η := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ L - m) hη,
        mul_nonneg (by linarith : 0 ≤ L - 1) hη]
    have hLG : L * η ≤ G * L * η := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ G - 1) (mul_nonneg (by positivity : 0 ≤ L) hη)]
    calc
      _ ≤ P * (6 * (G * L * η) + 1 / 2 * (29 * G * L * η)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  change P * G * L * η ≤ _ at hsmall
  refine ⟨?_, ?_, ?_⟩
  · have hm0 : (0 : ℝ) ≤ m := by positivity
    linarith
  · linarith
  · linarith

/-- The chosen linear precision makes the common error budget exactly 2^-12. -/
theorem chirpForwardPrecision_budget (p Γ l : ℕ) :
    (2 : ℝ) ^ p * 2 ^ Γ * 2 ^ l * chirpForwardEta (chirpForwardPrecision p Γ l) Γ = 1 / 4096 := by
  have hsub : chirpForwardPrecision p Γ l - Γ = p + Γ + l + 13 := by
    unfold chirpForwardPrecision
    omega
  unfold chirpForwardEta
  rw [hsub]
  simp only [pow_add]
  norm_num
  field_simp
  ring

/-- All accumulated error inequalities follow from the explicit precision choice. -/
theorem chirpForwardPrecision_gates (p Γ l m : ℕ) (hm : m ≤ 2 ^ l) :
    let q := chirpForwardPrecision p Γ l
    chirpForwardCorrelationError q l Γ m ≤ 3 * m + 1 ∧
      chirpForwardProductError q l Γ m ≤ 1 ∧ chirpForwardFinalError p q l Γ m ≤ 1 / 2 :=
  chirpForwardError_gates p _ l Γ m hm (le_of_eq (chirpForwardPrecision_budget p Γ l))

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
