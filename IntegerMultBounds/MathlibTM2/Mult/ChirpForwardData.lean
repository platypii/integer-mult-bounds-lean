module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpCorrelationRows
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputFactorSetup
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputIndex
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputDecode
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputFormula

/-! # The exact data returned by the chirped forward program

Keep the padded correlation rows until the last arithmetic pass, then crop to t.
The output list records the actual integer computation, with no analytic oracle.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast

def chirpForwardRows (s t α q l m : ℕ) (u : ZMod s → GaussianInt) : List (List GaussianInt) :=
  chirpCorrelationRows (chirpBlockCount t m) m (fun n => coeff (q + 1) l
    (chirpOperandX s t q m n (chirpInputNumerators s t α q m) u)
    (chirpOperandY m n (chirpKernelNumerators s t α q m)))

def chirpForwardNumerators (s t α q l Γ m : ℕ) (u : ZMod s → GaussianInt) : List GaussianInt :=
  chirpOutputNumerators q l Γ (chirpForwardRows s t α q l m u)
    (chirpOutputFactors s t α q Γ m) (chirpNormalization q α)

def chirpForwardOutput (s t α p q l Γ m : ℕ) (u : ZMod s → GaussianInt) : List GaussianInt :=
  ((chirpForwardNumerators s t α q l Γ m u).take t).map (tdivN (q - p))

/-- The ceiling batch covers every original output position. -/
theorem chirpBlockCount_mul_ge (t m : ℕ) (hm : 0 < m) : t ≤ chirpBlockCount t m * m := by
  have hmod := Nat.mod_lt (t - 1) hm
  have hdiv := Nat.div_add_mod (t - 1) m
  rw [Nat.mul_comm m] at hdiv
  unfold chirpBlockCount
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Every row has exactly the number of factors generated for it. -/
theorem chirpForwardRows_length (s t α q l m : ℕ) (u : ZMod s → GaussianInt)
    (hl : 7 * m ≤ 2 ^ l) :
    ∀ xs ∈ chirpForwardRows s t α q l m u, xs.length = m :=
  chirpCorrelationRows_length _ _ _ (by omega)

theorem chirpForwardNumerators_length (s t α q l Γ m : ℕ) (u : ZMod s → GaussianInt)
    (hl : 7 * m ≤ 2 ^ l) :
    (chirpForwardNumerators s t α q l Γ m u).length = chirpBlockCount t m * m := by
  rw [chirpForwardNumerators, chirpOutputNumerators_length]
  · rw [chirpForwardRows, chirpCorrelationRows_flatten]
    exact correlationStream_length _ _ (by omega) _
  · simpa only [chirpOutputFactors_length] using chirpForwardRows_length s t α q l m u hl

/-- Cropping emits exactly t values, including the final partial block. -/
theorem chirpForwardOutput_length (s t α p q l Γ m : ℕ) (u : ZMod s → GaussianInt)
    (hm : 0 < m) (hl : 7 * m ≤ 2 ^ l) :
    (chirpForwardOutput s t α p q l Γ m u).length = t := by
  simp only [chirpForwardOutput, List.length_map, List.length_take,
    chirpForwardNumerators_length s t α q l Γ m u hl]
  exact Nat.min_eq_left (chirpBlockCount_mul_ge t m hm)

/-- The generated data supply the complete output stage's norm envelope. -/
theorem chirpForwardNumerators_norm {s t : ℕ} [NeZero s] [NeZero t]
    (hst : s < t) (α q l Γ m : ℕ) (hα : 0 < α) (hΓq : Γ ≤ q) (hq : 13 ≤ q - Γ)
    (hl : 7 * m ≤ 2 ^ l)
    (hgate : ∀ b < m, Real.pi * (chirpEN s t b : ℝ) / (chirpED t α : ℝ) ≤ (q - Γ : ℕ) - 1)
    (hΓ : ∀ b < m, NLogN.chirpE s t (α : ℝ) b ≤ 2 ^ Γ)
    (u : ZMod s → GaussianInt) (hu : ∀ j, ‖value q (u j)‖ ≤ 1) :
    ∀ z ∈ chirpForwardNumerators s t α q l Γ m u, ‖value q z‖ ≤ 8 * (2 : ℝ) ^ (l + Γ) :=
  chirpOutputNumerators_norm q l Γ _ _ _
    (chirpGeneratedCorrelationRows_norm hst α q l _ m hα (by omega) hl u hu)
    (chirpOutputFactors_bound s t α q Γ m (NeZero.pos s) hst hα hΓq hq hgate hΓ)
    (chirpNormalization_abs_le_one q α)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
