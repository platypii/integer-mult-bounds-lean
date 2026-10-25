module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputProductNorm

/-! # Structural contracts for the complete chirp numerator stream -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.MathlibTM2.Fast

def chirpOutputNumerators (q l Γ : ℕ) (blocks : List (List GaussianInt))
    (es : List ℤ) (a : ℤ) : List GaussianInt :=
  blocks.flatMap (fun xs => List.zipWith (fun c e => chirpOutputNumerator q l Γ c e a) xs es)

/-- The normalization pass acts on exactly the preceding E-product stream. -/
theorem chirpOutputNumerators_eq (q l Γ : ℕ) (blocks : List (List GaussianInt))
    (es : List ℤ) (a : ℤ) :
    chirpOutputNumerators q l Γ blocks es a =
      (blocks.flatMap (fun xs => List.zipWith (chirpOutputEProduct q l) xs es)).map
        (fun x => chirpOutputNormalize q Γ x a) := by
  simp only [chirpOutputNumerators, List.map_flatMap, List.map_zipWith,
    chirpOutputNormalize_EProduct]

/-- Every correlation contributes one numerator, including the padded last row. -/
theorem chirpOutputNumerators_length (q l Γ : ℕ) (blocks : List (List GaussianInt))
    (es : List ℤ) (a : ℤ) (hlen : ∀ xs ∈ blocks, xs.length = es.length) :
    (chirpOutputNumerators q l Γ blocks es a).length = blocks.flatten.length := by
  simp only [chirpOutputNumerators, List.length_flatMap, List.length_flatten]
  congr 1
  apply List.map_congr_left
  intro xs hx
  simp only [List.length_zipWith, hlen xs hx, Nat.min_self]

/-- The product-stage envelope supplies the final rounding pass without extra fit assumptions. -/
theorem chirpOutputNumerators_norm (q l Γ : ℕ) (blocks : List (List GaussianInt))
    (es : List ℤ) (a : ℤ)
    (hx : ∀ c ∈ blocks.flatten, ‖value (q + 1) c‖ ≤ 1)
    (he : ∀ e ∈ es, |(e : ℝ) / 2 ^ q| ≤ 2) (ha : |(a : ℝ) / 2 ^ q| ≤ 1) :
    ∀ z ∈ chirpOutputNumerators q l Γ blocks es a,
      ‖value q z‖ ≤ 8 * (2 : ℝ) ^ (l + Γ) := by
  intro z hz
  rw [chirpOutputNumerators_eq] at hz
  obtain ⟨x, hxmem, rfl⟩ := List.mem_map.mp hz
  have hE := chirpOutputEBlocks_norm q l blocks es hx he x hxmem
  have hshift : ‖value q ((2 : GaussianInt) ^ Γ * x)‖ ≤
      (2 : ℝ) ^ Γ * (8 * (2 : ℝ) ^ l) := by
    rw [value_pow_two_mul, norm_mul, norm_pow, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hE (by positivity)
  exact (norm_value_real_product q _ a _ _ hshift ha (by norm_num)).trans_eq
    (by rw [pow_add]; ring)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
