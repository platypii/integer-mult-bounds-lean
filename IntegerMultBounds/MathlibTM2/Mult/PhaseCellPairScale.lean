module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairFinish

/-! # Explicit scales for the two executed triangular stages

These are interpretations of stored normalized numerators, not free tape
operations. Generator construction, scalar arithmetic and final word conversion
remain execution obligations of the cell caller.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.Spec.SignedRingProduct
  IntegerMultBounds.NLogN.ToeplitzInverse Finset

/-- Both triangular operators are bilinear, including clipped and empty rows. -/
theorem lower_scale {K : Type*} [Field K] (a b : K) (x v : ℕ → K) (i : ℕ) :
    lower (fun k => a * x k) (fun k => b * v k) i = (a * b) * lower x v i := by
  simp only [lower, mul_sum]
  apply sum_congr rfl
  intro k _
  ring

theorem upper_scale {K : Type*} [Field K] (a b : K) (L : ℕ) (x v : ℕ → K) (i : ℕ) :
    upper L (fun k => a * x k) (fun k => b * v k) i = (a * b) * upper L x v i := by
  simp only [upper, mul_sum]
  apply sum_congr rfl
  intro k _
  ring

/-- The compacted upper operand is the rounded numerator at reflected coordinate i. -/
theorem upperOperand_block {q l L : ℕ} (hL : L ≤ 2 ^ l)
    (X V : ℕ → List GaussianInt) (n i : ℕ) (hi : i < L) :
    block (upperOperand q l L X V n) i =
      coeff q l (X n) (V n).reverse ⟨L - 1 - i, by omega⟩ := by
  unfold block upperOperand
  rw [sliceCoeffs_get 0 L _ (by simpa using hL) i hi]
  simp [show L - 1 - i < 2 ^ l by omega]

/-- The computed upper row has the stage error before any later encoding. -/
theorem upperOperand_error {q l M L : ℕ} (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (n : ℕ) (hn : n < M) (i : ℕ) (hi : i < L) :
    ‖((2 ^ l : ℕ) : ℂ) * value q (block (upperOperand q l L X V n) i) -
      upper L (fun k => value q (block (X n) k)) (fun k => value q (block (V n) k)) i‖ ≤
      2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q := by
  have hr : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  rw [upperOperand_block (by omega) X V n i hi]
  exact upper_coeff_error q l L (X n) (V n) (hlenX n hn) (hlenV n hn) hpad i hi

/-- Scaling an already computed stage scales its error by the scalar norm. -/
theorem scale_stage_error (a z target : ℂ) (ε : ℝ) (h : ‖z - target‖ ≤ ε) :
    ‖a * z - a * target‖ ≤ ‖a‖ * ε := by
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg a)

/-- Interpretation of the actual upper numerator after undoing the ring factor. -/
noncomputable def scaledUpper (a b : ℂ) (q l L : ℕ)
    (X V : ℕ → List GaussianInt) (n k : ℕ) : ℂ :=
  (a * b) * (((2 ^ l : ℕ) : ℂ) * value q (block (upperOperand q l L X V n) k))

theorem scaledUpper_error (a b : ℂ) {q l M L : ℕ} (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (n : ℕ) (hn : n < M) (i : ℕ) (hi : i < L) :
    ‖scaledUpper a b q l L X V n i -
      upper L (fun k => a * value q (block (X n) k))
        (fun k => b * value q (block (V n) k)) i‖ ≤
      ‖a * b‖ * (2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q) := by
  rw [upper_scale]
  exact scale_stage_error _ _ _ _ (upperOperand_error hpad X V hlenX hlenV n hn i hi)

/-- The second stage uses the computed upper row, so its interpretation has
one additional generator factor and one additional ring factor. -/
theorem scaledPair_output_error {A q l w M L : ℕ} (hA : 4 ≤ A) (hw : q + 2 ≤ w)
    (a b : ℂ) (hpad : L + L ≤ 2 ^ l + 1) (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (tail : List (Fin (A + 4))) (n : ℕ) (hn : n < M) (i : Fin L) :
    let z := value q (decodeWord (((cstream A w (pairRows q l M L X V) ++ tail).drop
      ((n * L + (L - 1 - i.val)) * w)).take w))
    ‖(a * (a * b * ((2 ^ l : ℕ) : ℂ))) * (((2 ^ l : ℕ) : ℂ) * z) -
      lower (fun k => a * value q (block (X n) k)) (scaledUpper a b q l L X V n) i.val‖ ≤
      ‖a * (a * b * ((2 ^ l : ℕ) : ℂ))‖ * (2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q) := by
  dsimp only
  have hr : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  have hL : L ≤ 2 ^ l := by omega
  have h := lowerRows_error hA hw hpad X (upperOperand q l L X V) hlenX
    (fun j _ => upperOperand_length hL X V j) hX
    (upperOperand_disk hpad X V hlenX hlenV hX hV) tail n hn i
  have hupper : scaledUpper a b q l L X V n =
      fun k => (a * b * ((2 ^ l : ℕ) : ℂ)) * value q (block (upperOperand q l L X V n) k) := by
    funext k
    unfold scaledUpper
    ring
  rw [hupper, lower_scale]
  exact scale_stage_error _ _ _ _ h

/-- Real generators act separately on real and imaginary parts. Rounded
intermediate rows need not have zero imaginary part. -/
theorem lower_re (x v : ℕ → ℂ) (hx : ∀ k, (x k).im = 0) (i : ℕ) :
    (lower x v i).re = lower (fun k => (x k).re) (fun k => (v k).re) i := by
  simp [lower, Complex.re_sum, Complex.mul_re, hx]

theorem upper_re (L : ℕ) (x v : ℕ → ℂ) (hx : ∀ k, (x k).im = 0) (i : ℕ) :
    (upper L x v i).re = upper L (fun k => (x k).re) (fun k => (v k).re) i := by
  simp [upper, Complex.re_sum, Complex.mul_re, hx]

/-- Projecting a complex stage bound to the real cell contract loses no precision. -/
theorem lower_real_error (x v : ℕ → ℂ) (hx : ∀ k, (x k).im = 0)
    (z : ℂ) (i : ℕ) (ε : ℝ) (h : ‖z - lower x v i‖ ≤ ε) :
    |z.re - lower (fun k => (x k).re) (fun k => (v k).re) i| ≤ ε := by
  have he := (Complex.abs_re_le_norm (z - lower x v i)).trans h
  simpa only [Complex.sub_re, lower_re x v hx i] using he

theorem upper_real_error (L : ℕ) (x v : ℕ → ℂ) (hx : ∀ k, (x k).im = 0)
    (z : ℂ) (i : ℕ) (ε : ℝ) (h : ‖z - upper L x v i‖ ≤ ε) :
    |z.re - upper L (fun k => (x k).re) (fun k => (v k).re) i| ≤ ε := by
  have he := (Complex.abs_re_le_norm (z - upper L x v i)).trans h
  simpa only [Complex.sub_re, upper_re L x v hx i] using he

/-- The upper arithmetic obligation in the real cell contract, on the actual
stored numerator. The real-generator hypothesis does not constrain FFT noise. -/
theorem scaledUpper_real_error (a b : ℝ) {q l M L : ℕ} (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (n : ℕ) (hn : n < M) (hreal : ∀ k, (value q (block (X n) k)).im = 0)
    (i : ℕ) (hi : i < L) :
    |(scaledUpper (a : ℂ) (b : ℂ) q l L X V n i).re -
      upper L (fun k => a * (value q (block (X n) k)).re)
        (fun k => b * (value q (block (V n) k)).re) i| ≤
      ‖(a : ℂ) * (b : ℂ)‖ * (2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q) := by
  have hx : ∀ k, ((a : ℂ) * value q (block (X n) k)).im = 0 := by
    intro k
    simp [Complex.mul_im, hreal]
  have h := upper_real_error L _ _ hx _ i _
    (scaledUpper_error (a : ℂ) (b : ℂ) hpad X V hlenX hlenV n hn i hi)
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using h

/-- The lower arithmetic obligation in the real cell contract, relative to the
computed upper real parts and the word actually published by the machine. -/
theorem scaledPair_real_output_error {A q l w M L : ℕ} (hA : 4 ≤ A) (hw : q + 2 ≤ w)
    (a b : ℝ) (hpad : L + L ≤ 2 ^ l + 1) (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (tail : List (Fin (A + 4))) (n : ℕ) (hn : n < M)
    (hreal : ∀ k, (value q (block (X n) k)).im = 0) (i : Fin L) :
    let z := value q (decodeWord (((cstream A w (pairRows q l M L X V) ++ tail).drop
      ((n * L + (L - 1 - i.val)) * w)).take w))
    |(((a : ℂ) * ((a : ℂ) * (b : ℂ) * ((2 ^ l : ℕ) : ℂ))) * (((2 ^ l : ℕ) : ℂ) * z)).re -
      lower (fun k => a * (value q (block (X n) k)).re)
        (fun k => (scaledUpper (a : ℂ) (b : ℂ) q l L X V n k).re) i.val| ≤
      ‖(a : ℂ) * ((a : ℂ) * (b : ℂ) * ((2 ^ l : ℕ) : ℂ))‖ *
        (2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q) := by
  dsimp only
  have hx : ∀ k, ((a : ℂ) * value q (block (X n) k)).im = 0 := by
    intro k
    simp [Complex.mul_im, hreal]
  have h := lower_real_error _ _ hx _ i.val _
    (scaledPair_output_error hA hw (a : ℂ) (b : ℂ) hpad X V hlenX hlenV hX hV tail n hn i)
  have hxre : (fun k => ((a : ℂ) * value q (block (X n) k)).re) =
      (fun k => a * (value q (block (X n) k)).re) := by
    funext k
    simp [Complex.mul_re]
  rw [hxre] at h
  exact h

/-- Real raw generator words establish the real-stage premise also outside their support. -/
theorem value_block_im_zero (q : ℕ) (x : List GaussianInt)
    (hx : ∀ z ∈ x, z.im = 0) (k : ℕ) : (value q (block x k)).im = 0 := by
  unfold block
  cases h : x[k]? with
  | none => simp [value]
  | some z => simp [value, hx z (List.mem_of_getElem? h)]

/-- With generator scale 2 and input scale V, the first stage spends this tolerance. -/
theorem upper_cell_scale (q l : ℕ) (V : ℝ) (hV : 0 ≤ V) :
    ‖(2 : ℂ) * (V : ℂ)‖ * (2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q) =
      4 * V * (2 ^ l : ℕ) / (2 : ℝ) ^ q := by
  norm_num [norm_mul, abs_of_nonneg hV]
  ring

/-- The second stage spends an additional generator factor and ring factor. -/
theorem lower_cell_scale (q l : ℕ) (V : ℝ) (hV : 0 ≤ V) :
    ‖(2 : ℂ) * (2 * (V : ℂ) * ((2 ^ l : ℕ) : ℂ))‖ *
      (2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q) =
      8 * V * (2 ^ l : ℕ) ^ 2 / (2 : ℝ) ^ q := by
  norm_num [norm_mul, abs_of_nonneg hV]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
