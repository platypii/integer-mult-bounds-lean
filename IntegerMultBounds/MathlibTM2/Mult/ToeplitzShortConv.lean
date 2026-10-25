module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvDecode
public import IntegerMultBounds.NLogN.ToeplitzApply

/-! # Triangular Toeplitz stages on the executed short-convolution stream

The generator stays in forward order. An upper stage reverses the input and
reads coefficient L-1-i; a lower stage reads coefficient i. Reversal and crop
execution belong to the caller and are not free operations in this interface.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN.ToeplitzInverse
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv Finset

/-- A lower stage is the initial segment of an ordinary linear convolution. -/
theorem lower_convolution {K : Type*} [Field K] (x v : ℕ → K) (i : ℕ) :
    lower x v i = ∑ k ∈ range (i + 1), x k * v (i - k) := by
  unfold lower
  rw [← sum_range_reflect]
  apply sum_congr rfl
  intro k hk
  have hk' := mem_range.mp hk
  have hsub : i + 1 - 1 - k = i - k := by omega
  have hback : i - (i + 1 - 1 - k) = k := by omega
  rw [hback, hsub]

/-- Upper stages need a reversed input, not a different convolution supplier. -/
theorem upper_convolution {K : Type*} [Field K] (L : ℕ) (x v : ℕ → K) (i : ℕ) (hi : i < L) :
    upper L x v i = ∑ k ∈ range (L - 1 - i + 1), x k * v (L - 1 - (L - 1 - i - k)) := by
  unfold upper
  rw [sum_Ico_eq_sum_range]
  have hlen : L - i = L - 1 - i + 1 := by omega
  rw [hlen]
  apply sum_congr rfl
  intro k hk
  have hk' := mem_range.mp hk
  have hshift : i + k - i = k := by omega
  have hback : L - 1 - (L - 1 - i - k) = i + k := by omega
  rw [hshift, hback]

/-- Reversing coefficient words reverses their values without reversing bits within a word. -/
theorem block_reverse (v : List GaussianInt) (k : ℕ) (hk : k < v.length) :
    block v.reverse k = block v (v.length - 1 - k) := by
  have hk' : k < v.reverse.length := by simpa using hk
  have hrev : v.length - 1 - k < v.length := by omega
  simp only [block, List.getElem?_eq_getElem hk', List.getElem?_eq_getElem hrev, Option.getD_some]
  rw [List.getElem_reverse]

/-- Decode a lower stage directly from the actual S1 output symbols. -/
theorem lower_output_error {A q l w M L : ℕ} (hA : 4 ≤ A) (hw : q + 2 ≤ w)
    (hpad : L + L ≤ 2 ^ l + 1) (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (tail : List (Fin (A + 4))) (n : ℕ) (hn : n < M) (i : ℕ) (hi : i < L) :
    ‖((2 ^ l : ℕ) : ℂ) * value q (decodeWord
      (((cstream A w (Fixed.result q l M X V) ++ tail).drop
        ((n * 2 ^ l + i) * w)).take w)) -
      lower (fun k => value q (block (X n) k)) (fun k => value q (block (V n) k)) i‖ ≤
        2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q := by
  have hiR : i < 2 ^ l := by omega
  rw [lower_convolution]
  exact Fixed.output_err hA hw hpad X V hlenX hlenV hX hV tail n hn ⟨i, hiR⟩

/-- The rounded numerator already has the upper-stage error before any tape encoding. -/
theorem upper_coeff_error (q l L : ℕ) (x v : List GaussianInt)
    (hlenX : x.length = L) (hlenV : v.length = L) (hpad : L + L ≤ 2 ^ l + 1)
    (i : ℕ) (hi : i < L) :
    ‖((2 ^ l : ℕ) : ℂ) * value q (coeff q l x v.reverse
        ⟨L - 1 - i, by omega⟩) -
      upper L (fun k => value q (block x k)) (fun k => value q (block v k)) i‖ ≤
        2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q := by
  have hxy : x.length + v.reverse.length ≤ 2 ^ l + 1 := by simpa [hlenX, hlenV] using hpad
  have hsum : (∑ k ∈ range (L - 1 - i + 1),
      value q (block x k) * value q (block v.reverse (L - 1 - i - k))) =
      upper L (fun k => value q (block x k)) (fun k => value q (block v k)) i := by
    rw [upper_convolution L _ _ i hi]
    apply sum_congr rfl
    intro k hk
    have hk' := mem_range.mp hk
    rw [block_reverse v _ (by rw [hlenV]; omega), hlenV]
  have h := coeff_err q l x v.reverse hxy ⟨L - 1 - i, by omega⟩
  simpa only [hsum] using h

/-- Decode an upper stage from the same S1 stream, with each input row reversed. -/
theorem upper_output_error {A q l w M L : ℕ} (hA : 4 ≤ A) (hw : q + 2 ≤ w)
    (hpad : L + L ≤ 2 ^ l + 1) (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (tail : List (Fin (A + 4))) (n : ℕ) (hn : n < M) (i : ℕ) (hi : i < L) :
    ‖((2 ^ l : ℕ) : ℂ) * value q (decodeWord
      (((cstream A w (Fixed.result q l M X (fun n => (V n).reverse)) ++ tail).drop
        ((n * 2 ^ l + (L - 1 - i)) * w)).take w)) -
      upper L (fun k => value q (block (X n) k)) (fun k => value q (block (V n) k)) i‖ ≤
        2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q := by
  have hiR : L - 1 - i < 2 ^ l := by omega
  have hlenY : ∀ n < M, ((V n).reverse).length = L := by simpa using hlenV
  have hY : ∀ n < M, ∀ z ∈ (V n).reverse,
      z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q) := by
    intro j hj z hz
    exact hV j hj z (List.mem_reverse.mp hz)
  rw [Fixed.output_coeff hA hw hpad X (fun n => (V n).reverse) hlenX hlenY hX hY
    tail n hn ⟨L - 1 - i, hiR⟩]
  exact upper_coeff_error q l L (X n) (V n) (hlenX n hn) (hlenV n hn) hpad i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
