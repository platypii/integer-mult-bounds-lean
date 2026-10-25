module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUpperCrop

/-! # Compacted upper rows as normalized operands for the next S1 call -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.Spec.SignedRingProduct

/-- The actual compacted row, without a prepared coefficient or range oracle. -/
def upperOperand (q l L : ℕ) (X V : ℕ → List GaussianInt) (n : ℕ) : List GaussianInt :=
  sliceCoeffs 0 L (List.ofFn (coeff q l (X n) (V n).reverse))

theorem upperRows_flatMap (q l M L : ℕ) (X V : ℕ → List GaussianInt) :
    upperRows q l M L X V = (List.range M).flatMap (upperOperand q l L X V) := rfl

theorem upperOperand_length {q l L : ℕ} (hL : L ≤ 2 ^ l)
    (X V : ℕ → List GaussianInt) (n : ℕ) :
    (upperOperand q l L X V n).length = L := by
  apply sliceCoeffs_length
  simpa using hL

/-- Each row independently satisfies the next product's normalized-input hypothesis. -/
theorem upperOperand_disk {q l M L : ℕ} (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q)) :
    ∀ n < M, ∀ z ∈ upperOperand q l L X V n,
      z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q) := by
  intro n hn z hz
  apply upperRows_disk hpad X V hlenX hlenV hX hV z
  rw [upperRows_flatMap]
  exact List.mem_flatMap.mpr ⟨n, List.mem_range.mpr hn, hz⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
