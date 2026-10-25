module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMergedBranches

/-! # Exact signed decoding of the actual merged branch stream -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.Spec.SignedRingProduct

/-- Cropping the second triangular product preserves the normalized numerator disk. -/
theorem pairNumerator_disk {q l M L : ℕ} (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (i : Fin (M * L)) :
    (pairNumerator q l M L X V i).re ^ 2 + (pairNumerator q l M L X V i).im ^ 2 ≤ (2 : ℤ) ^ (2 * q) := by
  have hr : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  have hL : L ≤ 2 ^ l := by omega
  have hrows := sliceStream_disk (show 0 + L ≤ 2 ^ l by omega)
    (fun n => coeff q l (X n) (upperOperand q l L X V n))
    (lower_records_disk hpad X (upperOperand q l L X V) hlenX
      (fun n _ => upperOperand_length hL X V n) hX
      (upperOperand_disk hpad X V hlenX hlenV hX hV))
  have hi : i.val < (pairRows q l M L X V).length := by
    rw [pairRows_length hL]
    exact i.isLt
  unfold pairNumerator block
  rw [List.getElem?_eq_getElem hi, Option.getD_some]
  exact hrows _ (List.getElem_mem hi)

/-- A normalized Gaussian numerator fits with two sign/guard bits. -/
theorem fits_of_disk {q w : ℕ} (hw : q + 2 ≤ w) (z : GaussianInt)
    (hz : z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q)) : Fits w z := by
  have hd : DiskGrid q (fun _ : Fin 1 => z.re) (fun _ => z.im) := fun _ => hz
  obtain ⟨hre, him⟩ := hd.abs_le 0
  have hp : (2 : ℤ) ^ q < 2 ^ (w - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  exact ⟨hre.trans_lt hp, him.trans_lt hp⟩

/-- One extra guard bit makes the merged machine output the exact signed
branch difference. The original output suffix is arbitrary. -/
theorem branchDifference_word {A q l w M L : ℕ} (hA : 4 ≤ A) (hw : q + 3 ≤ w)
    (hpad : L + L ≤ 2 ^ l + 1) (X Z V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenZ : ∀ n < M, (Z n).length = L)
    (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hZ : ∀ n < M, ∀ z ∈ Z n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (tail : List (Fin (A + 4))) (i : Fin (M * L)) :
    decodeWord (((cstream A w (branchDifference q l M L X Z V) ++ tail).drop (i.val * w)).take w) =
      pairNumerator q l M L X V i - pairNumerator q l M L Z V i := by
  rw [cstream_word w _ tail i.val (by simp [branchDifference])]
  simp only [branchDifference, List.getElem_ofFn]
  apply decodeWord_of_fits hA (by omega)
  apply fits_sub (by omega)
  · exact fits_of_disk (by omega) _ (pairNumerator_disk hpad X V hlenX hlenV hX hV i)
  · exact fits_of_disk (by omega) _ (pairNumerator_disk hpad Z V hlenZ hlenV hZ hV i)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
