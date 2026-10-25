module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarStream
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMergeRange

/-! # Scalar-word bounds for the actual merged branch numerators -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.Spec.SignedRingProduct

/-- The actual compact branch numerators have decoded norm at most one. -/
theorem pairNumerator_norm {q l M L : ℕ} (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (i : Fin (M * L)) : ‖value q (pairNumerator q l M L X V i)‖ ≤ 1 := by
  have hd : DiskGrid q (fun _ : Fin 1 => (pairNumerator q l M L X V i).re)
      (fun _ => (pairNumerator q l M L X V i).im) :=
    fun _ => pairNumerator_disk hpad X V hlenX hlenV hX hV i
  simpa only [value, gridPoly] using hd.norm_le 0

/-- The merge does not amplify the raw numerator norm beyond two. -/
theorem branchDifference_norm {q l M L : ℕ} (hpad : L + L ≤ 2 ^ l + 1)
    (X Z V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenZ : ∀ n < M, (Z n).length = L)
    (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hZ : ∀ n < M, ∀ z ∈ Z n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q)) :
    ∀ z ∈ branchDifference q l M L X Z V, ‖value q z‖ ≤ 2 := by
  intro z hz
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
  rw [value_sub]
  exact (norm_sub_le _ _).trans (by
    have hx := pairNumerator_norm hpad X V hlenX hlenV hX hV i
    have hz := pairNumerator_norm hpad Z V hlenZ hlenV hZ hV i
    linarith)

/-- Signed scalar decoding and its grid error on the branch stream require only
the proved operand bounds, a bounded stored scalar and the selected word width. -/
theorem branchScalar_output_error {A q l w M L : ℕ} (hA : 4 ≤ A) (hw : q + 4 ≤ w)
    (hpad : L + L ≤ 2 ^ l + 1) (X Z V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenZ : ∀ n < M, (Z n).length = L)
    (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hZ : ∀ n < M, ∀ z ∈ Z n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (a : GaussianInt) (ha : ‖value q a‖ ≤ 2) (tail : List (Fin (A + 4))) (i : Fin (M * L)) :
    ‖value q (decodeWord (((cstream A w ((branchDifference q l M L X Z V).map
        (fun x => tdivN q (x * a))) ++ tail).drop (i.val * w)).take w)) -
      (value q (pairNumerator q l M L X V i) - value q (pairNumerator q l M L Z V i)) * value q a‖ ≤
      2 / (2 : ℝ) ^ q := by
  have h := realScalar_output_error_bounded hA hw (branchDifference q l M L X Z V) a
    (branchDifference_norm hpad X Z V hlenX hlenZ hlenV hX hZ hV) ha tail i.val (by simp [branchDifference])
  simpa only [branchDifference, List.getElem_ofFn, value_sub] using h

/-- Scaling the decoded scalar result supplies the real merge obligation on the
computed branch outputs. The stored reciprocal is real; intermediate FFT
numerators may still have imaginary noise. -/
theorem scaled_scalar_real_error (x z y a : ℂ) (scale ε : ℝ)
    (hscale : 0 ≤ scale) (ha : a.im = 0) (h : ‖y - (x - z) * a‖ ≤ ε) :
    |scale * y.re - a.re * (scale * x.re - scale * z.re)| ≤ scale * ε := by
  have hre : |y.re - a.re * (x.re - z.re)| ≤ ε := by
    have hr := (Complex.abs_re_le_norm (y - (x - z) * a)).trans h
    simpa only [Complex.sub_re, Complex.mul_re, Complex.sub_im, ha,
      mul_zero, sub_zero, mul_comm] using hr
  calc
    |scale * y.re - a.re * (scale * x.re - scale * z.re)| =
        |scale * (y.re - a.re * (x.re - z.re))| := by congr 1; ring
    _ = scale * |y.re - a.re * (x.re - z.re)| := by
      rw [abs_mul, abs_of_nonneg hscale]
    _ ≤ scale * ε := mul_le_mul_of_nonneg_left hre hscale

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
