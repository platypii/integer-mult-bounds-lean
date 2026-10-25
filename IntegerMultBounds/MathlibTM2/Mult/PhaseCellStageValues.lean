module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairScale
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarRange

/-! # Real cell stages represented by the executed numerator banks

Compact lower rows are stored in reverse coordinate order. These lemmas identify
that layout with the real stages required by `CellRun.Valid`; they do not assume
that an S1 result equals a scalar-rounding reference.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.ToeplitzInverse

/-- Position of a cell coordinate in the compact reversed-row stream. -/
def cellIndex {M L : ℕ} (n : Fin M) (i : Fin L) : Fin (M * L) :=
  ⟨n.val * L + (L - 1 - i.val), by
    have hn := Nat.mul_le_mul_right L (show n.val + 1 ≤ M by omega)
    simp only [Nat.add_mul, Nat.one_mul] at hn
    have hi := i.isLt
    omega⟩

/-- A compact branch word decodes to its numerator without aliasing. -/
theorem pairNumerator_word {A q l w M L : ℕ} (hA : 4 ≤ A) (hw : q + 2 ≤ w)
    (hpad : L + L ≤ 2 ^ l + 1) (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (tail : List (Fin (A + 4))) (i : Fin (M * L)) :
    decodeWord (((cstream A w (pairRows q l M L X V) ++ tail).drop (i.val * w)).take w) =
      pairNumerator q l M L X V i := by
  have hr : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  have hlen := pairRows_length (show L ≤ 2 ^ l by omega) q M X V
  have hi : i.val < (pairRows q l M L X V).length := by simpa only [hlen] using i.isLt
  rw [cstream_word w _ tail i.val hi]
  have hblock : (pairRows q l M L X V)[i.val] = pairNumerator q l M L X V i := by
    simp [pairNumerator, block, hi]
  rw [hblock]
  exact decodeWord_of_fits hA (by omega) _
    (fits_of_disk hw _ (pairNumerator_disk hpad X V hlenX hlenV hX hV i))

/-- The first triangular stage uses generator scale two and input scale `B`.
The same theorem applies to each of the two generator branches. -/
theorem upperNumerator_real_error {q l M L : ℕ} (B : ℝ) (hB : 0 ≤ B)
    (hpad : L + L ≤ 2 ^ l + 1) (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hreal : ∀ n < M, ∀ z ∈ X n, z.im = 0) (n : Fin M) (i : Fin L) :
    |(scaledUpper (2 : ℂ) (B : ℂ) q l L X V n i).re -
      upper L (fun k => 2 * (value q (block (X n) k)).re)
        (fun k => B * (value q (block (V n) k)).re) i.val| ≤
      4 * B * (2 ^ l : ℕ) / (2 : ℝ) ^ q := by
  have h := scaledUpper_real_error 2 B hpad X V hlenX hlenV n n.isLt
    (value_block_im_zero q (X n) (hreal n n.isLt)) i i.isLt
  have htwo : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  rw [htwo, upper_cell_scale q l B hB] at h
  exact h

/-- The real lower stage is the decoded compact numerator times its two ring
factors and two generator factors. It acts on the computed upper row. -/
theorem pairNumerator_real_error {q l M L : ℕ} (B : ℝ) (hB : 0 ≤ B)
    (hpad : L + L ≤ 2 ^ l + 1) (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hreal : ∀ n < M, ∀ z ∈ X n, z.im = 0) (n : Fin M) (i : Fin L) :
    |4 * B * (2 ^ l : ℕ) ^ 2 * (value q (pairNumerator q l M L X V (cellIndex n i))).re -
      lower (fun k => 2 * (value q (block (X n) k)).re)
        (fun k => (scaledUpper (2 : ℂ) (B : ℂ) q l L X V n k).re) i.val| ≤
      8 * B * (2 ^ l : ℕ) ^ 2 / (2 : ℝ) ^ q := by
  have h := scaledPair_real_output_error (A := 4) (w := q + 2) (by omega) (by omega)
    2 B hpad X V hlenX hlenV hX hV [] n n.isLt
    (value_block_im_zero q (X n) (hreal n n.isLt)) i
  have hw := pairNumerator_word (A := 4) (w := q + 2) (by omega) (by omega)
    hpad X V hlenX hlenV hX hV [] (cellIndex n i)
  change decodeWord (((cstream 4 (q + 2) (pairRows q l M L X V) ++ []).drop
    ((n.val * L + (L - 1 - i.val)) * (q + 2))).take (q + 2)) = _ at hw
  dsimp only at h
  rw [hw] at h
  have htwo : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  rw [htwo] at h
  rw [lower_cell_scale q l B hB] at h
  have htwore : (2 : ℂ).re = 2 := by norm_num
  have htwoim : (2 : ℂ).im = 0 := by norm_num
  convert h using 1 <;> simp only [Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
    htwore, htwoim, mul_zero, zero_mul, sub_zero]
  congr 1
  ring

/-- The actual scalar output supplies the merge stage after the same scale as
the two lower branches. The bound concerns operations on computed inputs. -/
theorem branchScalar_real_error {A q l w M L : ℕ} (hA : 4 ≤ A) (hw : q + 4 ≤ w)
    (B : ℝ) (hB : 0 ≤ B) (hpad : L + L ≤ 2 ^ l + 1)
    (X Z V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenZ : ∀ n < M, (Z n).length = L)
    (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hZ : ∀ n < M, ∀ z ∈ Z n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (a : GaussianInt) (ha : ‖value q a‖ ≤ 2) (har : a.im = 0)
    (tail : List (Fin (A + 4))) (i : Fin (M * L)) :
    let scale : ℝ := 4 * B * (2 ^ l : ℕ) ^ 2
    let y := value q (decodeWord (((cstream A w ((branchDifference q l M L X Z V).map
      (fun x => tdivN q (x * a))) ++ tail).drop (i.val * w)).take w))
    |scale * y.re - (value q a).re *
      (scale * (value q (pairNumerator q l M L X V i)).re -
        scale * (value q (pairNumerator q l M L Z V i)).re)| ≤
      8 * B * (2 ^ l : ℕ) ^ 2 / (2 : ℝ) ^ q := by
  dsimp only
  have hreal : (value q a).im = 0 := by simp [value, har]
  have h := scaled_scalar_real_error _ _ _ (value q a) (4 * B * (2 ^ l : ℕ) ^ 2)
    (2 / (2 : ℝ) ^ q) (by positivity) hreal
    (branchScalar_output_error hA hw hpad X Z V hlenX hlenZ hlenV hX hZ hV a ha tail i)
  convert h using 1 <;> ring

/-- One common precision pays for the rescaled lower and scalar stages when
the input magnitude is bounded by `2^b`. This is arithmetic precision, independent
of the selected coefficient precision and address width. -/
theorem cell_stage_precision {B : ℝ} {b l j q : ℕ} (hB : B ≤ (2 : ℝ) ^ b)
    (hq : b + 2 * l + j + 3 ≤ q) :
    8 * B * (2 ^ l : ℕ) ^ 2 / (2 : ℝ) ^ q ≤ 1 / (2 : ℝ) ^ j := by
  have hpow : (2 : ℝ) ^ (b + 2 * l + j + 3) ≤ 2 ^ q :=
    pow_le_pow_right₀ (by norm_num) hq
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ q)
    (by positivity : (0 : ℝ) < 2 ^ j)).mpr
  calc
    8 * B * (2 ^ l : ℕ) ^ 2 * (2 : ℝ) ^ j ≤
        8 * (2 : ℝ) ^ b * (2 ^ l : ℕ) ^ 2 * (2 : ℝ) ^ j := by gcongr
    _ = (2 : ℝ) ^ (b + 2 * l + j + 3) := by
      simp only [Nat.cast_pow, Nat.cast_ofNat, two_mul, pow_add]
      ring
    _ ≤ 1 * (2 : ℝ) ^ q := by simpa only [one_mul] using hpow

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
