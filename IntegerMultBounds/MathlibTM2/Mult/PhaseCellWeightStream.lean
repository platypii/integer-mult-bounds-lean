module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarStream
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputValue

/-! # Executed products with aligned real weights and an explicit normalization

The existing multiplier stream supplies the machine. The grid precision `q`,
extra normalization shift `b`, word width and magnitude exponents are separate.
Its actual truncation is toward zero; no equality with rational floor rounding
is used.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}
  {cr : CR → Fin T} {ι : Fin 64 → Fin T}

/-- Aligned varying real weights use the existing stream engine. -/
noncomputable def realWeightStream (cr : CR → Fin T) (ι : Fin 64 → Fin T)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  cmulStream cr (rmulOne ι hι hT hQ cr)

/-- One right shift combines fixed-point multiplication and normalization. -/
theorem value_normalized_product (q b : ℕ) (x a : GaussianInt) :
    value q (tdivN (q + b) (x * a)) = rhoC q (value q x * value q a / (2 : ℂ) ^ b) := by
  rw [value_tdivN]
  congr 1
  simp only [value_eq_grid, map_mul, pow_add]
  field_simp

/-- The actual normalized product spends the grid tolerance at the output
precision, independently of the additional normalization shift. -/
theorem normalized_product_error (q b : ℕ) (x a : GaussianInt) :
    ‖value q (tdivN (q + b) (x * a)) - value q x * value q a / (2 : ℂ) ^ b‖ ≤
      2 / (2 : ℝ) ^ q := by
  rw [value_normalized_product]
  exact norm_rhoC_sub_le_two q _

/-- Truncation does not increase the normalized product magnitude. -/
theorem normalized_product_norm (q b e f : ℕ) (x a : GaussianInt)
    (hx : ‖value q x‖ ≤ (2 : ℝ) ^ e) (ha : ‖value q a‖ ≤ (2 : ℝ) ^ f) :
    ‖value q (tdivN (q + b) (x * a))‖ ≤ (2 : ℝ) ^ (e + f) / (2 : ℝ) ^ b := by
  rw [value_normalized_product]
  apply (norm_rhoC_le q _).trans
  rw [norm_div, norm_mul, norm_pow, Complex.norm_ofNat, pow_add]
  exact div_le_div_of_nonneg_right (mul_le_mul hx ha (norm_nonneg _) (by positivity)) (by positivity)

/-- The actual normalized multiplier output meets S1's disk contract. -/
theorem normalized_product_disk (q e f : ℕ) (x a : GaussianInt)
    (hx : ‖value q x‖ ≤ (2 : ℝ) ^ e) (ha : ‖value q a‖ ≤ (2 : ℝ) ^ f) :
    (tdivN (q + (e + f + 1)) (x * a)).re ^ 2 +
      (tdivN (q + (e + f + 1)) (x * a)).im ^ 2 ≤ (2 : ℤ) ^ (2 * q) := by
  apply disk_of_norm_value_le
  apply (normalized_product_norm q (e + f + 1) e f x a hx ha).trans
  apply (div_le_one (by positivity)).mpr
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- Undoing the normalization gives the real input-stage error on computed
operands. Imaginary FFT components need not vanish in the first operand. -/
theorem normalized_product_real_error (q b : ℕ) (x a : GaussianInt) (har : a.im = 0) :
    |(2 : ℝ) ^ b * (value q (tdivN (q + b) (x * a))).re -
      (value q x).re * (value q a).re| ≤ (2 : ℝ) ^ b * (2 / (2 : ℝ) ^ q) := by
  have hpow : (2 : ℂ) ^ b = Complex.ofReal ((2 : ℝ) ^ b) := by norm_cast
  have hreal : (value q a).im = 0 := by simp [value, har]
  have h := (Complex.abs_re_le_norm
    (value q (tdivN (q + b) (x * a)) - value q x * value q a / (2 : ℂ) ^ b)).trans
    (normalized_product_error q b x a)
  have htarget : (value q x * value q a / (2 : ℂ) ^ b).re =
      (value q x).re * (value q a).re / (2 : ℝ) ^ b := by
    rw [hpow, Complex.div_ofReal_re, Complex.mul_re, hreal, mul_zero, sub_zero]
  rw [Complex.sub_re, htarget] at h
  have hp : (0 : ℝ) < 2 ^ b := by positivity
  calc
    _ = |(2 : ℝ) ^ b * ((value q (tdivN (q + b) (x * a))).re -
        (value q x).re * (value q a).re / (2 : ℝ) ^ b)| := by
      congr 1
      field_simp
    _ = (2 : ℝ) ^ b * |(value q (tdivN (q + b) (x * a))).re -
        (value q x).re * (value q a).re / (2 : ℝ) ^ b| := by rw [abs_mul, abs_of_pos hp]
    _ ≤ _ := mul_le_mul_of_nonneg_left h hp.le

/-- A power magnitude bound gives a concrete signed-word allowance. -/
theorem fits_of_value_power {q w e : ℕ} (hw : q + e + 2 ≤ w) (x : GaussianInt)
    (hx : ‖value q x‖ ≤ (2 : ℝ) ^ e) : Fits w x := by
  apply fits_of_norm_value_bound x ((2 : ℝ) ^ e) hx
  rw [← pow_add]
  exact pow_lt_pow_right₀ (by norm_num) (by omega)

/-- All normalized products fit with the same allowance as their unnormalized
magnitude bound; no output-fit premise is needed. -/
theorem normalized_product_fits {q w b e f : ℕ} (hw : q + (e + f) + 2 ≤ w)
    (x a : GaussianInt) (hx : ‖value q x‖ ≤ (2 : ℝ) ^ e) (ha : ‖value q a‖ ≤ (2 : ℝ) ^ f) :
    Fits w (tdivN (q + b) (x * a)) := by
  apply fits_of_value_power hw
  exact (normalized_product_norm q b e f x a hx ha).trans
    (div_le_self (by positivity) (one_le_pow₀ (by norm_num)))

/-- The shared multiplier stream restores both operands and all scratch.
Signed-word bounds suffice at every truncation precision, including zero. -/
theorem realWeightStream_exec_of_fits
    (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p w : ℕ} (hw : 1 ≤ w) (hshift : p ≤ w)
    (xs as : List GaussianInt) (hlen : xs.length = as.length)
    (hxs : ∀ x ∈ xs, Fits w x)
    (has : ∀ a ∈ as, Fits w a ∧ a.im = 0)
    (v : HS T Q A U) (S : Stacks T A) (hclean : CClean ι S)
    (hr : Ready (fun r => S.R (cr r)) w p)
    (hx : S.R (cr .xs) = cstream A w xs) (hy : S.R (cr .ys) = cstream A w as)
    (hxsv : S.R (cr .xsv) = []) (hysv : S.R (cr .ysv) = []) (hacc : S.R (cr .acc) = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ xs.length * (rmulCost w + 6 * w + 2) + 8 ∧
      Exec body (realWeightStream cr ι hι hT hQ) (mk v S) m
        (mk v' { S with R := (Function.update S.R (cr .out)
          (cstream A w (List.zipWith (fun x a => tdivN p (x * a)) xs as) ++ S.R (cr .out))) }) := by
  have hex := rmulStream_runs (body := body) hcr hdisj hι hT hQ hA hr hw hshift xs as hlen hxs has
    hx hy hxsv hysv hacc
  obtain ⟨v', S', m, hu, hm, he, hh, hf⟩ := hex v S hclean (fun _ => rfl)
  refine ⟨v', m, hu, hm, he.cast rfl ?_⟩
  apply congrArg (mk v')
  ext1
  · exact hf.1
  · exact hf.2.1
  · exact hf.2.2.1
  funext k
  change S'.R k = Function.update S.R (cr .out)
    (cstream A w (List.zipWith (fun x a => tdivN p (x * a)) xs as) ++ S.R (cr .out)) k
  by_cases hk : ∃ r, cr r = k
  · obtain ⟨r, rfl⟩ := hk
    rw [hh r]
    simp only [Function.update_apply, hcr.eq_iff]
  · have hnot : ∀ r, cr r ≠ k := by simpa using hk
    rw [hf.2.2.2 k hnot, Function.update_of_ne (hnot .out).symm]

/-- Both operand streams and every scratch port are restored. Only the ordered
output prefix changes. The precision counter is `q+b`, not silently `q`. -/
theorem realWeightStream_exec
    (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q b w e f : ℕ} (hw : q + (e + f) + 2 ≤ w) (hshift : q + b ≤ w)
    (xs as : List GaussianInt) (hlen : xs.length = as.length)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ (2 : ℝ) ^ e)
    (has : ∀ a ∈ as, ‖value q a‖ ≤ (2 : ℝ) ^ f ∧ a.im = 0)
    (v : HS T Q A U) (S : Stacks T A) (hclean : CClean ι S)
    (hr : Ready (fun r => S.R (cr r)) w (q + b))
    (hx : S.R (cr .xs) = cstream A w xs) (hy : S.R (cr .ys) = cstream A w as)
    (hxsv : S.R (cr .xsv) = []) (hysv : S.R (cr .ysv) = []) (hacc : S.R (cr .acc) = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ xs.length * (rmulCost w + 6 * w + 2) + 8 ∧
      Exec body (realWeightStream cr ι hι hT hQ) (mk v S) m
        (mk v' { S with R := (Function.update S.R (cr .out)
          (cstream A w (List.zipWith (fun x a => tdivN (q + b) (x * a)) xs as) ++ S.R (cr .out))) }) := by
  exact realWeightStream_exec_of_fits hcr hdisj hι hT hQ hA (by omega) hshift xs as hlen
    (fun x hx => fits_of_value_power (by omega) x (hxs x hx))
    (fun a ha => ⟨fits_of_value_power (by omega) a (has a ha).1, (has a ha).2⟩)
    v S hclean hr hx hy hxsv hysv hacc

/-- Signed decoding of the actual output word has the normalized product error
under proved input magnitude and width bounds. -/
theorem realWeightStream_output_error {A q b w e f : ℕ} (hA : 4 ≤ A)
    (hw : q + (e + f) + 2 ≤ w) (xs as : List GaussianInt) (hlen : xs.length = as.length)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ (2 : ℝ) ^ e)
    (has : ∀ a ∈ as, ‖value q a‖ ≤ (2 : ℝ) ^ f)
    (tail : List (Fin (A + 4))) (i : ℕ) (hi : i < xs.length) :
    ‖value q (decodeWord (((cstream A w (List.zipWith (fun x a => tdivN (q + b) (x * a)) xs as) ++ tail).drop
      (i * w)).take w)) - value q xs[i] * value q as[i] / (2 : ℂ) ^ b‖ ≤ 2 / (2 : ℝ) ^ q := by
  have hi' : i < as.length := by omega
  rw [cstream_word w _ tail i (by simp [hlen, hi'])]
  simp only [List.getElem_zipWith]
  rw [decodeWord_of_fits hA (by omega) _ (normalized_product_fits hw _ _
    (hxs _ (List.getElem_mem hi)) (has _ (List.getElem_mem hi')))]
  exact normalized_product_error q b _ _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
