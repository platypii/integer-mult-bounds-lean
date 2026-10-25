module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightStream

/-! # The executed normalized input-weight stage

Reciprocal table words are constructed from rational weights. A lower bound on
the weights and an RHS magnitude bound discharge multiplier fits and the S1
output disk. Setup execution and fixed-bank routing remain caller obligations.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- The actual reciprocal-weight table, at the arithmetic precision. -/
def reciprocalWeightWords (q : ℕ) (ds : List ℚ) : List GaussianInt :=
  ds.map (reciprocalWeightWord q)

/-- Numerators produced by the existing multiplier with one combined shift. -/
def weightedInputNumerators (q cExp e : ℕ) (xs : List GaussianInt) (ds : List ℚ) : List GaussianInt :=
  List.zipWith (fun x a => tdivN (q + (cExp + e + 1)) (x * a)) xs (reciprocalWeightWords q ds)

theorem reciprocalWeightWords_norm {q e : ℕ} (ds : List ℚ)
    (hds : ∀ d ∈ ds, 1 / (2 : ℝ) ^ e ≤ (d : ℝ)) :
    ∀ a ∈ reciprocalWeightWords q ds, ‖value q a‖ ≤ (2 : ℝ) ^ e ∧ a.im = 0 := by
  intro a ha
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
  have hr := reciprocalWeightWord_bounds (q := q) d (hds d hd)
  refine ⟨?_, rfl⟩
  change ‖value q (rationalWord q (1 / d))‖ ≤ _
  rw [rationalWord_norm]
  simpa only [reciprocalWeightWord, abs_of_nonneg hr.1] using
    (show |(value q (reciprocalWeightWord q d)).re| ≤ (2 : ℝ) ^ e by
      rw [abs_of_nonneg hr.1]; exact hr.2)

@[simp] theorem weightedInputNumerators_length (q cExp e : ℕ) (xs : List GaussianInt) (ds : List ℚ)
    (hlen : xs.length = ds.length) : (weightedInputNumerators q cExp e xs ds).length = xs.length := by
  simp [weightedInputNumerators, reciprocalWeightWords, hlen]

/-- The actual executed result is already a legal raw S1 operand. -/
theorem weightedInputNumerators_disk {q cExp e : ℕ} (xs : List GaussianInt) (ds : List ℚ)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ (2 : ℝ) ^ cExp)
    (hds : ∀ d ∈ ds, 1 / (2 : ℝ) ^ e ≤ (d : ℝ)) :
    ∀ z ∈ weightedInputNumerators q cExp e xs ds, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q) := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
  have hil : i < min xs.length (reciprocalWeightWords q ds).length := by
    simpa only [weightedInputNumerators, List.length_zipWith] using hi
  simp only [weightedInputNumerators, List.getElem_zipWith]
  exact normalized_product_disk q cExp e _ _ (hxs _ (List.getElem_mem (by omega)))
    (reciprocalWeightWords_norm ds hds _ (List.getElem_mem (by omega))).1

theorem weightedInputNumerators_block {q cExp e : ℕ} (xs : List GaussianInt) (ds : List ℚ)
    (hlen : xs.length = ds.length) (i : ℕ) (hi : i < xs.length) :
    block (weightedInputNumerators q cExp e xs ds) i =
      tdivN (q + (cExp + e + 1)) (xs[i] * reciprocalWeightWord q ds[i]) := by
  have hout : i < (weightedInputNumerators q cExp e xs ds).length := by
    simpa only [weightedInputNumerators_length q cExp e xs ds hlen] using hi
  unfold block
  rw [List.getElem?_eq_getElem hout, Option.getD_some]
  have hzip : i < (List.zipWith (fun x a => tdivN (q + (cExp + e + 1)) (x * a))
      xs (reciprocalWeightWords q ds)).length := by
    simpa only [List.length_zipWith, reciprocalWeightWords, List.length_map, hlen, Nat.min_self] using
      (show i < ds.length by omega)
  change (List.zipWith (fun x a => tdivN (q + (cExp + e + 1)) (x * a))
    xs (reciprocalWeightWords q ds))[i]'hzip = _
  rw [List.getElem_zipWith]
  simp only [reciprocalWeightWords, List.getElem_map]

/-- The real input-scaling clause holds for machine truncation, independently of
whether it equals a rational-floor constructor. -/
theorem weightedInputNumerators_error {q cExp e : ℕ} (xs : List GaussianInt) (ds : List ℚ)
    (hlen : xs.length = ds.length) (i : ℕ) (hi : i < xs.length) :
    |(2 : ℝ) ^ (cExp + e + 1) *
        (value q (block (weightedInputNumerators q cExp e xs ds) i)).re -
      (value q xs[i]).re * (value q (reciprocalWeightWord q ds[i])).re| ≤
      (2 : ℝ) ^ (cExp + e + 1) * (2 / (2 : ℝ) ^ q) := by
  rw [weightedInputNumerators_block xs ds hlen i hi]
  exact normalized_product_real_error q (cExp + e + 1) _ _ rfl

/-- The combined-shift multiplier error fits the chosen real cell tolerance. -/
theorem normalized_weight_precision {b j q : ℕ} (hq : b + j + 1 ≤ q) :
    (2 : ℝ) ^ b * (2 / (2 : ℝ) ^ q) ≤ 1 / (2 : ℝ) ^ j := by
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hp : (2 : ℝ) ^ (b + j + 1) ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hq
  calc
    _ = (2 : ℝ) ^ (b + j + 1) := by rw [pow_add, pow_add]; ring
    _ ≤ _ := by simpa only [one_mul] using hp

theorem weightedInputNumerators_error_precision {q cExp e j : ℕ}
    (hq : cExp + e + 1 + j + 1 ≤ q) (xs : List GaussianInt) (ds : List ℚ)
    (hlen : xs.length = ds.length) (i : ℕ) (hi : i < xs.length) :
    |(2 : ℝ) ^ (cExp + e + 1) *
        (value q (block (weightedInputNumerators q cExp e xs ds) i)).re -
      (value q xs[i]).re * (value q (reciprocalWeightWord q ds[i])).re| ≤ 1 / (2 : ℝ) ^ j :=
  (weightedInputNumerators_error xs ds hlen i hi).trans (normalized_weight_precision hq)

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}
  {cr : CR → Fin T} {ι : Fin 64 → Fin T}

/-- Execute with constructed reciprocal table words. Their range and reality,
operand fits and the extra normalization counter are all explicit. -/
theorem weightedInputStream_exec
    (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q w cExp e : ℕ} (hw : q + (cExp + e) + 2 ≤ w)
    (xs : List GaussianInt) (ds : List ℚ) (hlen : xs.length = ds.length)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ (2 : ℝ) ^ cExp)
    (hds : ∀ d ∈ ds, 1 / (2 : ℝ) ^ e ≤ (d : ℝ))
    (v : HS T Q A U) (S : Stacks T A) (hclean : CClean ι S)
    (hr : Ready (fun r => S.R (cr r)) w (q + (cExp + e + 1)))
    (hx : S.R (cr .xs) = cstream A w xs) (hy : S.R (cr .ys) = cstream A w (reciprocalWeightWords q ds))
    (hxsv : S.R (cr .xsv) = []) (hysv : S.R (cr .ysv) = []) (hacc : S.R (cr .acc) = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ xs.length * (rmulCost w + 6 * w + 2) + 8 ∧
      Exec body (realWeightStream cr ι hι hT hQ) (mk v S) m
        (mk v' { S with R := (Function.update S.R (cr .out)
          (cstream A w (weightedInputNumerators q cExp e xs ds) ++ S.R (cr .out))) }) := by
  exact realWeightStream_exec (body := body) hcr hdisj hι hT hQ hA hw (by omega)
    xs (reciprocalWeightWords q ds) (by simp [reciprocalWeightWords, hlen]) hxs
    (reciprocalWeightWords_norm ds hds) v S hclean hr hx hy hxsv hysv hacc

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
