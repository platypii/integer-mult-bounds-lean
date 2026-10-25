module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOutputBounds

/-! # Encoded aligned weights and final output numerators -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- Actual grid words for the final similarity weights. -/
def outputWeightWords (q : ℕ) (ds : List ℚ) : List GaussianInt := ds.map (rationalWord q)

/-- The exact output list of rescaling followed by the aligned real multiplier. -/
def weightedOutputNumerators (q d : ℕ) (xs : List GaussianInt) (ds : List ℚ) : List GaussianInt :=
  List.zipWith (fun x a => tdivN q (x * a))
    (xs.map (fun x => (2 : GaussianInt) ^ d * x)) (outputWeightWords q ds)

@[simp] theorem weightedOutputNumerators_length (q d : ℕ) (xs : List GaussianInt) (ds : List ℚ)
    (hlen : xs.length = ds.length) : (weightedOutputNumerators q d xs ds).length = xs.length := by
  simp [weightedOutputNumerators, outputWeightWords, hlen]

theorem outputWeightWords_norm (q : ℕ) (ds : List ℚ)
    (hds : ∀ a ∈ ds, 0 ≤ (a : ℝ) ∧ (a : ℝ) ≤ 1) :
    ∀ a ∈ outputWeightWords q ds, ‖value q a‖ ≤ 1 ∧ a.im = 0 := by
  intro a ha
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
  exact ⟨output_weight_norm q d (hds d hd).1 (hds d hd).2, rfl⟩

theorem weightedOutputNumerators_block {q d : ℕ} (xs : List GaussianInt) (ds : List ℚ)
    (hlen : xs.length = ds.length) (i : ℕ) (hi : i < xs.length) :
    block (weightedOutputNumerators q d xs ds) i = weightedOutputNumerator q d xs[i] ds[i] := by
  have hout : i < (weightedOutputNumerators q d xs ds).length := by
    simpa only [weightedOutputNumerators_length q d xs ds hlen] using hi
  unfold block
  rw [List.getElem?_eq_getElem hout, Option.getD_some]
  have hzip : i < (List.zipWith (fun x a => tdivN q (x * a))
      (xs.map (fun x => (2 : GaussianInt) ^ d * x)) (outputWeightWords q ds)).length := by
    simpa only [List.length_zipWith, List.length_map, outputWeightWords, hlen, Nat.min_self] using
      (show i < ds.length by omega)
  change (List.zipWith (fun x a => tdivN q (x * a))
    (xs.map (fun x => (2 : GaussianInt) ^ d * x)) (outputWeightWords q ds))[i]'hzip = _
  rw [List.getElem_zipWith]
  simp only [outputWeightWords, List.getElem_map, weightedOutputNumerator]

/-- Actual word decoding of the final result has the full weighted error bound. -/
theorem weightedOutputNumerators_word_error {A q d w : ℕ} (hA : 4 ≤ A) (hw : q + d + 4 ≤ w)
    (xs : List GaussianInt) (ds : List ℚ) (hlen : xs.length = ds.length)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ 4)
    (hds : ∀ a ∈ ds, 0 ≤ (a : ℝ) ∧ (a : ℝ) ≤ 1)
    (tail : List (Fin (A + 4))) (i : ℕ) (hi : i < xs.length) :
    |(value q (decodeWord (((cstream A w (weightedOutputNumerators q d xs ds) ++ tail).drop (i * w)).take w))).re -
      (ds[i] : ℝ) * ((2 : ℝ) ^ d * (value q xs[i]).re)| ≤
      (2 + (2 : ℝ) ^ (d + 2)) / (2 : ℝ) ^ q := by
  have hi' : i < ds.length := by omega
  have hout : i < (weightedOutputNumerators q d xs ds).length := by
    simpa only [weightedOutputNumerators_length q d xs ds hlen] using hi
  have hblock := weightedOutputNumerators_block (q := q) (d := d) xs ds hlen i hi
  have helem : (weightedOutputNumerators q d xs ds)[i] = weightedOutputNumerator q d xs[i] ds[i] := by
    simpa only [block, List.getElem?_eq_getElem hout, Option.getD_some] using hblock
  rw [cstream_word w _ tail i hout, helem]
  rw [decodeWord_of_fits hA (by omega) _ (weightedOutputNumerator_fits hw _ _
    (hxs _ (List.getElem_mem hi)) (hds _ (List.getElem_mem hi')).1 (hds _ (List.getElem_mem hi')).2)]
  exact weightedOutputNumerator_error q d _ _ (hxs _ (List.getElem_mem hi))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
