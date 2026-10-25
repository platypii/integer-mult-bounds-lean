module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandProduct

/-! # Row structure and norm of the generated correlation stream -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.Spec.SignedRingProduct

def chirpCorrelationRows {r : ℕ} (M m : ℕ) (X : ℕ → Fin r → GaussianInt) : List (List GaussianInt) :=
  (List.range M).map fun n => correlationCoeffs m (List.ofFn (X n))

theorem chirpCorrelationRows_flatten {r : ℕ} (M m : ℕ) (X : ℕ → Fin r → GaussianInt) :
    (chirpCorrelationRows M m X).flatten = correlationStream M m X := by
  simp only [chirpCorrelationRows, correlationStream, List.flatMap_def]

theorem chirpCorrelationRows_length {r : ℕ} (M m : ℕ) (X : ℕ → Fin r → GaussianInt)
    (hsize : 4 * m ≤ r) :
    ∀ xs ∈ chirpCorrelationRows M m X, xs.length = m := by
  intro xs hx
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
  simp only [correlationCoeffs, List.length_reverse, List.length_take, List.length_drop, List.length_ofFn]
  omega

/-- Selecting the correlation interval preserves every coefficient's norm bound. -/
theorem chirpCorrelationRows_norm {r : ℕ} (p M m : ℕ) (X : ℕ → Fin r → GaussianInt)
    (hX : ∀ n < M, ∀ i, ‖value p (X n i)‖ ≤ 1) :
    ∀ z ∈ (chirpCorrelationRows M m X).flatten, ‖value p z‖ ≤ 1 := by
  intro z hz
  obtain ⟨xs, hxs, hz⟩ := List.mem_flatten.mp hz
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hxs
  have hz' : z ∈ List.ofFn (X n) :=
    List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_reverse.mp hz))
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz'
  exact hX n (List.mem_range.mp hn) i

/-- The actual generated operands discharge the output-stage unit-disk precondition. -/
theorem chirpGeneratedCorrelationRows_norm {s t : ℕ} [NeZero s] [NeZero t]
    (hst : s < t) (α q l M m : ℕ) (hα : 0 < α) (hq : 13 ≤ q) (hl : 7 * m ≤ 2 ^ l)
    (u : ZMod s → GaussianInt) (hu : ∀ j, ‖value q (u j)‖ ≤ 1) :
    ∀ z ∈ (chirpCorrelationRows M m (fun n => coeff (q + 1) l
      (chirpOperandX s t q m n (chirpInputNumerators s t α q m) u)
      (chirpOperandY m n (chirpKernelNumerators s t α q m)))).flatten,
      ‖value (q + 1) z‖ ≤ 1 := by
  apply chirpCorrelationRows_norm
  intro n hn i
  have hd := coeff_diskGrid (q + 1) l _ _ (chirpOperands_length s t q m n l _ _ u hl)
    (chirpOperandX_disk hst α q m hα hq u hu n)
    (chirpOperandY_disk hst α q m hα hq u hu n)
  simpa only [value, gridPoly] using hd.norm_le i

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
