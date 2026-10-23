module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandBounds
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBatchProductMath

/-! # Shared correlation error for the generated integer operands

This specialization discharges every representation and disk hypothesis of the batch
product bridge. Executing operand production and composing it with the batch caller
remain separate machine obligations.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast

/-- The generated operands give the shared tape correlation bound without assumed
operand representations or integer disk bounds. -/
theorem chirpOperandBatch_err {s t A : ℕ} [NeZero s] [NeZero t]
    (hA : 4 ≤ A) (hst : s < t) (α q l w M m : ℕ)
    (hα : 0 < α) (hq : 13 ≤ q) (hw : q + 1 + 2 ≤ w)
    (hm : 1 ≤ m) (hl : 7 * m ≤ 2 ^ l)
    (u : ZMod s → GaussianInt) (hu : ∀ j, ‖value q (u j)‖ ≤ 1)
    (tail : List (Fin (A + 4))) (n : ℕ) (hn : n < M) (b : Fin m) :
    let X := fun n => chirpOperandX s t q m n (chirpInputNumerators s t α q m) u
    let Y := fun n => chirpOperandY m n (chirpKernelNumerators s t α q m)
    ‖(4 * (2 ^ l : ℕ) : ℂ) * value (q + 1) (decodeWord
      (((cstream A w (correlationStream M m (fun n => coeff (q + 1) l (X n) (Y n))) ++
        tail).drop ((n * m + b.val) * w)).take w)) -
      chirpCorr (t := t) m (rhoC q)
        (fun k0 a => (chirpTableG s t α q m k0 a : ℝ) / 2 ^ q)
        (fun k0 a => (chirpTableK s t α q m k0 a : ℝ) / 2 ^ q)
        (fun j => value q (u j)) (n * m) b.val‖ ≤ 8 * (2 : ℝ) ^ l / (2 : ℝ) ^ (q + 1) := by
  apply correlationBatchTape_chirpCorr_err hA (q + 1) l w M m hw hm hl
  · intro j hj
    exact chirpOperands_length s t q m j l _ _ u hl
  · intro j hj z hz
    exact chirpOperandX_disk hst α q m hα hq u hu j z hz
  · intro j hj z hz
    exact chirpOperandY_disk hst α q m hα hq u hu j z hz
  · intro j hj i
    simpa only [chirpInputNumerators, Int.cast_natCast] using
      value_chirpOperandX q m j i (chirpInputNumerators s t α q m) u
  · intro j hj i
    simpa only [chirpKernelNumerators, Int.cast_natCast] using
      value_chirpOperandY q m j i (chirpKernelNumerators s t α q m)
  · exact hn

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
