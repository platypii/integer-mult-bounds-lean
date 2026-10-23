module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpWeightedStream
public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableBlockHost

/-! # Generated table tapes agree with operand-production streams

The executable table scheduler emits exactly the weight stream consumed by the real
multiplier and the kernel stream consumed by S1. These identities preserve coefficient
and bit order; no re-encoding or table oracle is involved.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.MathlibTM2.Fast

/-- Encoding commutes with structural concatenation of coefficient rows. -/
theorem cstream_flatMap_rows {A w : ℕ} {α : Type} (ls : List α)
    (row : α → List GaussianInt) :
    cstream A w (ls.flatMap row) = ls.flatMap (fun a => cstream A w (row a)) := by
  simp only [cstream, List.flatMap_assoc]

/-- The generated input table is the aligned real multiplier table. -/
theorem chirpWeightRow_stream {A : ℕ} (s t α q w m n : ℕ) :
    cstream A w (chirpWeightRow s t α q m n) =
      chirpEntryStream A w (3 * m + 1)
        (fun a => chirpNegativeNumerator false s t α q m (n * m) a) := by
  simp only [chirpWeightRow, chirpEntryStream, chirpNegativeNumerator_input,
    chirpInputNumerators]

/-- All generated input rows appear in the block order of the gathered windows. -/
theorem chirpWeightStream_eq {A : ℕ} (s t α q w m M : ℕ) :
    cstream A w ((List.range M).flatMap fun n => chirpWeightRow s t α q m n) =
      chirpBlockStream M (fun n => chirpEntryStream A w (3 * m + 1)
        (fun a => chirpNegativeNumerator false s t α q m (n * m) a)) := by
  rw [cstream_flatMap_rows]
  simp only [chirpWeightRow_stream, chirpBlockStream]

/-- The generated shifted kernel row is already in the convolution operand order. -/
theorem chirpOperandY_stream {A : ℕ} (s t α q w m n : ℕ) (hm : 1 ≤ m) :
    cstream A w (chirpOperandY m n (chirpKernelNumerators s t α q m)) =
      chirpEntryStream A w (4 * m)
        (fun a => chirpNegativeNumerator true s t α q (2 * m - 1) (n * m) a) := by
  simp only [chirpOperandY, chirpEntryStream, chirpNegativeNumerator_kernel s t α q m _ _ hm,
    chirpKernelNumerators]

/-- The complete generated kernel table is exactly the flattened S1 operand tape. -/
theorem chirpOperandYStream_eq {A : ℕ} (s t α q w m M : ℕ) (hm : 1 ≤ m) :
    cstream A w ((List.range M).flatMap fun n =>
      chirpOperandY m n (chirpKernelNumerators s t α q m)) =
      chirpBlockStream M (fun n => chirpEntryStream A w (4 * m)
        (fun a => chirpNegativeNumerator true s t α q (2 * m - 1) (n * m) a)) := by
  rw [cstream_flatMap_rows]
  simp only [chirpOperandY_stream s t α q w m _ hm, chirpBlockStream]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
