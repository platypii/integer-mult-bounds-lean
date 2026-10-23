module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOperands
public import IntegerMultBounds.MathlibTM2.Mult.ChirpTables

/-! # Disk bounds for operands formed from the generated chirp tables

The coefficient identities discharge the ring-record representation conditions, and the
computed-table estimates discharge the integer disk conditions used by shared packing.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- Actual generated input weight numerators, as signed integers. -/
def chirpInputNumerators (s t α q m : ℕ) (k0 a : ℕ) : ℤ :=
  chirpTableG s t α q m k0 a

/-- Actual generated kernel weight numerators, as signed integers. -/
def chirpKernelNumerators (s t α q m : ℕ) (k0 : ℕ) (a : ℤ) : ℤ :=
  chirpTableK s t α q m k0 a

/-- Both integer operand records satisfy the disk condition at their half-scaled precision. -/
theorem chirpOperands_disk {s t : ℕ} [NeZero s] [NeZero t]
    (hst : s < t) (α q m : ℕ) (hα : 0 < α) (hq : 13 ≤ q)
    (u : ZMod s → GaussianInt) (hu : ∀ j, ‖value q (u j)‖ ≤ 1) (n i : ℕ) :
    let x := block (chirpOperandX s t q m n (chirpInputNumerators s t α q m) u) i
    let y := block (chirpOperandY m n (chirpKernelNumerators s t α q m)) i
    x.re ^ 2 + x.im ^ 2 ≤ (2 : ℤ) ^ (2 * (q + 1)) ∧
      y.re ^ 2 + y.im ^ 2 ≤ (2 : ℤ) ^ (2 * (q + 1)) := by
  have h := chirpTable_records_norm hst α q m hα hq (fun j => value q (u j)) hu n i
  constructor
  · apply disk_of_norm_value_le
    rw [value_chirpOperandX]
    simpa only [chirpInputNumerators, Int.cast_natCast] using h.1
  · apply disk_of_norm_value_le
    rw [value_chirpOperandY]
    simpa only [chirpKernelNumerators, Int.cast_natCast] using h.2

/-- The disk condition holds for every stored input coefficient, as required by S1. -/
theorem chirpOperandX_disk {s t : ℕ} [NeZero s] [NeZero t]
    (hst : s < t) (α q m : ℕ) (hα : 0 < α) (hq : 13 ≤ q)
    (u : ZMod s → GaussianInt) (hu : ∀ j, ‖value q (u j)‖ ≤ 1) (n : ℕ)
    (z : GaussianInt) (hz : z ∈ chirpOperandX s t q m n (chirpInputNumerators s t α q m) u) :
    z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * (q + 1)) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
  have h := (chirpOperands_disk hst α q m hα hq u hu n i).1
  simpa only [block, List.getElem?_eq_getElem hi, Option.getD_some] using h

/-- The disk condition holds for every stored kernel coefficient, as required by S1. -/
theorem chirpOperandY_disk {s t : ℕ} [NeZero s] [NeZero t]
    (hst : s < t) (α q m : ℕ) (hα : 0 < α) (hq : 13 ≤ q)
    (u : ZMod s → GaussianInt) (hu : ∀ j, ‖value q (u j)‖ ≤ 1) (n : ℕ)
    (z : GaussianInt) (hz : z ∈ chirpOperandY m n (chirpKernelNumerators s t α q m)) :
    z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * (q + 1)) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
  have h := (chirpOperands_disk hst α q m hα hq u hu n i).2
  simpa only [block, List.getElem?_eq_getElem hi, Option.getD_some] using h

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
