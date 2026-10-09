import IntegerMultBounds.Machine.CompactRowReservationRun

/-! Paid complete reservation layout bounds, including R<c. -/
namespace IntegerMultBounds.Machine.CompactRowReservationBudget
noncomputable section
variable {a c : ℕ}
open IntegerMultBounds.Compact.Layout (paddedRows)
open CompactRowReservationPlacement (bank)
open CompactRowReservationData (original outputPayload)
open CompactRowReservationRun (budget emptyPayload)

def constant (c : ℕ) :=
  (2+5*RecursiveRowsMove.TapeCount c)*(RecursiveRowsQuotient.constant c+1099)+
    11*RecursiveRowsMove.TapeCount c+5204

theorem linear (c r l : ℕ) (hc : 0 < c) (hr : 0 < r) (hl : 0 < l) :
    budget c r l ≤ constant c*(paddedRows r c*l) := by
  have hP : 0 < paddedRows r c := lt_of_lt_of_le hr (CompactRowPaddingRound.padded_bounds r c hc).1
  have hcP : c ≤ paddedRows r c := by
    rw [← CompactRowPaddingRound.rounded_eq r c hr hc]
    exact RoundedRowDescriptor.divisor_le r c
  have hV := Nat.mul_pos hP hl
  have hPV := Nat.le_mul_of_pos_right (paddedRows r c) hl
  have hlV := Nat.le_mul_of_pos_left l hP
  have hcwidth := GrowingCounterData.canonical_width (RecursiveChildQuotientsConstant.bits c)
    (RecursiveChildQuotientsConstant.bits_canonical c)
  have hpwidth := GrowingCounterData.canonical_width (CompactRowPaddingRound.bits r c)
    (CompactRowPaddingRound.bits_canonical r c)
  rw [RecursiveChildQuotientsConstant.bits_value] at hcwidth
  rw [CompactRowPaddingRound.bits_value r c hr hc] at hpwidth
  have hcLog := Nat.log2_le_self c
  have hpLog := Nat.log2_le_self (paddedRows r c)
  have hb := RecursiveRowsClean.bound_linear c (paddedRows r c*l) hV
  unfold budget constant
  nlinarith

/-- Static role count gives a uniform original-volume bound without assuming
there are already at least as many rows as physical roles. -/
theorem original_linear (c r l : ℕ) (hc : 0 < c) (hr : 0 < r) (hl : 0 < l) :
    budget c r l ≤ (constant c*(c+1))*(r*l) := by
  calc
    _ ≤ constant c*(paddedRows r c*l) := linear c r l hc hr hl
    _ ≤ constant c*((c+1)*(r*l)) := Nat.mul_le_mul_left _
      (CompactRowPaddingRun.volume_le_original r c l hr hc)
    _ = _ := by ring

/-- In the usual reservation range, the whole paid machine has at most twice
the padded-volume coefficient against the original literal word volume. -/
theorem range_linear (c r l : ℕ) (hc : 0 < c) (hr : 0 < r) (hl : 0 < l) (hcr : c ≤ r) :
    budget c r l ≤ (2*constant c)*(r*l) := by
  calc
    _ ≤ constant c*(paddedRows r c*l) := linear c r l hc hr hl
    _ ≤ constant c*(2*(r*l)) := Nat.mul_le_mul_left _
      (CompactRowPaddingRun.volume_le_twice r c l hc hcr)
    _ = _ := by ring

/-- Exact whole-bank execution, including every preparation and erasure,
within a constant times the original complete-record binary word volume. -/
theorem runs (ha : 2 ≤ a) (c : ℕ) (rs ls : List Bool) (r l : ℕ)
    (x : Fin (1*r*l) → Bool) (hr : Counter.value rs = r) (hl : Counter.value ls = l)
    (cr : GrowingCounterData.Canonical rs) (cl : GrowingCounterData.Canonical ls)
    (hR : 0 < r) (hL : 0 < l) (hc : 0 < c) :
    HoareTime (CompactRowReservationRun.program ha c)
      (fun w => w = bank (original x) (emptyPayload (c := c)) rs ls none none)
      (fun w => w = bank (fun _ => blank) (outputPayload hc x) rs ls none none)
      ((constant c*(c+1))*(r*l)) :=
  (CompactRowReservationRun.runs ha c rs ls r l x hr hl cr cl hR hL hc).consequence
    (fun _ h => h) (fun _ h => h) (original_linear c r l hc hR hL)

end
end IntegerMultBounds.Machine.CompactRowReservationBudget
