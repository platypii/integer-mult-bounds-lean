import IntegerMultBounds.Machine.CompactGlobalRowPadding
import IntegerMultBounds.Machine.CompactGadgetReservationShape

/-! Original global parameters determine the complete reserved layout. Rows
use only the original first q0 axes; all three compact fields, unused bits,
active axes and payload remain in every row and hence in every role. -/
namespace IntegerMultBounds.Machine.CompactGlobalReservation
open CompactGlobalRowPadding
open CompactGadgetReservationCapacity
open CompactGadgetReservationShape

def reservedAxes (c m d G K : ℕ) := rowAxes c m d+frontChunks d G K+backChunks d G K

def shape (c m d D G K payload : ℕ) : Shape where
  axes := d
  guard := G
  chunk := K
  active := D-reservedAxes c m d G K
  payload := payload

theorem original_axes (c m d D G K : ℕ) (hD : reservedAxes c m d G K ≤ D) :
    rowAxes c m d+frontChunks d G K+(D-reservedAxes c m d G K)+backChunks d G K = D :=
  axes_exact D (rowAxes c m d) d G K hD

theorem original_bits (c m d D G K payload : ℕ) (hK : 0 < K)
    (hD : reservedAxes c m d G K ≤ D) :
    rowAxes c m d*K+(shape c m d D G K payload).bits = D*K := by
  rw [Shape.existing_bits _ hK]
  have he := original_axes c m d D G K hD
  simp only [shape]
  nlinarith

/-- The entire original address volume is retained by the row reinterpretation. -/
theorem original_volume (c m d D G K payload : ℕ) (hK : 0 < K)
    (hD : reservedAxes c m d G K ≤ D) :
    originalRows c m d K*(shape c m d D G K payload).recordWidth = 2^(D*K)*payload := by
  simp only [originalRows,Shape.recordWidth,shape]
  rw [← Nat.mul_assoc,← pow_add]
  exact congrArg (fun b => 2^b*payload) (original_bits c m d D G K payload hK hD)

theorem padded_volume (c m d D G K payload : ℕ) (hc : 0 < c) (hK : 0 < K)
    (hD : reservedAxes c m d G K ≤ D) :
    2^(D*K)*payload ≤ initialRows c m d K*(shape c m d D G K payload).recordWidth ∧
    initialRows c m d K*(shape c m d D G K payload).recordWidth ≤ 2*(2^(D*K)*payload) := by
  have hb := initial_bounds c m d K hc hK
  rw [← original_volume c m d D G K payload hK hD]
  constructor
  · exact Nat.mul_le_mul_right _ hb.1
  · calc
      _ ≤ (2*originalRows c m d K)*(shape c m d D G K payload).recordWidth :=
        Nat.mul_le_mul_right _ hb.2.2.1
      _ = _ := by ring

/-- All reserved axes are original axes, bounded by the global axis count. -/
theorem reserved_le_global (c m d D G K : ℕ)
    (hD : reservedAxes c m d G K ≤ D) (hDd : D ≤ d) : reservedAxes c m d G K ≤ d :=
  hD.trans hDd

theorem active_le_global (c m d D G K payload : ℕ) (hDd : D ≤ d) :
    (shape c m d D G K payload).active ≤ (shape c m d D G K payload).axes :=
  (Nat.sub_le _ _).trans hDd

/-- Both front fields and the back field retain sufficient capacity at every
node; carving never uses the row index bits. -/
theorem node_capacity (c m d D G K payload f : ℕ) (hf : f ≤ d) :
    (shape c m d D G K payload).width (f-1) ≤ (shape c m d D G K payload).H :=
  (shape c m d D G K payload).carved_le (f-1) (by simpa only [shape] using (Nat.sub_le f 1).trans hf)

end IntegerMultBounds.Machine.CompactGlobalReservation
