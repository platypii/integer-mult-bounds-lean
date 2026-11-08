module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseMasterInput

/-! Enlarge scalar words once to accommodate the retained recovery packet width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

namespace InverseMasterInput
variable {s : ℕ} [NeZero s]

/-- Widening the scalar format preserves all ordinary input data and room bounds. -/
def widen (d : InverseMasterInput s) (B : ℕ) (hB : d.B ≤ B) : InverseMasterInput s := by
  have hpow : 2^d.B ≤ 2^B := Nat.pow_le_pow_right (by decide) hB
  exact {d with B := B
                band_room := d.band_room.trans_le hpow
                geometry_room := d.geometry_room.trans_le hpow
                precision_room := d.precision_room.trans_le hpow
                values_fit := fun i => (d.values_fit i).trans_le hpow}

/-- The root scalar format covers both its original setup and the multiplier's
packet-width ruler. Its width depends only on ordinary dimensions. -/
def withPacketRoom (d : InverseMasterInput s) (w : ℕ) : InverseMasterInput s :=
  d.widen (max d.B (Nat.size (4*w+2))) (le_max_left _ _)

theorem withPacketRoom_room (d : InverseMasterInput s) (w : ℕ) :
    4*w+2 < 2^(d.withPacketRoom w).B := by
  exact (Nat.lt_size_self (4*w+2)).trans_le
    (Nat.pow_le_pow_right (by decide) (le_max_right d.B (Nat.size (4*w+2))))

end InverseMasterInput
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
