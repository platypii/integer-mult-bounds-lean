module

public import IntegerMultBounds.MathlibTM2.Routing.LiveHeaderRepairProgram

/-! Separate scalar/descriptor setup from the linear-volume part of live repair
metadata. Unary construction has an additive value cost, with no width factor. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

/-- Keep scalar widths fixed while separating the two physical stream sizes. -/
theorem liveRepairUniformOverhead_split (n rb R B width wb wm wp wk : ℕ)
    (w : LiveDescriptorWidths) :
    liveRepairUniformOverhead n rb R B width wb wm wp wk w =
      liveRepairUniformOverhead n rb 0 0 width wb wm wp wk w + 272 * (B + R * 2 ^ n) := by
  unfold liveRepairUniformOverhead
  ring

/-- The remaining setup price depends on scalar and descriptor sizes only. -/
theorem liveRepairUniformOverhead_amortized (n rb R B width wb wm wp wk : ℕ)
    (w : LiveDescriptorWidths) (hR : 1 ≤ R) (hB : 1 ≤ B) :
    liveRepairUniformOverhead n rb R B width wb wm wp wk w ≤
      liveRepairUniformOverhead n rb 0 0 width wb wm wp wk w + 544 * (R * 2 ^ n * B) := by
  have hM : 1 ≤ R * 2 ^ n := by
    have hp := Nat.two_pow_pos n
    nlinarith
  have hb : B ≤ R * 2 ^ n * B := by simpa using Nat.mul_le_mul_right B hM
  have hm : R * 2 ^ n ≤ R * 2 ^ n * B := by simpa using Nat.mul_le_mul_left (R * 2 ^ n) hB
  rw [liveRepairUniformOverhead_split]
  omega

end IntegerMultBounds.MathlibTM2.Routing
