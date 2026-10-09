import IntegerMultBounds.Machine.ArbitraryWidthHighPrepare
import IntegerMultBounds.Swap.Recurrence

/-! The concrete runtime high-row selector agrees with the manuscript's
large-width branch. The complementary widths form a bounded fallback set. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighGuard
open ArbitraryWidthHighPrepare

theorem depth_eq_ceiling (e : ℕ) :
    depth e = ⌈Real.log e / Real.log base⌉₊ := by
  rw [depth,← Real.natCeil_logb_natCast,Real.logb]

theorem highDepth_positive (q e : ℕ) (hq : 2 ≤ q) (he : 1 < e) :
    0 < highDepth q e := by
  have hk : 0 < depth e := Nat.clog_pos (by decide : 1 < base) he
  have hW : 1 < worlds := lt_of_lt_of_le (by decide : 1 < base) worlds_ge_base
  have hD : 1 < divisor e := by
    unfold divisor
    have h := Nat.pow_le_pow_right (by omega : 1 ≤ worlds) (show 1 ≤ depth e by omega)
    simpa only [pow_one] using lt_of_lt_of_le hW h
  exact Nat.clog_pos (ArbitraryWidthHighRows.square_base q hq) hD

/-- Both branch conditions of the actual integer selector hold for every
sufficiently large width; the proof uses the exact selected runtime values. -/
theorem eventually_highDepth (q : ℕ) (hq : 2 ≤ q) :
    ∀ᶠ e : ℕ in Filter.atTop, 1 ≤ highDepth q e ∧ highDepth q e < e := by
  have hW : 1 ≤ worlds := le_trans (by decide : 1 ≤ base) worlds_ge_base
  have h := Swap.Recurrence.row_range_small (m := base) (W := worlds) (q := q)
    (by decide) hW hq
  filter_upwards [h,Filter.eventually_ge_atTop 2] with e he he2
  constructor
  · exact highDepth_positive q e hq (by omega)
  · rw [selector_eq_manuscript q e hq,← worlds_eq_W,depth_eq_ceiling]
    exact he

/-- A fixed finite cutoff suffices for the elementary-width fallback.
This is existence of a mathematical cutoff, not its machine implementation. -/
theorem bounded_fallback (q : ℕ) (hq : 2 ≤ q) :
    ∃ cutoff : ℕ, ∀ e : ℕ, cutoff ≤ e → 1 ≤ highDepth q e ∧ highDepth q e < e := by
  exact Filter.eventually_atTop.mp (eventually_highDepth q hq)

end IntegerMultBounds.Machine.ArbitraryWidthHighGuard
