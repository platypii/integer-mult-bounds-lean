import IntegerMultBounds.Machine.ActivePrefixLayoutShapes

/-! Prefix construction is paid by the original record payload whenever that
payload exceeds the complete address width. All spectator/back factors only
increase the available volume; no wide active target fits a compact slot. -/
namespace IntegerMultBounds.Machine.ActivePrefixLayoutAbsorption
open CompactGadgetReservationShape CompactActiveTargetGeometry
open ActivePrefixLayoutShapes ActivePrefixLayoutGeometry

variable (s : Shape) (p : Parameters s)

theorem target_width_le : targetWidth s p.before ≤ s.bits := by
  have ha := p.activeSize
  unfold targetWidth Shape.bits
  omega

theorem back_width_le : backWidth s (p.n*p.q) p.before p.after ≤ s.bits := by
  rw [back_width]
  unfold Shape.bits
  omega

/-- A sufficient original-record condition for every compact load, for either
source order. This is independent of row count and selected target width. -/
theorem whole_back (hrecord : s.bits+1 ≤ s.payload) :
    backWidth s (p.n*p.q) p.before p.after+1 ≤ 2^(s.H+s.B)*s.payload := by
  have hw := back_width_le s p
  exact (by omega : backWidth s (p.n*p.q) p.before p.after+1 ≤ s.payload).trans
    (Nat.le_mul_of_pos_left _ (by positivity))

theorem target (offset : ℕ) (hfit : offset+p.f*p.q ≤ p.before)
    (hrecord : s.bits+1 ≤ s.payload) :
    (targetShape s p offset hfit).W+1 ≤ 2^(p.n*p.q)*targetSuffix s p.after := by
  have hw := target_width_le s p
  have hfirst : (targetShape s p offset hfit).W+1 ≤ s.payload := by
    change targetWidth s p.before+1 ≤ s.payload
    omega
  exact hfirst.trans (by
    unfold targetSuffix
    have hpos : 0 < 2^(p.n*p.q)*(2^p.after*2^(s.H+s.B)) := by positivity
    simpa only [Nat.mul_assoc] using Nat.le_mul_of_pos_left s.payload hpos)

theorem compact_before (offset : ℕ) (hfit : offset+p.f*p.q ≤ p.before)
    (hrecord : s.bits+1 ≤ s.payload) :
    (backBeforeShape s p offset hfit).W+1 ≤ 2^(p.n*p.b)*compactSuffix s (p.n*p.b) := by
  have hw := back_width_le s p
  have hfirst : (backBeforeShape s p offset hfit).W+1 ≤ s.payload := by
    change backWidth s (p.n*p.q) p.before p.after+1 ≤ s.payload
    omega
  exact hfirst.trans (by
    unfold compactSuffix
    have hpos : 0 < 2^(p.n*p.b)*2^(s.H-p.n*p.b+s.B) := by positivity
    simpa only [Nat.mul_assoc] using Nat.le_mul_of_pos_left s.payload hpos)

theorem compact_after (offset : ℕ) (hfit : offset+p.f*p.q ≤ p.after)
    (hrecord : s.bits+1 ≤ s.payload) :
    (backAfterShape s p offset hfit).W+1 ≤ 2^(p.n*p.b)*compactSuffix s (p.n*p.b) :=
by
  have hw := back_width_le s p
  have hfirst : (backAfterShape s p offset hfit).W+1 ≤ s.payload := by
    change backWidth s (p.n*p.q) p.before p.after+1 ≤ s.payload
    omega
  exact hfirst.trans (by
    unfold compactSuffix
    have hpos : 0 < 2^(p.n*p.b)*2^(s.H-p.n*p.b+s.B) := by positivity
    simpa only [Nat.mul_assoc] using Nat.le_mul_of_pos_left s.payload hpos)
end IntegerMultBounds.Machine.ActivePrefixLayoutAbsorption
