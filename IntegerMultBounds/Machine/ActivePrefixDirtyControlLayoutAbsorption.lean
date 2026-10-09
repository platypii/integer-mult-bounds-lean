import IntegerMultBounds.Machine.ActivePrefixLayoutAbsorption

/-! The actual layout pays the wider dirty-U producer bound without requiring
the wide target in a compact slot or increasing the record payload allowance. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlLayoutAbsorption
open CompactGadgetReservationShape CompactActiveTargetGeometry
open ActivePrefixLayoutShapes ActivePrefixLayoutGeometry

variable (s : Shape) (p : Parameters s)

theorem active_width_le : p.n*p.q≤s.bits := by
  have ha := p.activeSize
  unfold Shape.bits
  omega

theorem producer_width (W : ℕ) (hW : W≤s.bits) (hn : 0<p.n) :
    W+p.n*p.q+p.q+p.b+1≤4*(s.bits+1) := by
  have hactive := active_width_le s p
  have hq : p.q≤p.n*p.q := Nat.le_mul_of_pos_left _ hn
  have hb : p.b≤p.q := by have := p.hbq; omega
  omega

theorem target_capacity (hn : 0<p.n) : 4≤2^(p.n*p.q) := by
  have hq : 2≤p.q := by have := p.hb; have := p.hbq; omega
  have hwidth : 2≤p.n*p.q := hq.trans (Nat.le_mul_of_pos_left _ hn)
  exact (show 4=2^2 from rfl).le.trans (Nat.pow_le_pow_right (by decide) hwidth)

theorem compact_capacity (hn : 0<p.n) (hb : 2≤p.b) : 4≤2^(s.H+s.B) := by
  have hH : 2≤s.H := hb.trans ((Nat.le_mul_of_pos_left _ hn).trans p.compactFits)
  exact (show 4=2^2 from rfl).le.trans (Nat.pow_le_pow_right (by decide) (by omega))

/-- Selected/correction producer work fits the unchanged active-target fiber;
the existing address-sized payload allowance suffices. -/
theorem target (hn : 0<p.n) (hrecord : s.bits+1≤s.payload) :
    targetWidth s p.before+p.n*p.q+p.q+p.b+1≤
      2^(p.n*p.q)*targetSuffix s p.after := by
  have hw := producer_width s p _ (ActivePrefixLayoutAbsorption.target_width_le s p) hn
  have hp := Nat.mul_le_mul_left 4 hrecord
  have hc := Nat.mul_le_mul_right s.payload (target_capacity s p hn)
  have htail : s.payload≤targetSuffix s p.after := by
    unfold targetSuffix
    exact Nat.le_mul_of_pos_left _ (by positivity)
  exact hw.trans (hp.trans (hc.trans (Nat.mul_le_mul_left _ htail)))

/-- Pure/negative dirty-U loads see the complete back prefix. Compact width
at least two supplies the constant factor needed by their explicit wide work. -/
theorem compact (hn : 0<p.n) (hb : 2≤p.b) (hrecord : s.bits+1≤s.payload) :
    backWidth s (p.n*p.q) p.before p.after+p.n*p.q+p.q+p.b+1≤
      2^(p.n*p.b)*compactSuffix s (p.n*p.b) := by
  have hw := producer_width s p _ (ActivePrefixLayoutAbsorption.back_width_le s p) hn
  have hp := Nat.mul_le_mul_left 4 hrecord
  have hc := Nat.mul_le_mul_right s.payload (compact_capacity s p hn hb)
  have he : 2^(p.n*p.b)*compactSuffix s (p.n*p.b)=2^(s.H+s.B)*s.payload := by
    unfold compactSuffix
    rw [←Nat.mul_assoc,←pow_add]
    congr 2
    have := p.compactFits
    omega
  rw [he]
  exact hw.trans (hp.trans hc)

end IntegerMultBounds.Machine.ActivePrefixDirtyControlLayoutAbsorption
