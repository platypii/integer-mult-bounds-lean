import IntegerMultBounds.Machine.ActiveTargetHighestPairSemantics
import IntegerMultBounds.Machine.ActivePrefixLayoutShapes

/-! Exact highest-selected-bit split of the unchanged active layout.
The omitted target bit is the least significant bit of activeBefore. No
address bit, compact reservation, spectator, or payload is added or dropped. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestPairLayoutGeometry
open CompactGadgetReservationShape
open ActivePrefixLayoutShapes
open ActiveTargetHighestPairData

variable (s : Shape) (p : Parameters s)

def sourceHigh (offset : ℕ) := offset+p.rho+p.n*p.q

theorem source_high_lt (offset limit : ℕ) (hfit : offset+p.f*p.q≤limit) :
    sourceHigh s p offset<limit := by
  have := p.hnf
  have := p.hr
  unfold sourceHigh
  nlinarith

theorem source_high_pos (offset : ℕ) (hn : 0<p.n) : 0<sourceHigh s p offset := by
  have := p.hb
  have := p.hbq
  unfold sourceHigh
  nlinarith

/-- Later source: target highest bit is left of the source highest bit. -/
def late (offset rows : ℕ) (_hfit : offset+p.f*p.q≤p.after)
    (hbefore : 1≤p.before) (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload) : Geometry where
  L := 2*s.H+s.F+p.before-1
  G := p.after-offset-p.rho-1
  K := sourceHigh s p offset+s.H+s.B
  rows := rows
  payload := s.payload
  positiveLeft := by omega
  positiveRows := hr
  positivePayload := hp

/-- Earlier source: source highest bit is left of target highest bit. -/
def early (offset rows : ℕ) (hfit : offset+p.f*p.q≤p.before)
    (_hsource : 0<sourceHigh s p offset) (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload) : Geometry where
  L := 2*s.H+s.F+p.before-(sourceHigh s p offset+1)
  G := sourceHigh s p offset-1
  K := p.n*p.q+p.after+s.H+s.B
  rows := rows
  payload := s.payload
  positiveLeft := by have := source_high_lt s p offset p.before hfit; omega
  positiveRows := hr
  positivePayload := hp

theorem late_bits (offset rows : ℕ) (hfit : offset+p.f*p.q≤p.after)
    (hbefore : 1≤p.before) (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload) :
    ActiveTargetHighestPairBudget.bits (late s p offset rows hfit hbefore hH hr hp)=s.bits := by
  have := source_high_lt s p offset p.after hfit
  have := p.activeSize
  simp only [ActiveTargetHighestPairBudget.bits,W,late,sourceHigh,Shape.bits] at *
  omega

theorem early_bits (offset rows : ℕ) (hfit : offset+p.f*p.q≤p.before)
    (hsource : 0<sourceHigh s p offset) (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload) :
    ActiveTargetHighestPairBudget.bits (early s p offset rows hfit hsource hH hr hp)=s.bits := by
  have := source_high_lt s p offset p.before hfit
  have := p.activeSize
  simp only [ActiveTargetHighestPairBudget.bits,W,early,Shape.bits]
  omega

theorem late_volume (offset rows : ℕ) (hfit : offset+p.f*p.q≤p.after)
    (hbefore : 1≤p.before) (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload) :
    volume (late s p offset rows hfit hbefore hH hr hp)=rows*s.recordWidth := by
  rw [ActiveTargetHighestPairBudget.original_volume,late_bits]
  rfl

theorem early_volume (offset rows : ℕ) (hfit : offset+p.f*p.q≤p.before)
    (hsource : 0<sourceHigh s p offset) (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload) :
    volume (early s p offset rows hfit hsource hH hr hp)=rows*s.recordWidth := by
  rw [ActiveTargetHighestPairBudget.original_volume,early_bits]
  rfl

/-- The right bit is the original source bit inside activeAfter. -/
theorem late_source_position (offset rows : ℕ) (hfit : offset+p.f*p.q≤p.after)
    (hbefore : 1≤p.before) (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload) :
    (late s p offset rows hfit hbefore hH hr hp).K=sourceHigh s p offset+s.H+s.B := rfl

/-- The left bit is the original lowest activeBefore bit, immediately above
all n*q low target bits and activeAfter. -/
theorem late_target_position (offset rows : ℕ) (hfit : offset+p.f*p.q≤p.after)
    (hbefore : 1≤p.before) (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload) :
    (late s p offset rows hfit hbefore hH hr hp).G+1+
      (late s p offset rows hfit hbefore hH hr hp).K=p.n*p.q+p.after+s.H+s.B := by
  have := source_high_lt s p offset p.after hfit
  simp only [late,sourceHigh] at *
  omega

theorem early_target_position (offset rows : ℕ) (hfit : offset+p.f*p.q≤p.before)
    (hsource : 0<sourceHigh s p offset) (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload) :
    (early s p offset rows hfit hsource hH hr hp).K=p.n*p.q+p.after+s.H+s.B := rfl

theorem early_source_position (offset rows : ℕ) (hfit : offset+p.f*p.q≤p.before)
    (hsource : 0<sourceHigh s p offset) (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload) :
    (early s p offset rows hfit hsource hH hr hp).G+1+
      (early s p offset rows hfit hsource hH hr hp).K=
      sourceHigh s p offset+p.n*p.q+p.after+s.H+s.B := by
  simp only [early]
  omega

end IntegerMultBounds.Machine.ActiveTargetHighestPairLayoutGeometry
