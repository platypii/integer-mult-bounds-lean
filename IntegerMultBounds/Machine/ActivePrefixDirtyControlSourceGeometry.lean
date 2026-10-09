import IntegerMultBounds.Machine.ActivePrefixDirtyControlLayoutFields
import IntegerMultBounds.Machine.ActivePrefixDirtyControlLoadData

/-! The later source-loading conjugation uses the selected source bits in the
actual active-after field and the retained compact T field as controls. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlSourceGeometry
open CompactGadgetReservationShape CompactActiveTargetGeometry
open ActivePrefixLayoutShapes ActivePrefixLayoutGeometry

variable (s : Shape) (p : Parameters s) (offset : ℕ) (hfit : offset+p.f*p.q≤p.after)

def sourceShape : ActivePrefixDirtyControlData.Shape .parity where
  W := backWidth s (p.n*p.q) p.before p.after
  startT := offset+p.rho
  startU := p.n*p.q+p.after+tStart s (p.n*p.b) p.before
  q := p.q
  b := p.b
  n := p.n
  tempFits := by
    change offset+p.rho+p.n*p.q≤backWidth s (p.n*p.q) p.before p.after
    have hf := p.hnf
    have hr := p.hr
    unfold backWidth
    nlinarith
  controlFits := by
    have ht := target_t_fits s (p.n*p.b) p.before p.compactFits
    change p.n*p.q+p.after+tStart s (p.n*p.b) p.before+p.n*p.b≤_
    unfold backWidth
    omega
  hb := p.hb
  hbq := p.hbq

include hfit in
theorem source_fits_after : offset+p.rho+p.n*p.q≤p.after := by
  have hf := p.hnf
  have hr := p.hr
  nlinarith

theorem source_volume (rows : ℕ) :
    rows*s.recordWidth=ActivePrefixDirtyControlLoadData.volume (m := .pure)
      (sourceShape s p offset hfit) rows (compactSuffix s (p.n*p.b)) := by
  change rows*(2^s.bits*s.payload)=
    (rows*2^(backWidth s (p.n*p.q) p.before p.after))*(2^(p.n*p.b)*compactSuffix s (p.n*p.b))
  unfold compactSuffix
  rw [←Nat.mul_assoc (2^(p.n*p.b)),←pow_add]
  rw [Nat.mul_assoc rows,←Nat.mul_assoc (2^(backWidth s (p.n*p.q) p.before p.after)),←pow_add]
  have he : backWidth s (p.n*p.q) p.before p.after+(p.n*p.b+(s.H-p.n*p.b+s.B))=s.bits := by
    have ha := p.activeSize
    have hw := p.compactFits
    unfold backWidth targetWidth Shape.bits
    omega
  rw [he]

theorem source_absorbed (hn : 0<p.n) (hb : 2≤p.b) (hrecord : s.bits+1≤s.payload) :
    (sourceShape s p offset hfit).W+(sourceShape s p offset hfit).n*(sourceShape s p offset hfit).q+
      (sourceShape s p offset hfit).q+(sourceShape s p offset hfit).b+1≤
        2^((sourceShape s p offset hfit).n*(sourceShape s p offset hfit).b)*compactSuffix s (p.n*p.b) :=
  ActivePrefixDirtyControlLayoutAbsorption.compact s p hn hb hrecord

end IntegerMultBounds.Machine.ActivePrefixDirtyControlSourceGeometry
