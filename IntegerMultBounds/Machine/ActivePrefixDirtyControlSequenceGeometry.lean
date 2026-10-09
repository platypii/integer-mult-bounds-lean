import IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceData
import IntegerMultBounds.Machine.ActivePrefixDirtyControlSourceGeometry

/-! The prepared later sequence's complete geometry is obtained from the
original unchanged array and compact parameters, including all absorption. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceGeometry
open CompactGadgetReservationShape CompactActiveTargetGeometry
open ActivePrefixLayoutShapes ActivePrefixLayoutGeometry
open ActivePrefixDirtyControlLayoutFields

variable (s : Shape) (p : Parameters s)

theorem target_volume (rows : ℕ) :
    rows*s.recordWidth=ActivePrefixDirtyControlLoadData.volume (m := .selected)
      (targetShape s p) rows (targetSuffix s p.after) := by
  have hh := (CompactActiveTargetGeometry.target_volume s (p.n*p.b) (p.n*p.q) p.before p.after rows
    p.compactFits p.activeSize).symm
  rw [target_count s (p.n*p.b) p.before rows p.compactFits] at hh
  exact hh

theorem compact_volume (rows : ℕ) :
    rows*s.recordWidth=ActivePrefixDirtyControlLoadData.volume (m := .pure)
      (compactShape s p) rows (compactSuffix s (p.n*p.b)) := by
  have hh := (CompactActiveTargetGeometry.back_volume s (p.n*p.b) (p.n*p.q) p.before p.after rows
    p.compactFits p.activeSize).symm
  rw [back_count s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits] at hh
  exact hh

def geometry (rows offset : ℕ) (hfit : offset+p.f*p.q≤p.after)
    (hn : 0<p.n) (hb : 2≤p.b) (hrecord : s.bits+1≤s.payload)
    (hrows : 0<rows) (hK : 0<s.chunk) (hd : 0<s.axes) (hg : 0<s.guard) :
    ActivePrefixDirtyControlSequenceData.Geometry s where
  n := p.n
  b := p.b
  rows := rows
  target := targetShape s p
  compact := compactShape s p
  source := ActivePrefixDirtyControlSourceGeometry.sourceShape s p offset hfit
  targetSuffix := targetSuffix s p.after
  compactSuffix := compactSuffix s (p.n*p.b)
  compactFits := p.compactFits
  targetVolume := target_volume s p rows
  compactVolume := compact_volume s p rows
  sourceVolume := ActivePrefixDirtyControlSourceGeometry.source_volume s p offset hfit rows
  targetAbsorbed := target_absorbed s p hn hrecord
  compactAbsorbed := compact_absorbed s p hn hb hrecord
  sourceAbsorbed := ActivePrefixDirtyControlSourceGeometry.source_absorbed s p offset hfit hn hb hrecord
  positiveRows := hrows
  positiveWidth := by omega
  positiveTargetSuffix := by
    unfold targetSuffix
    have hp : 0<s.payload := by omega
    positivity
  positiveCompactSuffix := by
    unfold compactSuffix
    have hp : 0<s.payload := by omega
    positivity
  positiveChunk := hK
  positiveAxes := hd
  positiveGuard := hg
  positivePayload := by omega

end IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceGeometry
