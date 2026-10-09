import IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalData
import IntegerMultBounds.Machine.ActivePrefixEarlySequenceRun

/-! Only original swap geometry and original layout/gadget controls are
supplied. The consumer Inputs record is filled by the physical header outputs. -/
namespace IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalInputs
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes CompactActiveTargetGeometry
open ActivePrefixEarlySequenceOriginalData

structure Inputs (s : Shape) (p : Parameters s) (offset rows : ℕ) where
  gs : Fin 7 → List Bool
  bw : List Bool
  hs : Fin 14 → List Bool
  gv : ∀ i, Counter.value (gs i)=CompactGadgetReservationHeadersCarvedSchedule.originalValues s p.n rows i
  gc : ∀ i, GrowingCounterData.Canonical (gs i)
  gb : Counter.value bw=p.b
  cb : GrowingCounterData.Canonical bw
  hv : ∀ i, Counter.value (hs i)=ActivePrefixLayoutHeadersData.originalValues
    (ActivePrefixLayoutHeadersGeometry.inputs s p offset rows) i
  hc : ∀ i, GrowingCounterData.Canonical (hs i)
  hr : 0<rows
  hK : 0<s.chunk
  hd : 0<s.axes
  hg : 0<s.guard
  hrecord : s.bits+1≤s.payload

variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

def geometry := ActivePrefixLayoutHeadersGeometry.inputs s p offset rows

def layout (_d : Inputs s p offset rows) := geometry (s := s) (p := p) (offset := offset) (rows := rows)

def prepared (hfit : offset+p.f*p.q≤p.before) (d : Inputs s p offset rows) :
    ActivePrefixEarlySequenceRun.Inputs s p offset rows hfit where
  gs := d.gs
  bw := d.bw
  ht := fun i => targetWords (geometry (s := s) (p := p) (offset := offset) (rows := rows)) (Fin.castAdd 2 i)
  hc := fun i => compactWords (geometry (s := s) (p := p) (offset := offset) (rows := rows)) (Fin.castAdd 2 i)
  rs := targetWords (geometry (s := s) (p := p) (offset := offset) (rows := rows)) 8
  bt := targetWords (geometry (s := s) (p := p) (offset := offset) (rows := rows)) 9
  bc := compactWords (geometry (s := s) (p := p) (offset := offset) (rows := rows)) 9
  gv := d.gv
  gc := d.gc
  gb := d.gb
  cb := d.cb
  tv := by
    intro i
    exact (ActivePrefixLayoutHeadersEndpoint.words_value .target geometry (Fin.castAdd 2 i)).trans
      (ActivePrefixLayoutHeadersGeometry.target_values s p offset rows hfit i)
  tc := fun i => ActivePrefixLayoutHeadersEndpoint.words_canonical .target geometry (Fin.castAdd 2 i)
  cv := by
    intro i
    exact (ActivePrefixLayoutHeadersEndpoint.words_value .compactBefore geometry (Fin.castAdd 2 i)).trans
      (ActivePrefixLayoutHeadersGeometry.compact_before_values s p offset rows hfit i)
  cc := fun i => ActivePrefixLayoutHeadersEndpoint.words_canonical .compactBefore geometry (Fin.castAdd 2 i)
  rv := RecursiveChildQuotientsConstant.bits_value rows
  rc := ActivePrefixLayoutHeadersEndpoint.words_canonical .target geometry 8
  btv := (ActivePrefixLayoutHeadersEndpoint.words_value .target geometry 9).trans
    (ActivePrefixLayoutHeadersGeometry.target_suffix s p offset rows)
  btc := ActivePrefixLayoutHeadersEndpoint.words_canonical .target geometry 9
  bcv := (ActivePrefixLayoutHeadersEndpoint.words_value .compactBefore geometry 9).trans
    (ActivePrefixLayoutHeadersGeometry.compact_suffix s p offset rows .compactBefore (by decide))
  bcc := ActivePrefixLayoutHeadersEndpoint.words_canonical .compactBefore geometry 9
  hr := d.hr
  hK := d.hK
  hd := d.hd
  hg := d.hg
  hrecord := d.hrecord

end
end IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalInputs
