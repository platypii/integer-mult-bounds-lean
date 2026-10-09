import IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceOriginalData
import IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalInputs
import IntegerMultBounds.Machine.ActivePrefixDirtyControlSequencePlaced

/-! The later sequence accepts only original geometry and stage words.
All consumer header values here are supplied by the physical producer. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceOriginalInputs
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes
open ActivePrefixEarlySequenceOriginalInputs (Inputs)
open ActivePrefixDirtyControlSequenceOriginalData
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

abbrev layout (d : Inputs s p offset rows) := ActivePrefixEarlySequenceOriginalInputs.layout d
abbrev geometry (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b) (d : Inputs s p offset rows) :=
  ActivePrefixDirtyControlSequenceGeometry.geometry s p rows offset hfit hn hb d.hrecord d.hr d.hK d.hd d.hg

def prepared (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b) (d : Inputs s p offset rows) :
    ActivePrefixDirtyControlSequenceData.Inputs s (geometry hfit hn hb d) where
  gs := d.gs
  bw := d.bw
  ht := fun i => targetWords (layout d) (Fin.castAdd 4 i)
  hc := fun i => compactWords (layout d) (Fin.castAdd 4 i)
  hx := fun i => sourceWords (layout d) (Fin.castAdd 4 i)
  rs := targetWords (layout d) 8
  bt := targetWords (layout d) 9
  bc := compactWords (layout d) 9
  gv := d.gv
  gc := d.gc
  gb := d.gb
  cb := d.cb
  tv := fun i => (ActivePrefixDirtyControlHeadersEndpoint.words_value .target (layout d) (Fin.castAdd 4 i)).trans
    (ActivePrefixDirtyControlHeadersGeometry.target_values s p offset rows i)
  tc := fun i => ActivePrefixDirtyControlHeadersEndpoint.words_canonical .target (layout d) (Fin.castAdd 4 i)
  cv := fun i => (ActivePrefixDirtyControlHeadersEndpoint.words_value .compact (layout d) (Fin.castAdd 4 i)).trans
    (ActivePrefixDirtyControlHeadersGeometry.compact_values s p offset rows i)
  cc := fun i => ActivePrefixDirtyControlHeadersEndpoint.words_canonical .compact (layout d) (Fin.castAdd 4 i)
  xv := fun i => (ActivePrefixDirtyControlHeadersEndpoint.words_value .source (layout d) (Fin.castAdd 4 i)).trans
    (ActivePrefixDirtyControlHeadersGeometry.source_values s p offset rows hfit i)
  xc := fun i => ActivePrefixDirtyControlHeadersEndpoint.words_canonical .source (layout d) (Fin.castAdd 4 i)
  rv := RecursiveChildQuotientsConstant.bits_value rows
  rc := ActivePrefixDirtyControlHeadersEndpoint.words_canonical .target (layout d) 8
  btv := (ActivePrefixDirtyControlHeadersEndpoint.words_value .target (layout d) 9).trans
    (ActivePrefixLayoutHeadersGeometry.target_suffix s p offset rows)
  btc := ActivePrefixDirtyControlHeadersEndpoint.words_canonical .target (layout d) 9
  bcv := (ActivePrefixDirtyControlHeadersEndpoint.words_value .compact (layout d) 9).trans
    (ActivePrefixLayoutHeadersGeometry.compact_suffix s p offset rows .compactAfter (by decide))
  bcc := ActivePrefixDirtyControlHeadersEndpoint.words_canonical .compact (layout d) 9

theorem sequence_sources (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b)
    (d : Inputs s p offset rows) (x : ActivePrefixDirtyControlConjugationData.FullArray s rows) :
    SharedBank.payload (ready d.gs d.bw d.hs x (layout d)) sequenceFocus=
      ActivePrefixDirtyControlSequenceData.caller (prepared hfit hn hb d) x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceOriginalInputs
