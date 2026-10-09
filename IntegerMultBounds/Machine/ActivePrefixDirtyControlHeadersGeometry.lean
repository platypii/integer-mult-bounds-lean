import IntegerMultBounds.Machine.ActivePrefixDirtyControlHeadersPlaced
import IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceGeometry
import IntegerMultBounds.Machine.ActivePrefixLayoutHeadersGeometry

/-! The physical header producer's six-word groups are the exact target,
compact-back and later-source geometries of the unchanged original array. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlHeadersGeometry
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixLayoutHeadersGeometry
open ActivePrefixDirtyControlHeadersData
open ActivePrefixDirtyControlLayoutFields
open CompactActiveTargetGeometry ActivePrefixLayoutGeometry
variable (s : Shape) (p : Parameters s) (offset rows : ℕ)

theorem target_values (i : Fin 6) :
    values .target (inputs s p offset rows) (Fin.castAdd 4 i)=
      ActivePrefixDirtyControlData.values (ActivePrefixDirtyControlLayoutFields.targetShape s p) i := by
  have hw := p.compactFits
  fin_cases i <;> simp [values,startU,startT,mode,inputs,ActivePrefixLayoutHeadersData.prefixWidth,
    ActivePrefixLayoutHeadersData.targetStart,ActivePrefixDirtyControlData.values,ActivePrefixDirtyControlLayoutFields.targetShape,targetWidth,tStart,uStart]
  all_goals omega

theorem compact_values (i : Fin 6) :
    values .compact (inputs s p offset rows) (Fin.castAdd 4 i)=
      ActivePrefixDirtyControlData.values (compactShape s p) i := by
  have hw := p.compactFits
  fin_cases i <;> simp [values,startU,startT,mode,inputs,ActivePrefixLayoutHeadersData.prefixWidth,
    ActivePrefixLayoutHeadersData.targetStart,ActivePrefixDirtyControlData.values,compactShape,backWidth,targetWidth,uStart]
  all_goals omega

theorem source_values (hfit : offset+p.f*p.q≤p.after) (i : Fin 6) :
    values .source (inputs s p offset rows) (Fin.castAdd 4 i)=
      ActivePrefixDirtyControlData.values (ActivePrefixDirtyControlSourceGeometry.sourceShape s p offset hfit) i := by
  have hw := p.compactFits
  fin_cases i <;> simp [values,startU,startT,mode,inputs,ActivePrefixLayoutHeadersData.prefixWidth,
    ActivePrefixDirtyControlData.values,ActivePrefixDirtyControlSourceGeometry.sourceShape,backWidth,targetWidth,tStart]
  all_goals omega

end IntegerMultBounds.Machine.ActivePrefixDirtyControlHeadersGeometry
