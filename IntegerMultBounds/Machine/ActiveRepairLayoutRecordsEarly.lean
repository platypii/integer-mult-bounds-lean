import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsMove
import IntegerMultBounds.Machine.ActivePrefixEarlySequenceGlobal

/-! Grouping the actual early four-load output into original-width records
supplies exactly the payload-one global repair input, retaining wide physical
reservations and their absorption hypotheses. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsEarly
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes CompactActiveTargetLayout
open ActiveRepairLayoutRecordsShape ActiveRepairLayoutRecordsData
open Compact ActiveRepairLayoutPermutation
variable (s : Shape) (p : Parameters s) (offset : ℕ) (rows : ℕ)
variable (hfit : offset+p.f*p.q≤p.before)
variable (array : ActivePrefixEarlySequenceData.Array s rows)
local notation "E" => indexEquiv (addressShape s) (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize
local notation "P" => earlyActual s p.q p.b p.n p.before p.after rows p.rho offset (p.f*p.q) ActiveRepairRankHeadersData.SourceSide.before (ActivePrefixEarlySequenceGlobal.positive s p)
local notation "Q" => earlyActual (addressShape s) p.q p.b p.n p.before p.after rows p.rho offset (p.f*p.q) ActiveRepairRankHeadersData.SourceSide.before (ActivePrefixEarlySequenceGlobal.positive s p)

theorem result_move :
    ActivePrefixEarlySequenceData.result s p offset hfit rows array=
    ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows
      p.compactFits p.activeSize P array := by
  let f := indexEquiv s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize
  funext i
  have hh := ActivePrefixEarlySequenceGlobal.entry s p offset hfit array ((P).symm (f.symm i))
  change ActivePrefixEarlySequenceData.result s p offset hfit rows array (f (P ((P).symm (f.symm i))))=
    array (f ((P).symm (f.symm i))) at hh
  simpa only [Equiv.apply_symm_apply,ActiveRepairLayoutRecordsMove.move,f] using hh

theorem data_result :
    data s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize
      (ActivePrefixEarlySequenceData.result s p offset hfit rows array)=
    data s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize array ∘ (Q).symm := by
  apply data_after s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize
    array _
  · exact ActiveRepairLayoutRecordsPermutation.early_actual s p.q p.b p.n p.before p.after rows p.rho offset (p.f*p.q) ActiveRepairRankHeadersData.SourceSide.before (ActivePrefixEarlySequenceGlobal.positive s p)
  · exact ActivePrefixEarlySequenceGlobal.entry s p offset hfit array

theorem records_result :
    records s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize
      (ActivePrefixEarlySequenceData.result s p offset hfit rows array)=
    repairRecords E Q (data s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize array) := by
  unfold records repairRecords
  rw [data_result]

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsEarly
