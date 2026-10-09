import IntegerMultBounds.Machine.ButterflyInverseAxisRun

/-! The inverse axis uses the same physically installed runtime headers,
private-bank cleanliness, and exact volume as the forward implementation. -/
namespace IntegerMultBounds.Machine.ButterflyInverseAxisPrepared
noncomputable section
open ButterflyAxisHeadersData ButterflyAxisHeadersGeometry ButterflyAxisHeadersBudget
open ButterflyAxisHeadersInstall (prepared)
open ButterflyStreamData (Coefficient)
open ButterflyInverseAxisRouting (transformed)
open ButterflyAxisPrepared (bank commonPorts common_injective payload frame volume_eq)

abbrev count := ButterflyAxisPrepared.count

def program := Placement.placed ButterflyInverseAxisRun.program
  (CleanSubbank.placement ButterflyAxisPorts.ports commonPorts common_injective)

theorem runs (D t R p : ℕ) (ht : t<D) (hR : 0<R)
    (xs : Fin (RecursiveInterchangeRows.groups 2 (descriptor D t R p)) → Fin 2 → Fin (lower t R) → Coefficient)
    (hw : ∀ h j k,(xs h j k).1.length=ButterflyGuard.width p D ∧
      (xs h j k).2.length=ButterflyGuard.width p D) :
    HoareTime program (fun z => z=bank D t R p (ButterflyAxisBank.word xs))
      (fun z => z=bank D t R p (ButterflyAxisBank.word (transformed xs)))
      (ButterflyAxisRun.constant*logicalVolume D R p) := by
  have hh := ButterflyInverseAxisRun.runs_linear (headers D t R p) (headers_spec D t R p)
    (descriptor_positive D t R p hR) (divides D t R p) xs (ButterflyGuard.width p D) hw
    (row_length D t R p) (words D t R p 0) (words D t R p 1)
    (paired_count D t R p) (stream_count D t R p) (words_canonical D t R p 0) (words_canonical D t R p 1)
  rw [ButterflyAxisPrepared.volume_eq D t R p ht] at hh
  apply CleanSubbank.realizes (c:=9) (s:=ButterflyAxisPorts.count) (k:=52) ButterflyInverseAxisRun.program
    ButterflyAxisPorts.ports commonPorts ButterflyAxisPorts.injective common_injective
    (prepared D t R p (ButterflyAxisBank.word xs)) (prepared D t R p (ButterflyAxisBank.word (transformed xs)))
    _ _ _ ?_ ?_ ?_ ?_ ?_ hh
  · rw [ButterflyAxisPorts.payload,payload]
  · rw [ButterflyAxisPorts.payload,payload]
  · exact ButterflyAxisPorts.clean _ _ _ _
  · exact ButterflyAxisPorts.clean _ _ _ _
  · exact frame D t R p _ _

end
end IntegerMultBounds.Machine.ButterflyInverseAxisPrepared
