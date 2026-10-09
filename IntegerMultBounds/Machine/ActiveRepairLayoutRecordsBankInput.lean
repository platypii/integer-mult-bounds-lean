import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsBankHeaders
import IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelineEndpoint

/-! Exact consumer wiring: the generated fifteen-word bank fills every
nonblank repair descriptor port, and the remaining initial bank contains only
the actual unmarked source records. All work tapes and heads start blank. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsBankInput
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsHeadersData ActiveRepairLayoutRecordsBankHeaders
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

def destinations : Fin 15 → Fin 183 := ![44,45,46,47,48,49,50,51,52,53,27,28,29,30,31]
theorem destinations_injective : Function.Injective destinations := by decide

def raw (rs : List Partition.Record) : Tapes 183 1 :=
  ⟨fun _ => 0,fun i => if i=11 then RepairScan.srcTape rs else fun _ => blank⟩

theorem metadata (d : Inputs s p offset rows) (rs : List Partition.Record) :
    SharedBank.payload (ActiveRepairEarlyOriginalPipelineEndpoint.input (repair d) rs) destinations=
      FixedHeaderBankCopy.headerBank (words d) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem blank_work (d : Inputs s p offset rows) (rs : List Partition.Record) :
    SharedBank.strip (ActiveRepairEarlyOriginalPipelineEndpoint.input (repair d) rs) destinations=raw rs := by
  apply congrArg₂ Tapes.mk
  · funext i
    change (if ∃ j, destinations j = i then 0 else
      (ActiveRepairEarlyOriginalPipelineEndpoint.input (repair d) rs).head i) = 0
    fin_cases i
    all_goals first
      | rw [ite_eq_left (by decide)]
      | rw [ite_eq_right (by decide)]; rfl
  · funext i
    change (if ∃ j, destinations j = i then (fun _ => blank) else
      (ActiveRepairEarlyOriginalPipelineEndpoint.input (repair d) rs).tape i) =
      (if i=11 then RepairScan.srcTape rs else fun _ => blank)
    fin_cases i
    all_goals first
      | rw [ite_eq_left (by decide)] <;> rfl
      | rw [ite_eq_right (by decide)]; rfl

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsBankInput
