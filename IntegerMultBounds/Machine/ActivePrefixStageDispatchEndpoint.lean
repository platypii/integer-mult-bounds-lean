import IntegerMultBounds.Machine.ActivePrefixStageDispatchBudget
import IntegerMultBounds.Machine.ActivePrefixStageFullEndpoint

/-! The dispatched caller retains original thirteen numeric words and raw65;
every generated descriptor, runtime flag and private tape is physically blank. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageDispatchEndpoint
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs original)
open ActivePrefixStageDispatchRun
open ActiveRepairLayoutRecordsData (Array)
open Networks.Shared50ModularControl (prime)
variable {s : Shape}

theorem bank_eq_raw (d : Inputs s) (x : Array s d.rows) :
    bank d x=SharedBankStageInput.raw (original d x) count := by
  change SharedBankStageInput.raw (CleanSubbank.bank (s:=1) (original d x)) count=_
  rw [SharedBankRawCompose.bank_eq_raw,ActivePrefixEarlySequenceOriginalPlaced.raw_twice _ (by decide : 66≤67)]

theorem bank_blank (d : Inputs s) (x : Array s d.rows) (i : Fin count) (hl : 13 ≤ i.val) (hn : i.val ≠ 65) :
    (bank d x).head i=0 ∧ (bank d x).tape i=(fun _ => blank) := by
  rw [bank_eq_raw]
  by_cases h66 : i.val<66
  · have h := ActivePrefixStageFullEndpoint.original_blank d x ⟨i.val,h66⟩ hl hn
    simpa only [SharedBankStageInput.raw,h66,dite_true] using h
  · simp only [SharedBankStageInput.raw,h66,dite_false,and_self]

def rawSlot : Fin count := Fin.castLE permanent_le (Fin.castAdd 1 (65:Fin 66))

theorem raw (d : Inputs s) (x : Array s d.rows) :
    (bank d x).head rawSlot=0 ∧ (bank d x).tape rawSlot=ActiveTargetRotation.word x := by
  rw [bank_eq_raw]
  change (if h : 65<66 then (original d x).head ⟨65,h⟩ else 0)=0 ∧
    (if h : 65<66 then (original d x).tape ⟨65,h⟩ else fun _ => blank)=ActiveTargetRotation.word x
  simp only [dite_eq_left (by decide : 65<66)]
  exact ActivePrefixStageFullEndpoint.original_raw d x

end
end IntegerMultBounds.Machine.ActivePrefixStageDispatchEndpoint
