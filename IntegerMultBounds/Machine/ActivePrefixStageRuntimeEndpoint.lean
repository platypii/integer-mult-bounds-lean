import IntegerMultBounds.Machine.ActivePrefixStageRuntimeBudget

/-! Both runtime flags and all generated/private tapes are physically blank at
stage boundaries. Original descriptors remain in place and raw data stays65. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageRuntimeEndpoint
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs original)
open ActivePrefixStageRuntimeProgram
open ActiveRepairLayoutRecordsData (Array)
variable {s : Shape}

theorem bank_eq_original (d : Inputs s) (x : Array s d.rows) :
    bank d x=SharedBankStageInput.raw (original d x) count := by
  rw [bank_eq_raw]
  change SharedBankStageInput.raw
    (CleanSubbank.bank (s:=1) (CleanSubbank.bank (s:=1) (original d x))) count=_
  rw [SharedBankRawCompose.bank_eq_raw,SharedBankRawCompose.bank_eq_raw]
  rw [ActivePrefixEarlySequenceOriginalPlaced.raw_twice _ (by decide : 66≤67)]
  rw [ActivePrefixEarlySequenceOriginalPlaced.raw_twice _ (by decide : 66≤68)]

theorem private_blank (d : Inputs s) (x : Array s d.rows) (i : Fin count)
    (hl : 13 ≤ i.val) (hn : i.val≠65) :
    (bank d x).head i=0 ∧ (bank d x).tape i=(fun _ => blank) := by
  rw [bank_eq_original]
  by_cases h66 : i.val<66
  · have h := ActivePrefixStageFullEndpoint.original_blank d x ⟨i.val,h66⟩ hl hn
    simpa only [SharedBankStageInput.raw,h66,dite_true] using h
  · simp only [SharedBankStageInput.raw,h66,dite_false,and_self]

def publicSlots : Fin 66 → Fin count := fun i =>
  Fin.castAdd 3 (Fin.castLE public_le (Fin.castAdd 2 i))

theorem originals (d : Inputs s) (x : Array s d.rows) :
    SharedBank.payload (bank d x) publicSlots=original d x := by
  rw [bank_eq_original]
  exact SharedBankRawCompose.payload_raw _ _ (fun _ => rfl)

theorem raw (d : Inputs s) (x : Array s d.rows) :
    (bank d x).head (publicSlots 65)=0 ∧ (bank d x).tape (publicSlots 65)=ActiveTargetRotation.word x := by
  have h := originals d x
  have hh := congrFun (congrArg Tapes.head h) (65:Fin 66)
  have ht := congrFun (congrArg Tapes.tape h) (65:Fin 66)
  exact ⟨hh.trans (ActivePrefixStageFullEndpoint.original_raw d x).1,
    ht.trans (ActivePrefixStageFullEndpoint.original_raw d x).2⟩

end
end IntegerMultBounds.Machine.ActivePrefixStageRuntimeEndpoint
