import IntegerMultBounds.Machine.ActiveRepairRecordFlattenPlaced

namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsDecodeCommon
noncomputable section

 theorem decoder_input (rs : List Partition.Record) :
    ActiveRepairRecordFlattenAlphabet.input 0 rs=
      (ActiveRepairRecordFlatten.cfg (RepairStage.encTape (Partition.encode rs)) (fun _ => blank) 0 0 0).tapes := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i
    · change (fun j => (Alphabet.widen 1 0).encode
        (putWord (fun _ => blank) 0 (ActiveRepairRecordFlatten.encode rs) j))=_
      have hid : (Alphabet.widen 1 0).encode=id := rfl
      rw [hid]
      change putWord (fun _ => blank) 0 (ActiveRepairRecordFlatten.encode rs)=_
      rw [ActiveRepairRecordFlatten.encode_partition]
      exact RepairStage.encTape_eq _
    · rfl

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsDecodeCommon
