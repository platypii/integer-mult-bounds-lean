import IntegerMultBounds.Machine.ActiveRepairEarlyKeyOriginalPlaced

/-! Complete original-descriptor early key execution and paid cleanup. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyKeyOriginal
noncomputable section
abbrev Data := ActiveRepairEarlyKeyOriginalData.Data
abbrev Valid := ActiveRepairEarlyKeyOriginalValid.Valid
abbrev program := ActiveRepairEarlyKeyOriginalRun.program
abbrev constant := ActiveRepairEarlyKeyOriginalRun.constant

theorem runs_linear (d : Data) (h : Valid d) :
    HoareTime (program d.side) (fun z => z=CleanSubbank.bank (s := 84) d.input)
      (fun z => z=CleanSubbank.bank (s := 84) d.output) (constant*(d.geom.addressBits+1)) :=
  ActiveRepairEarlyKeyOriginalRun.runs_linear d h

theorem headers_blank (d : Data) :
    SharedBank.payload d.input ActiveRepairEarlyKeyOriginalData.generatedSlots=SharedBank.empty 15 1 :=
  SharedBank.strip_payload _ _

end
end IntegerMultBounds.Machine.ActiveRepairEarlyKeyOriginal
