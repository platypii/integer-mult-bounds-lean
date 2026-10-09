import IntegerMultBounds.Machine.ActiveRepairLateKeyOriginalPlaced

/-! Complete original-descriptor later key execution and paid cleanup. -/
namespace IntegerMultBounds.Machine.ActiveRepairLateKeyOriginal
noncomputable section
abbrev Data := ActiveRepairLateKeyOriginalData.Data
abbrev Valid := ActiveRepairLateKeyOriginalValid.Valid
abbrev program := ActiveRepairLateKeyOriginalRun.program
abbrev constant := ActiveRepairLateKeyOriginalRun.constant

theorem runs_linear (d : Data) (h : Valid d) :
    HoareTime (program d.side) (fun z => z=CleanSubbank.bank (s := 91) d.input)
      (fun z => z=CleanSubbank.bank (s := 91) d.output) (constant*(d.geom.addressBits+1)) :=
  ActiveRepairLateKeyOriginalRun.runs_linear d h

theorem headers_blank (d : Data) :
    SharedBank.payload d.input ActiveRepairLateKeyOriginalData.generatedSlots=SharedBank.empty 15 1 :=
  SharedBank.strip_payload _ _

theorem output_headers_blank (d : Data) :
    SharedBank.payload d.output ActiveRepairLateKeyOriginalData.generatedSlots=SharedBank.empty 15 1 := by
  rw [← headers_blank d]
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    have hi : ActiveRepairLateKeyOriginalData.generatedSlots i≠(31 : Fin 43) := by
      fin_cases i <;> decide
    simp only [ActiveRepairLateKeyOriginalData.Data.output,
      SharedPlacementAlphabet.setTape,Function.update_of_ne hi]

end
end IntegerMultBounds.Machine.ActiveRepairLateKeyOriginal
