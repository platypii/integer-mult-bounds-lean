import IntegerMultBounds.Machine.ActiveRepairLateKeyValue
import IntegerMultBounds.Machine.ActiveRepairLateKeyPlaced

/-! Complete current-address later key production, from genuine short rank
through exact full-rank reconstruction, conditional output and paid erasure. -/
namespace IntegerMultBounds.Machine.ActiveRepairLateKey
noncomputable section
abbrev Data := ActiveRepairLateKeyData.Data
abbrev Valid := ActiveRepairLateKeyRun.Valid
abbrev input := ActiveRepairLateKeyData.Data.input
abbrev output := ActiveRepairLateKeyData.Data.output
abbrev program := ActiveRepairLateKeyRun.program

theorem runs_linear (d : Data) (h : Valid d) :
    HoareTime program (fun z => z=CleanSubbank.bank (s := 58) (input d))
      (fun z => z=CleanSubbank.bank (s := 58) (output d)) (61000*(d.A+1)) :=
  ActiveRepairLateKeyRun.runs_linear d h

end
end IntegerMultBounds.Machine.ActiveRepairLateKey
