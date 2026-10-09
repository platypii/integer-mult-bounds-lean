import IntegerMultBounds.Machine.ActiveRepairEarlyKeyValue
import IntegerMultBounds.Machine.ActiveRepairEarlyKeyPlaced

/-! Complete current-address early key production, from genuine short rank
through exact full-rank reconstruction, conditional output and paid erasure. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyKey
noncomputable section
abbrev Data := ActiveRepairEarlyKeyData.Data
abbrev Valid := ActiveRepairEarlyKeyRun.Valid
abbrev input := ActiveRepairEarlyKeyData.Data.input
abbrev output := ActiveRepairEarlyKeyData.Data.output
abbrev program := ActiveRepairEarlyKeyRun.program

theorem runs_linear (d : Data) (h : Valid d) :
    HoareTime program (fun z => z=CleanSubbank.bank (s := 52) (input d))
      (fun z => z=CleanSubbank.bank (s := 52) (output d)) (29000*(d.A+1)) :=
  ActiveRepairEarlyKeyRun.runs_linear d h

end
end IntegerMultBounds.Machine.ActiveRepairEarlyKey
