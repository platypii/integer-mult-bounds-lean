import IntegerMultBounds.Machine.ActiveRepairEarlyKeyPlacement

/-! Conditional output contains the complete physical destination rank. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyKeyAppend
noncomputable section
open ActiveRepairEarlyKeyPlacement
variable {k : ℕ}

def native := extend CountedRepairKeyAppend.program 48
def program (focus : Fin 4 → Fin k) (hf : Function.Injective focus) :=
  ActiveRepairEarlyKeyPlacement.program (s := 48) native focus hf

theorem runs (caller : Tapes k 1) (focus : Fin 4 → Fin k)
    (hf : Function.Injective focus) (flag : Bool) (destination : List Bool)
    (hp : SharedBank.payload caller focus=CountedRepairKeyAppend.input flag destination []) :
    HoareTime (program focus hf)
      (fun z => z=CleanSubbank.bank (s := 52) caller)
      (fun z => z=CleanSubbank.bank (s := 52)
        (install caller focus (CountedRepairKeyAppend.output flag destination [])))
      (3*destination.length+18) := by
  have h := hoare_extend_eq (CountedRepairKeyAppend.runs flag destination [])
    (SharedBank.empty 48 1)
  simp only [List.length_nil,Nat.add_zero] at h
  exact ActiveRepairEarlyKeyPlacement.runs native caller focus hf _ _ _ hp h

end
end IntegerMultBounds.Machine.ActiveRepairEarlyKeyAppend
