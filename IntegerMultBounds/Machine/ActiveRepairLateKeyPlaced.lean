import IntegerMultBounds.Machine.ActiveRepairLateKeyRun

/-! Full later key computation on arbitrary original caller ports. -/
namespace IntegerMultBounds.Machine.ActiveRepairLateKeyPlaced
noncomputable section
open ActiveRepairLateKeyData ActiveRepairLateKeyData.Data ActiveRepairLateKeyRun
open ActiveRepairEarlyKeyPlacement
variable {k : ℕ}

def program (focus : Fin 33 → Fin k) (hf : Function.Injective focus) :=
  ActiveRepairEarlyKeyPlacement.program (s := 58) ActiveRepairLateKeyRun.program focus hf

def result (caller : Tapes k 1) (focus : Fin 33 → Fin k) (d : Data) :=
  SharedPlacementAlphabet.setTape caller (focus 31)
    (FlagCopy.keyTape (FlagCopy.keyWord d.flag d.destination)) 0

theorem runs (caller : Tapes k 1) (focus : Fin 33 → Fin k) (hf : Function.Injective focus)
    (d : Data) (h : Valid d) (hp : SharedBank.payload caller focus=d.input) :
    HoareTime (program focus hf) (fun z => z=CleanSubbank.bank (s := 91) caller)
      (fun z => z=CleanSubbank.bank (s := 91) (result caller focus d)) (61000*(d.A+1)) := by
  have hh := ActiveRepairEarlyKeyPlacement.runs (c := 33) (s := 58)
    ActiveRepairLateKeyRun.program caller focus hf d.input d.output _ hp (runs_linear d h)
  have he : install caller focus d.output=result caller focus d := by
    apply install_eq
    · unfold result output
      rw [CompactGadgetReservationPlacement.payload_set _ _ hf,hp]
    · unfold result
      rw [CompactGadgetReservationPlacement.strip_set]
  rw [he] at hh
  exact hh

theorem frame (caller : Tapes k 1) (focus : Fin 33 → Fin k) (d : Data)
    (i : Fin k) (hi : i≠focus 31) :
    (result caller focus d).head i=caller.head i ∧
      (result caller focus d).tape i=caller.tape i := by
  simp [result,SharedPlacementAlphabet.setTape,hi]

end
end IntegerMultBounds.Machine.ActiveRepairLateKeyPlaced
