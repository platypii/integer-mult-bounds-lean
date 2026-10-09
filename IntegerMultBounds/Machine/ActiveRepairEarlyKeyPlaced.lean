import IntegerMultBounds.Machine.ActiveRepairEarlyKeyRun

/-! Full early key computation on arbitrary original caller ports. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyKeyPlaced
noncomputable section
open ActiveRepairEarlyKeyData ActiveRepairEarlyKeyData.Data ActiveRepairEarlyKeyRun
open ActiveRepairEarlyKeyPlacement
variable {k : ℕ}

def program (focus : Fin 32 → Fin k) (hf : Function.Injective focus) :=
  ActiveRepairEarlyKeyPlacement.program (s := 52) ActiveRepairEarlyKeyRun.program focus hf

def result (caller : Tapes k 1) (focus : Fin 32 → Fin k) (d : Data) :=
  SharedPlacementAlphabet.setTape caller (focus 30)
    (FlagCopy.keyTape (FlagCopy.keyWord d.flag d.destination)) 0

theorem runs (caller : Tapes k 1) (focus : Fin 32 → Fin k) (hf : Function.Injective focus)
    (d : Data) (h : Valid d) (hp : SharedBank.payload caller focus=d.input) :
    HoareTime (program focus hf) (fun z => z=CleanSubbank.bank (s := 84) caller)
      (fun z => z=CleanSubbank.bank (s := 84) (result caller focus d)) (29000*(d.A+1)) := by
  have hh := ActiveRepairEarlyKeyPlacement.runs (c := 32) (s := 52)
    ActiveRepairEarlyKeyRun.program caller focus hf d.input d.output _ hp (runs_linear d h)
  have he : install caller focus d.output=result caller focus d := by
    apply install_eq
    · unfold result output
      rw [CompactGadgetReservationPlacement.payload_set _ _ hf,hp]
    · unfold result
      rw [CompactGadgetReservationPlacement.strip_set]
  rw [he] at hh
  exact hh

theorem frame (caller : Tapes k 1) (focus : Fin 32 → Fin k) (d : Data)
    (i : Fin k) (hi : i≠focus 30) :
    (result caller focus d).head i=caller.head i ∧
      (result caller focus d).tape i=caller.tape i := by
  simp [result,SharedPlacementAlphabet.setTape,hi]

end
end IntegerMultBounds.Machine.ActiveRepairEarlyKeyPlaced
