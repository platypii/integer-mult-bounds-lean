import IntegerMultBounds.Machine.ActiveRepairEarlyKeyOriginalGeometry

/-! Original-input early key production on arbitrary caller tapes, retaining
all original descriptors, the scan counter, and every complementary frame. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyKeyOriginalPlaced
noncomputable section
open ActiveRepairEarlyKeyOriginalData ActiveRepairEarlyKeyOriginalValid
open ActiveRepairEarlyKeyPlacement
variable {k : ℕ}

def program (side : ActiveRepairRankHeadersData.SourceSide) (focus : Fin 42 → Fin k)
    (hf : Function.Injective focus) := ActiveRepairEarlyKeyPlacement.program (s := 84)
  (ActiveRepairEarlyKeyOriginalRun.program side) focus hf

def result (caller : Tapes k 1) (focus : Fin 42 → Fin k) (d : Data) :=
  SharedPlacementAlphabet.setTape caller (focus 30)
    (FlagCopy.keyTape (FlagCopy.keyWord d.key.flag d.key.destination)) 0

theorem runs (caller : Tapes k 1) (focus : Fin 42 → Fin k) (hf : Function.Injective focus)
    (d : Data) (h : Valid d) (hp : SharedBank.payload caller focus=d.input) :
    HoareTime (program d.side focus hf) (fun z => z=CleanSubbank.bank (s := 126) caller)
      (fun z => z=CleanSubbank.bank (s := 126) (result caller focus d))
      (ActiveRepairEarlyKeyOriginalRun.constant*(d.geom.addressBits+1)) := by
  have hh := ActiveRepairEarlyKeyPlacement.runs (c := 42) (s := 84)
    (ActiveRepairEarlyKeyOriginalRun.program d.side) caller focus hf d.input d.output _ hp
    (ActiveRepairEarlyKeyOriginalRun.runs_linear d h)
  have he : install caller focus d.output=result caller focus d := by
    apply install_eq
    · unfold result Data.output
      rw [CompactGadgetReservationPlacement.payload_set _ _ hf,hp]
    · unfold result
      rw [CompactGadgetReservationPlacement.strip_set]
  rw [he] at hh
  exact hh

theorem frame (caller : Tapes k 1) (focus : Fin 42 → Fin k) (d : Data)
    (i : Fin k) (hi : i≠focus 30) :
    (result caller focus d).head i=caller.head i ∧
      (result caller focus d).tape i=caller.tape i := by
  simp [result,SharedPlacementAlphabet.setTape,hi]

end
end IntegerMultBounds.Machine.ActiveRepairEarlyKeyOriginalPlaced
