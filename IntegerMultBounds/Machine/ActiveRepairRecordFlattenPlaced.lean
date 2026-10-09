import IntegerMultBounds.Machine.ActiveRepairRecordFlattenAlphabet
import IntegerMultBounds.Machine.CompactGadgetReservationPlacement

/-! Actual raw decoder on two caller ports, preserving the full complementary
frame and restoring appended private storage. -/
namespace IntegerMultBounds.Machine.ActiveRepairRecordFlattenPlaced
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {a t : ℕ}

def ports : Fin 2 → Fin 2 := id
theorem ports_injective : Function.Injective ports := Function.injective_id
def raw (rs : List Partition.Record) : ℤ → Fin ((1+a)+4) :=
  putWord (fun _ => blank) 0 (((rs.map Partition.Record.payload).flatten).map bitSymbol)
def result (caller : Tapes t (1+a)) (focus : Fin 2 → Fin t) (rs : List Partition.Record) :=
  setTape (setTape caller (focus 0) (fun _ => blank) 0) (focus 1) (raw rs) 0
def program (focus : Fin 2 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActiveRepairRecordFlattenAlphabet.program a) (CleanSubbank.placement ports focus hf)

theorem payload_id (v : Tapes 2 (1+a)) : SharedBank.payload v ports=v := rfl
theorem clean (v : Tapes 2 (1+a)) : SharedBank.strip v ports=SharedBank.empty 2 (1+a) := by
  apply congrArg₂ Tapes.mk
  · funext i
    change (if ∃ j : Fin 2,id j=i then 0 else v.head i)=0
    simp
  · funext i
    change (if ∃ j : Fin 2,id j=i then (fun _ => blank) else v.tape i)=fun _ => blank
    simp

theorem output_result (rs : List Partition.Record) :
    ActiveRepairRecordFlattenAlphabet.output a rs=
      result (ActiveRepairRecordFlattenAlphabet.input a rs) ports rs := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i
    · change (ActiveRepairRecordFlattenAlphabet.output a rs).head 0=0
      exact ActiveRepairRecordFlattenAlphabet.heads_origin a rs 0
    · change (ActiveRepairRecordFlattenAlphabet.output a rs).head 1=0
      exact ActiveRepairRecordFlattenAlphabet.heads_origin a rs 1
  · funext i; fin_cases i
    · change (ActiveRepairRecordFlattenAlphabet.output a rs).tape 0=fun _ => blank
      exact ActiveRepairRecordFlattenAlphabet.source_blank a rs
    · change (ActiveRepairRecordFlattenAlphabet.output a rs).tape 1=raw rs
      exact ActiveRepairRecordFlattenAlphabet.output_raw a rs

theorem runs (caller : Tapes t (1+a)) (focus : Fin 2 → Fin t) (hf : Function.Injective focus)
    (rs : List Partition.Record)
    (hsrc : SharedBank.payload caller focus=ActiveRepairRecordFlattenAlphabet.input a rs) :
    HoareTime (program focus hf) (fun v => v=CleanSubbank.bank (s := 2) caller)
      (fun v => v=CleanSubbank.bank (s := 2) (result caller focus rs))
      (ActiveRepairRecordFlattenOriginal.cost rs) := by
  have h := ActiveRepairRecordFlattenAlphabet.runs a rs
  rw [output_result] at h
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller (result caller focus rs)
    (ActiveRepairRecordFlattenAlphabet.input a rs)
    (result (ActiveRepairRecordFlattenAlphabet.input a rs) ports rs) _ hsrc.symm ?_ (clean _) (clean _) ?_ h
  · simp only [result,CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,payload_id,hsrc]
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

theorem runs_linear (caller : Tapes t (1+a)) (focus : Fin 2 → Fin t) (hf : Function.Injective focus)
    (rs : List Partition.Record) (R : ℕ) (hw : ∀ r∈rs,r.payload.length≤R)
    (hsrc : SharedBank.payload caller focus=ActiveRepairRecordFlattenAlphabet.input a rs) :
    HoareTime (program focus hf) (fun v => v=CleanSubbank.bank (s := 2) caller)
      (fun v => v=CleanSubbank.bank (s := 2) (result caller focus rs))
      (5*rs.length*(R+1)+12) := by
  have h := ActiveRepairRecordFlattenAlphabet.runs_linear a rs R hw
  rw [output_result] at h
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller (result caller focus rs)
    (ActiveRepairRecordFlattenAlphabet.input a rs)
    (result (ActiveRepairRecordFlattenAlphabet.input a rs) ports rs) _ hsrc.symm ?_ (clean _) (clean _) ?_ h
  · simp only [result,CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,payload_id,hsrc]
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

end
end IntegerMultBounds.Machine.ActiveRepairRecordFlattenPlaced
