import IntegerMultBounds.Machine.ActiveRepairRecordFormatAlphabet
import IntegerMultBounds.Machine.CompactGadgetReservationPlacement

/-! Caller placement for the real formatter: raw source, record output and
original binary width/count are the only four permanent ports. -/
namespace IntegerMultBounds.Machine.ActiveRepairRecordFormatPlaced
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {a t : ℕ}

def ports : Fin 4 → Fin 6 := ![0,1,3,5]
theorem ports_injective : Function.Injective ports := by decide
def sources (chunks : List (List Bool)) (bs ns : List Bool) :=
  SharedBank.payload (ActiveRepairRecordFormatAlphabet.input a chunks bs ns) ports
def encoded (chunks : List (List Bool)) : ℤ → Fin (a+4) :=
  putWord (fun _ => blank) 0
    ((Partition.encode (ActiveRepairRecordFormatWords.records chunks)).map
      (CountedLoopReuseAlphabet.encoding a).encode)
def result (caller : Tapes t a) (focus : Fin 4 → Fin t) (chunks : List (List Bool)) :=
  setTape caller (focus 1) (encoded chunks) 0
def program (focus : Fin 4 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActiveRepairRecordFormatAlphabet.program a) (CleanSubbank.placement ports focus hf)

theorem clean (chunks : List (List Bool)) (bs ns : List Bool) :
    SharedBank.strip (ActiveRepairRecordFormatAlphabet.input a chunks bs ns) ports=SharedBank.empty 6 a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [ports,Fin.exists_fin_succ]
  all_goals rfl

theorem output_result (chunks : List (List Bool)) (bs ns : List Bool) :
    ActiveRepairRecordFormatAlphabet.output a chunks bs ns=
      result (ActiveRepairRecordFormatAlphabet.input a chunks bs ns) ports chunks := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i
    all_goals first
      | rfl
      | (change (ActiveRepairRecordFormatAlphabet.output a chunks bs ns).tape 1=encoded chunks
         exact ActiveRepairRecordFormatAlphabet.output_encoded a chunks bs ns)

theorem runs (caller : Tapes t a) (focus : Fin 4 → Fin t) (hf : Function.Injective focus)
    (chunks : List (List Bool)) (bs ns : List Bool) (R : ℕ)
    (hw : ∀ xs∈chunks,xs.length=R) (hbs : Counter.value bs=R) (hns : Counter.value ns=chunks.length)
    (hsrc : SharedBank.payload caller focus=sources chunks bs ns) :
    HoareTime (program focus hf) (fun v => v=CleanSubbank.bank (s := 6) caller)
      (fun v => v=CleanSubbank.bank (s := 6) (result caller focus chunks))
      (ActiveRepairRecordFormatEndpoint.cost chunks bs ns R) := by
  have h := ActiveRepairRecordFormatAlphabet.runs a chunks bs ns R hw hbs hns
  rw [output_result] at h
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller (result caller focus chunks)
    _ _ _ hsrc.symm ?_ (clean chunks bs ns) ?_ ?_ h
  · simp only [result,CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,sources]
  · simp only [result,CompactGadgetReservationPlacement.strip_set]
    exact clean chunks bs ns
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

theorem runs_linear (caller : Tapes t a) (focus : Fin 4 → Fin t) (hf : Function.Injective focus)
    (chunks : List (List Bool)) (bs ns : List Bool) (R : ℕ)
    (hw : ∀ xs∈chunks,xs.length=R) (hbs : Counter.value bs=R) (hns : Counter.value ns=chunks.length)
    (hbits : bs.length≤R+1) (hsrc : SharedBank.payload caller focus=sources chunks bs ns) :
    HoareTime (program focus hf) (fun v => v=CleanSubbank.bank (s := 6) caller)
      (fun v => v=CleanSubbank.bank (s := 6) (result caller focus chunks))
      (35*chunks.length*(R+1)+7*ns.length+40) := by
  have h := ActiveRepairRecordFormatAlphabet.runs_linear a chunks bs ns R hw hbs hns hbits
  rw [output_result] at h
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller (result caller focus chunks)
    _ _ _ hsrc.symm ?_ (clean chunks bs ns) ?_ ?_ h
  · simp only [result,CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,sources]
  · simp only [result,CompactGadgetReservationPlacement.strip_set]
    exact clean chunks bs ns
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

end
end IntegerMultBounds.Machine.ActiveRepairRecordFormatPlaced
