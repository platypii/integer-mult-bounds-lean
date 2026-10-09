import IntegerMultBounds.Machine.BinaryPrefixFieldTableData
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersPowerRound

/-! Physical table and dummy-zero constructors sharing fifteen private tapes.
Only the selected destination changes; every workspace tape returns blank. -/
namespace IntegerMultBounds.Machine.BinaryPrefixFieldTablePrimitives
noncomputable section
open SharedPlacementAlphabet (setTape)
open CompactGadgetReservationHeadersCore (bank)
variable {t k q : ℕ}

def placed (M : Program 15 q 0) (ports : Fin k → Fin 15)
    (focus : Fin k → Fin t) (hf : Function.Injective focus) :=
  Placement.placed M (CleanSubbank.placement ports focus hf)

theorem single (M : Program 15 q 0) (ports : Fin k → Fin 15)
    (hp : Function.Injective ports) (focus : Fin k → Fin t) (hf : Function.Injective focus)
    (v : Tapes t 0) (X : Tapes 15 0) (i : Fin k) (tape : ℤ → Fin 4) (head : ℤ) (C : ℕ)
    (hsel : SharedBank.payload X ports = SharedBank.payload v focus)
    (hclean : SharedBank.strip X ports = SharedBank.empty 15 0)
    (hr : HoareTime M (fun u => u=X) (fun u => u=setTape X (ports i) tape head) C) :
    HoareTime (placed M ports focus hf) (fun u => u=bank v)
      (fun u => u=bank (setTape v (focus i) tape head)) C := by
  refine CleanSubbank.realizes M ports focus hp hf v (setTape v (focus i) tape head)
    X (setTape X (ports i) tape head) C hsel ?_ hclean ?_ ?_ hr
  · simp only [CompactGadgetReservationPlacement.payload_set _ _ hp,
      CompactGadgetReservationPlacement.payload_set _ _ hf,hsel]
  · simpa only [CompactGadgetReservationPlacement.strip_set] using hclean
  · simp only [CompactGadgetReservationPlacement.strip_set]

def tablePorts : Fin 2 → Fin 15 := ![5,1]
theorem table_injective : Function.Injective tablePorts := by decide
def tableCore := extend BinaryAddressTable.program 6
def tableProgram (focus : Fin 2 → Fin t) (hf : Function.Injective focus) := placed tableCore tablePorts focus hf

theorem table (v : Tapes t 0) (focus : Fin 2 → Fin t) (hf : Function.Injective focus)
    (ws : List Bool) (W : ℕ) (hv : Counter.value ws=W) (hc : GrowingCounterData.Canonical ws)
    (ht : v.tape (focus 0)=RadixZeroFill.encodedBinary ws) (hh : v.head (focus 0)=1)
    (hb : v.tape (focus 1)=fun _ => blank) (hz : v.head (focus 1)=0) :
    HoareTime (tableProgram focus hf) (fun z => z=bank v)
      (fun z => z=bank (setTape v (focus 1) (BinaryAddressTable.outputTape W) 0))
      (BinaryAddressTable.constant*((W+1)*2^W)) := by
  let X := (BinaryAddressTable.input ws).append (SharedBank.empty 6 0)
  have he : BinaryAddressTable.bank (fun _ => blank) (BinaryAddressTable.outputTape W)
      (fun _ => blank) (fun _ => blank) 0 0 0 0 ws =
      setTape (BinaryAddressTable.input ws) 1 (BinaryAddressTable.outputTape W) 0 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have h := hoare_extend_eq (BinaryAddressTable.constructs ws W hv hc) (SharedBank.empty 6 0)
  rw [he,← SharedPlacementAlphabet.setTape_append_left] at h
  refine single tableCore tablePorts table_injective focus hf v X 1 _ 0 _ ?_ ?_ h
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [X,tablePorts,BinaryAddressTable.input,BinaryAddressTable.bank,
      Tapes.append,Fin.addCases,ht,hh,hb,hz,BinaryAddressTable.binary_encoded]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [X,tablePorts,BinaryAddressTable.input,BinaryAddressTable.bank,
      Tapes.append,Fin.addCases,Fin.exists_fin_succ,SharedBank.empty]

def fillPorts : Fin 2 → Fin 15 := ![2,0]
theorem fill_injective : Function.Injective fillPorts := by decide
def fillCore := extend BinaryAddressTableFill.program 12
def fillProgram (focus : Fin 2 → Fin t) (hf : Function.Injective focus) := placed fillCore fillPorts focus hf

theorem fill (v : Tapes t 0) (focus : Fin 2 → Fin t) (hf : Function.Injective focus)
    (ns : List Bool) (N : ℕ) (hv : Counter.value ns=N)
    (ht : v.tape (focus 0)=RadixZeroFill.encodedBinary ns) (hh : v.head (focus 0)=1)
    (hb : v.tape (focus 1)=fun _ => blank) (hz : v.head (focus 1)=0) :
    HoareTime (fillProgram focus hf) (fun z => z=bank v)
      (fun z => z=bank (setTape v (focus 1) (CountedCopyReuse.binary (List.replicate N false)) 1))
      (8*N+7*ns.length+39) := by
  let X := (BinaryAddressTableFill.input ns).append (SharedBank.empty 12 0)
  have he : BinaryAddressTableFill.output ns N = setTape (BinaryAddressTableFill.input ns)
      0 (CountedCopyReuse.binary (List.replicate N false)) 1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have h := hoare_extend_eq (BinaryAddressTableFill.runs ns N hv) (SharedBank.empty 12 0)
  rw [he,← SharedPlacementAlphabet.setTape_append_left] at h
  refine single fillCore fillPorts fill_injective focus hf v X 1 _ 1 _ ?_ ?_ h
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [X,fillPorts,BinaryAddressTableFill.input,
      Tapes.append,Fin.addCases,ht,hh,hb,hz,BinaryAddressTable.binary_encoded]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [X,fillPorts,BinaryAddressTableFill.input,Tapes.append,Fin.addCases,
      Fin.exists_fin_succ,SharedBank.empty]

end
end IntegerMultBounds.Machine.BinaryPrefixFieldTablePrimitives
