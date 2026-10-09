import IntegerMultBounds.Machine.BinaryPrefixFieldTableAlphabet

/-! Actual field-table construction at arbitrary caller ports. Only three
canonical original descriptors and a blank output are needed; all original
and spectator tapes are retained and all private workspace returns blank. -/
namespace IntegerMultBounds.Machine.BinaryPrefixFieldTablePlaced
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {a t : ℕ}

def ports : Fin 4 → Fin 24 := ![0,1,2,7]
theorem ports_injective : Function.Injective ports := by decide

def sources (hs : Fin 3 → List Bool) : Tapes 4 a :=
  ⟨![1,1,1,0],![RadixZeroFill.encodedBinary (hs 0),RadixZeroFill.encodedBinary (hs 1),
    RadixZeroFill.encodedBinary (hs 2),fun _ => blank]⟩
def result (caller : Tapes t a) (focus : Fin 4 → Fin t) (W start d : ℕ) (h : start+d≤W) :=
  setTape caller (focus 3) (BinaryPrefixFieldTableAlphabet.word W start d h) 0

def program (focus : Fin 4 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (BinaryPrefixFieldTableAlphabet.program a) (CleanSubbank.placement ports focus hf)

theorem native_payload (hs : Fin 3 → List Bool) :
    SharedBank.payload (BinaryPrefixFieldTableAlphabet.bank (a := a) hs (fun _ => blank)) ports=sources hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem native_clean (hs : Fin 3 → List Bool) :
    SharedBank.strip (BinaryPrefixFieldTableAlphabet.bank (a := a) hs (fun _ => blank)) ports=SharedBank.empty 24 a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [BinaryPrefixFieldTableAlphabet.bank,ports,Fin.exists_fin_succ]

theorem constructs (caller : Tapes t a) (focus : Fin 4 → Fin t) (hf : Function.Injective focus)
    (hs : Fin 3 → List Bool) (W start d : ℕ) (h : start+d≤W)
    (hsrc : SharedBank.payload caller focus=sources hs)
    (hv : ∀ i, Counter.value (hs i)=BinaryPrefixFieldTableGather.values W start d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program focus hf) (fun v => v=CleanSubbank.bank (s := 24) caller)
      (fun v => v=CleanSubbank.bank (s := 24) (result caller focus W start d h))
      (BinaryPrefixFieldTableRun.constant*(2^W*(W+1))) := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller
    (result caller focus W start d h) _ _ _ ?_ ?_ (native_clean hs) ?_ ?_
    (BinaryPrefixFieldTableAlphabet.constructs hs W start d h hv hc)
  · rw [native_payload,hsrc]
  · rw [BinaryPrefixFieldTableAlphabet.output_eq]
    simp only [result,show (7 : Fin 24)=ports 3 from rfl,
      CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,native_payload,hsrc]
  · rw [BinaryPrefixFieldTableAlphabet.output_eq]
    simpa only [show (7 : Fin 24)=ports 3 from rfl,CompactGadgetReservationPlacement.strip_set] using native_clean (a := a) hs
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

theorem output_rows (caller : Tapes t a) (focus : Fin 4 → Fin t) (W start d : ℕ) (h : start+d≤W) :
    (result caller focus W start d h).tape (focus 3) = putWord (fun _ => blank) 0
      ((((List.range (2^W)).map (fun i => Gather.field (BinaryAddressTableData.row W i) start d)).flatten).map bitSymbol) ∧
    (result caller focus W start d h).head (focus 3)=0 := by
  simp [result,setTape,BinaryPrefixFieldTableAlphabet.word,BinaryPrefixFieldTableData.word_rows]

theorem frame (caller : Tapes t a) (focus : Fin 4 → Fin t) (W start d : ℕ) (h : start+d≤W)
    (i : Fin t) (hi : i≠focus 3) :
    (result caller focus W start d h).tape i=caller.tape i ∧
      (result caller focus W start d h).head i=caller.head i := by
  simp [result,setTape,hi]

end
end IntegerMultBounds.Machine.BinaryPrefixFieldTablePlaced
