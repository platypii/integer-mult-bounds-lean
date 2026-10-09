import IntegerMultBounds.Machine.ActivePrefixStageWidthSelector
import IntegerMultBounds.Machine.CompactGadgetReservationPlacement

/-! Width selection exposes just the original f word and one blank result
flag on an arbitrary caller. The physically constructed one lives in the
clean private bank; every other caller tape is framed. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageWidthPlaced
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {t a : ℕ}

def ports : Fin 2 → Fin 3 := ![1,2]
theorem ports_injective : Function.Injective ports := by decide

def sources (fs : List Bool) : Tapes 2 a :=
  ⟨![1,0],![BinaryDescriptorStack.descriptor fs,fun _ => blank]⟩
def marked (v : Tapes t a) (focus : Fin 2 → Fin t) (fs : List Bool) :=
  setTape v (focus 1) (BinaryDescriptorCompare.result (RecursiveChildQuotientsConstant.bits 1) fs) 0

theorem native_payload (fs : List Bool) : SharedBank.payload (ActivePrefixStageWidthSelector.input (a := a) fs) ports=sources fs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem native_output (fs : List Bool) : SharedBank.payload (ActivePrefixStageWidthSelector.output (a := a) fs) ports=
    marked (sources fs) id fs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem input_clean (fs : List Bool) : SharedBank.strip (ActivePrefixStageWidthSelector.input (a := a) fs) ports=SharedBank.empty 3 a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [ports,Fin.exists_fin_succ,ActivePrefixStageWidthSelector.input]

theorem output_clean (fs : List Bool) : SharedBank.strip (ActivePrefixStageWidthSelector.output (a := a) fs) ports=SharedBank.empty 3 a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [ports,Fin.exists_fin_succ,ActivePrefixStageWidthSelector.output]

def program (focus : Fin 2 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActivePrefixStageWidthSelector.program (a := a)) (CleanSubbank.placement ports focus hf)
def cleanup (focus : Fin 2 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActivePrefixStageWidthSelector.cleanup (a := a)) (CleanSubbank.placement ports focus hf)

theorem marked_payload (v : Tapes t a) (focus : Fin 2 → Fin t) (hf : Function.Injective focus)
    (fs : List Bool) (hsrc : SharedBank.payload v focus=sources fs) :
    SharedBank.payload (marked v focus fs) focus=SharedBank.payload (ActivePrefixStageWidthSelector.output fs) ports := by
  rw [native_output]
  unfold marked
  rw [CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc]
  rfl

theorem runs (v : Tapes t a) (focus : Fin 2 → Fin t) (hf : Function.Injective focus)
    (fs : List Bool) (hsrc : SharedBank.payload v focus=sources fs) :
    HoareTime (program focus hf) (fun w => w=CleanSubbank.bank (s := 3) v)
      (fun w => w=CleanSubbank.bank (s := 3) (marked v focus fs)) (ActivePrefixStageWidthSelector.cost fs) := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf v _ (ActivePrefixStageWidthSelector.input fs) (ActivePrefixStageWidthSelector.output fs) _
    ?_ ?_ (input_clean fs) (output_clean fs) ?_ (ActivePrefixStageWidthSelector.runs fs)
  · exact (native_payload fs).trans hsrc.symm
  · exact (marked_payload v focus hf fs hsrc).symm
  · exact (CompactGadgetReservationPlacement.strip_set v focus (1 : Fin 2) _ 0).symm

theorem cleans (v : Tapes t a) (focus : Fin 2 → Fin t) (hf : Function.Injective focus)
    (fs : List Bool) (hsrc : SharedBank.payload v focus=sources fs) :
    HoareTime (cleanup focus hf) (fun w => w=CleanSubbank.bank (s := 3) (marked v focus fs))
      (fun w => w=CleanSubbank.bank (s := 3) v) 1 := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf _ v (ActivePrefixStageWidthSelector.output fs) (ActivePrefixStageWidthSelector.input fs) _
    ?_ ?_ (output_clean fs) (input_clean fs) ?_ (ActivePrefixStageWidthSelector.cleans fs)
  · exact (marked_payload v focus hf fs hsrc).symm
  · exact (native_payload fs).trans hsrc.symm
  · exact CompactGadgetReservationPlacement.strip_set v focus (1 : Fin 2) _ 0

def test (focus : Fin 2 → Fin t) (sy : Fin (t+3) → Fin (a+4)) :=
  decide (sy (Fin.castAdd 3 (focus 1))=bitSymbol true)

theorem test_eq (v : Tapes t a) (focus : Fin 2 → Fin t) (fs : List Bool) :
    test focus (CleanSubbank.bank (s := 3) (marked v focus fs)).reads=decide (1<Counter.value fs) := by
  simp only [test,Tapes.reads,CleanSubbank.bank,Tapes.append,Fin.addCases_left,marked,setTape,Function.update_self]
  change decide (bitSymbol (a := a) (decide (Counter.value (RecursiveChildQuotientsConstant.bits 1)<Counter.value fs))=bitSymbol true)=_
  rw [RecursiveChildQuotientsConstant.bits_value]
  by_cases h : 1<Counter.value fs <;> simp [h,bitSymbol,Fin.ext_iff]

end
end IntegerMultBounds.Machine.ActivePrefixStageWidthPlaced
