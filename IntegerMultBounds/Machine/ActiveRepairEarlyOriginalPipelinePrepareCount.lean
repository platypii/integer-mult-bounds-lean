import IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelineRun
import IntegerMultBounds.Machine.CountedGuardConstantsFill
import IntegerMultBounds.Machine.CountedGuardGadgetPosition
import IntegerMultBounds.Machine.CountedRepairScanPrepare

/-! Runtime unary filling and return from the original address-width header.
One reusable three-tape bank is physically blank between all operations. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelinePrepareCount
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {k : ℕ}

def ports : Fin 2 → Fin 3 := ![0,2]
theorem ports_injective : Function.Injective ports := by decide
def sources (f : ℤ → Fin 5) (p : ℤ) (hs : List Bool) : Tapes 2 1 :=
  ⟨![p,1],![f,RadixZeroFill.encodedBinary hs]⟩

theorem payload (f : ℤ → Fin 5) (p : ℤ) (hs : List Bool) :
    SharedBank.payload (CountedGuardConstantsFill.input (a := 1) f p hs) ports=sources f p hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact CountedGuardGadgetHeaders.binary_eq hs

theorem clean (f : ℤ → Fin 5) (p : ℤ) (hs : List Bool) :
    SharedBank.strip (CountedGuardConstantsFill.input (a := 1) f p hs) ports=SharedBank.empty 3 1 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [ports,Fin.exists_fin_succ]
  all_goals rfl

def fill (b : Bool) (focus : Fin 2 → Fin k) (hf : Function.Injective focus) :=
  Placement.placed (CountedGuardConstantsFill.fill (a := 1) b) (CleanSubbank.placement ports focus hf)
def back (focus : Fin 2 → Fin k) (hf : Function.Injective focus) :=
  Placement.placed (CountedGuardGadgetPosition.program (a := 1)) (CleanSubbank.placement ports focus hf)

theorem local_result (f g : ℤ → Fin 5) (p r : ℤ) (hs : List Bool) :
    sources g r hs=setTape (sources f p hs) 0 g r := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem realizes {q B : ℕ} (M : Program 3 q 1) (caller : Tapes k 1)
    (focus : Fin 2 → Fin k) (hf : Function.Injective focus) (f g : ℤ → Fin 5)
    (p r : ℤ) (hs : List Bool) (hp : SharedBank.payload caller focus=sources f p hs)
    (h : HoareTime M (fun v => v=CountedGuardConstantsFill.input f p hs)
      (fun v => v=CountedGuardConstantsFill.input g r hs) B) :
    HoareTime (Placement.placed M (CleanSubbank.placement ports focus hf))
      (fun v => v=CleanSubbank.bank (s := 3) caller)
      (fun v => v=CleanSubbank.bank (s := 3) (setTape caller (focus 0) g r)) B := by
  refine CleanSubbank.realizes M ports focus ports_injective hf caller
    (setTape caller (focus 0) g r) _ _ B ?_ ?_ (clean _ _ _) (clean _ _ _) ?_ h
  · rw [payload,hp]
  · rw [payload,CompactGadgetReservationPlacement.payload_set _ _ hf,hp,←local_result]
  · rw [CompactGadgetReservationPlacement.strip_set]

theorem fills (b : Bool) (caller : Tapes k 1) (focus : Fin 2 → Fin k)
    (hf : Function.Injective focus) (f : ℤ → Fin 5) (p : ℤ) (hs : List Bool) (n : ℕ)
    (hp : SharedBank.payload caller focus=sources f p hs) (hv : Counter.value hs=n) :
    HoareTime (fill b focus hf) (fun v => v=CleanSubbank.bank (s := 3) caller)
      (fun v => v=CleanSubbank.bank (s := 3)
        (setTape caller (focus 0) (putWord f p (List.replicate n (bitSymbol b))) (p+n)))
      (7*n+7*hs.length+23) :=
  realizes _ caller focus hf _ _ _ _ hs hp (CountedGuardConstantsFill.fills b f p hs n hv)

theorem returns (caller : Tapes k 1) (focus : Fin 2 → Fin k)
    (hf : Function.Injective focus) (f : ℤ → Fin 5) (p : ℤ) (hs : List Bool) (n : ℕ)
    (hp : SharedBank.payload caller focus=sources f p hs) (hv : Counter.value hs=n) :
    HoareTime (back focus hf) (fun v => v=CleanSubbank.bank (s := 3) caller)
      (fun v => v=CleanSubbank.bank (s := 3) (setTape caller (focus 0) f (p-n)))
      (7*n+7*hs.length+23) :=
  realizes _ caller focus hf _ _ _ _ hs hp (CountedGuardGadgetPosition.positions f p hs n hv)

end
end IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelinePrepareCount
