import IntegerMultBounds.Machine.BinaryPackedEarlyRunBudget

/-! The complete early four-load machine on arbitrary caller-owned ports.
The actual reserved array changes in place; all other caller tapes and heads
are retained, and every native workspace tape returns wholly blank. -/
namespace IntegerMultBounds.Machine.BinaryPackedEarlyRunPlaced
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape
open SharedPlacementAlphabet (setTape)
open BinaryPackedEarlyRunBank (Work bank store)
variable {t : ℕ}

abbrev Native := 18+Work
def ports : Fin 18 → Fin Native := Fin.castAdd Work
theorem ports_injective : Function.Injective ports := Fin.castAdd_injective _ _
def program (focus : Fin 18 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed BinaryPackedEarlyRun.program (CleanSubbank.placement ports focus hf)
def result {m : ℕ} (caller : Tapes t prime) (focus : Fin 18 → Fin t) (x : Fin m → Bool) :=
  setTape caller (focus 8) (BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i))) 0

theorem native_payload (caller : Tapes 18 prime) :
    SharedBank.payload (BinaryPackedEarlyRun.input caller) ports=caller :=
  CleanSubbank.payload_bank caller
theorem native_clean (caller : Tapes 18 prime) :
    SharedBank.strip (BinaryPackedEarlyRun.input caller) ports=SharedBank.empty Native prime :=
  SharedBankFrames.strip_common_single_blank caller Work

theorem overwrite {m k : ℕ} (caller : Tapes 18 prime) (x : Fin m → Bool) (y : Fin k → Bool) :
    store (store caller x) y=store caller y := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases hi : i=8
  all_goals first
    | (subst i; simp [store,setTape])
    | simp [store,setTape,Function.update_of_ne hi]

theorem runs (caller : Tapes t prime) (focus : Fin 18 → Fin t) (hf : Function.Injective focus)
    (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H)
    (st sc : Fin 4 → List Bool) (hs : Fin 7 → List Bool) (Z : List Bool)
    (hb : 1≤b) (hbq : b+1≤q) (hr : 0<rows) (hp : 0<s.payload)
    (hv : ∀ i,Counter.value (hs i)=BinaryPackedEarlyRunGap.values s q b n rows i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n)
    (hst : ∀ i,Counter.value (st i)=BinaryRadixRangePrepare.values rows
      (BinaryPackedEarlyGeometry.tempGap s q b n) (CompactGadgetReservationHeadersCarvedData.suffix s (n*q)) (n*q) i)
    (hct : ∀ i,GrowingCounterData.Canonical (st i))
    (hsc : ∀ i,Counter.value (sc i)=BinaryRadixRangePrepare.values
      (BinaryPackedEarlyGeometry.controlPrefix s q n rows) (BinaryPackedEarlyGeometry.controlGap s b n)
      (CompactGadgetReservationHeadersCarvedData.suffix s (n*b)) (n*b) i)
    (hcc : ∀ i,GrowingCounterData.Canonical (sc i))
    (x : Fin (rows*s.recordWidth) → Bool)
    (hi : SharedBank.payload caller focus=store (bank st sc hs Z) x) :
    HoareTime (program focus hf) (fun v => v=CleanSubbank.bank (s := Native) caller)
      (fun v => v=CleanSubbank.bank (s := Native)
        (result caller focus (BinaryPackedEarlyArray.run s q b n rows hq hw Z hb hbq x)))
      (BinaryPackedEarlyRun.cost s q b n rows st sc hs Z hb hbq) := by
  apply CleanSubbank.realizes _ ports focus ports_injective hf caller
    (result caller focus (BinaryPackedEarlyArray.run s q b n rows hq hw Z hb hbq x))
    (BinaryPackedEarlyRun.input (store (bank st sc hs Z) x))
    (BinaryPackedEarlyRun.input (store (bank st sc hs Z)
      (BinaryPackedEarlyArray.run s q b n rows hq hw Z hb hbq x))) _
  · rw [native_payload,hi]
  · rw [native_payload,result,CompactGadgetReservationPlacement.payload_set caller focus hf,hi]
    exact (overwrite (bank st sc hs Z) x _).symm
  · exact native_clean _
  · exact native_clean _
  · exact (CompactGadgetReservationPlacement.strip_set caller focus 8 _ 0).symm
  · exact BinaryPackedEarlyRun.runs s q b n rows hq hw st sc hs Z hb hbq hr hp hv hc hZ hst hct hsc hcc x

end
end IntegerMultBounds.Machine.BinaryPackedEarlyRunPlaced
