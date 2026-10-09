import IntegerMultBounds.Machine.ActivePrefixDirtyControlUSwapRun
import IntegerMultBounds.Machine.SharedBankFrames

/-! Complete original-geometry compact swap on arbitrary caller tapes. Nine
ports retain the original eight numeric words and full array, with all native
private storage blank and every complementary caller tape unchanged. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlUSwapPlaced
noncomputable section
open ActivePrefixDirtyControlUSwapData ActivePrefixDirtyControlUSwapRun
open CompactGadgetReservationShape
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
variable {t : ℕ}

abbrev count := 13+40+scratch
def corePorts : Fin 9 → Fin 13 := ![0,1,2,3,4,5,6,7,12]
def middlePorts (i : Fin 9) := Fin.castAdd 40 (corePorts i)
def ports (i : Fin 9) := Fin.castAdd scratch (middlePorts i)
theorem core_injective : Function.Injective corePorts := by decide
theorem ports_injective : Function.Injective ports :=
  (Fin.castAdd_injective _ _).comp ((Fin.castAdd_injective _ _).comp core_injective)

def sources (hs : Fin 7 → List Bool) (bs : List Bool) {s : Shape} {rows w : ℕ} (x : Array s rows w) :=
  SharedBank.payload (base hs bs x) corePorts

def result (caller : Tapes t prime) (focus : Fin 9 → Fin t) {s : Shape} {rows w : ℕ} (x : Array s rows w) :=
  setTape caller (focus 8) (BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (RadixRangePadding.transpose x i))) 0

def program (focus : Fin 9 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed ActivePrefixDirtyControlUSwapRun.program (CleanSubbank.placement ports focus hf)

theorem native_payload (hs : Fin 7 → List Bool) (bs : List Bool) {s : Shape} {rows w : ℕ} (x : Array s rows w) :
    SharedBank.payload (bank (base hs bs x)) ports=sources hs bs x := by
  change SharedBank.payload (((base hs bs x).append (SharedBank.empty 40 prime)).append (SharedBank.empty scratch prime))
    (fun i => Fin.castAdd scratch (middlePorts i))=_
  rw [SharedBankFrames.payload_append_left]
  change SharedBank.payload ((base hs bs x).append (SharedBank.empty 40 prime))
    (fun i => Fin.castAdd 40 (corePorts i))=_
  rw [SharedBankFrames.payload_append_left]
  rfl

theorem core_clean (hs : Fin 7 → List Bool) (bs : List Bool) {s : Shape} {rows w : ℕ} (x : Array s rows w) :
    SharedBank.strip (base hs bs x) corePorts=SharedBank.empty 13 prime := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [corePorts,base,Fin.exists_fin_succ]

theorem native_clean (hs : Fin 7 → List Bool) (bs : List Bool) {s : Shape} {rows w : ℕ} (x : Array s rows w) :
    SharedBank.strip (bank (base hs bs x)) ports=SharedBank.empty count prime := by
  change SharedBank.strip (((base hs bs x).append (SharedBank.empty 40 prime)).append (SharedBank.empty scratch prime))
    (fun i => Fin.castAdd scratch (middlePorts i))=_
  rw [SharedBankFrames.strip_append_left]
  change (SharedBank.strip ((base hs bs x).append (SharedBank.empty 40 prime))
    (fun i => Fin.castAdd 40 (corePorts i))).append (SharedBank.empty scratch prime)=_
  rw [SharedBankFrames.strip_append_left,core_clean,SharedBankFrames.empty_append,SharedBankFrames.empty_append]

theorem native_output (hs : Fin 7 → List Bool) (bs : List Bool) {s : Shape} {rows w : ℕ} (x : Array s rows w) :
    bank (base hs bs (RadixRangePadding.transpose x))=setTape (bank (base hs bs x)) (ports 8)
      (BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (RadixRangePadding.transpose x i))) 0 := by
  rw [←base_store hs bs x (RadixRangePadding.transpose x)]
  unfold bank BinaryRadixEqualShared.input CleanSubbank.bank store BinaryPackedFieldSwap.store
  change ((setTape (base hs bs x) 12 _ 0).append (SharedBank.empty 40 prime)).append
    (FixedHeaderBankCopy.empty scratch)=
    setTape (((base hs bs x).append (SharedBank.empty 40 prime)).append (FixedHeaderBankCopy.empty scratch))
      (Fin.castAdd scratch (Fin.castAdd 40 (12 : Fin 13))) _ 0
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left]

theorem runs (caller : Tapes t prime) (focus : Fin 9 → Fin t) (hf : Function.Injective focus)
    (s : Shape) (n rows b : ℕ) (hs : Fin 7 → List Bool) (bs : List Bool) (x : Array s rows (n*b))
    (hsrc : SharedBank.payload caller focus=sources hs bs x)
    (hv : ∀ i, Counter.value (hs i)=CompactGadgetReservationHeadersCarvedSchedule.originalValues s n rows i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hb : Counter.value bs=b) (cb : GrowingCounterData.Canonical bs) (hbp : 0<b)
    (hr : 0<rows) (hK : 0<s.chunk) (hd : 0<s.axes) (hg : 0<s.guard) (hp : 0<s.payload) (hw : n*b≤s.H) :
    HoareTime (program focus hf) (fun v => v=CleanSubbank.bank (s := count) caller)
      (fun v => v=CleanSubbank.bank (s := count) (result caller focus x)) (cost s rows (n*b)) := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller (result caller focus x)
    _ _ _ ?_ ?_ (native_clean hs bs x) (native_clean hs bs _) ?_
    (ActivePrefixDirtyControlUSwapRun.runs s n rows b hs bs x hv hc hb cb hbp hr hK hd hg hp hw)
  · rw [native_payload,hsrc]
  · rw [native_output]
    simp only [result,CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,native_payload,hsrc]
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

theorem frame (caller : Tapes t prime) (focus : Fin 9 → Fin t) {s : Shape} {rows w : ℕ}
    (x : Array s rows w) (i : Fin t) (hi : i≠focus 8) :
    (result caller focus x).head i=caller.head i ∧ (result caller focus x).tape i=caller.tape i := by
  simp [result,setTape,hi]

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlUSwapPlaced
