import IntegerMultBounds.Machine.ActivePrefixSelectedOffsetData
import IntegerMultBounds.Machine.ActivePrefixOffsetHeadersBudget
import IntegerMultBounds.Machine.BinaryPrefixFieldTablePlaced
import IntegerMultBounds.Machine.SelectedSourceBitsStreamPlaced
import IntegerMultBounds.Machine.BinaryVaryingOffsetGatherPlaced

/-! One permanent caller bank for the original-input varying first load.
The wide target is not placed in a compact front field: this bank only
produces its actual offset word from current prefix-address coordinates. -/
namespace IntegerMultBounds.Machine.ActivePrefixSelectedOffsetBank
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {a : ℕ}

structure Shape where
  W : ℕ
  startT : ℕ
  startX : ℕ
  q : ℕ
  b : ℕ
  n : ℕ
  rho : ℕ
  f : ℕ
  tempFits : startT+n*b≤W
  sourceFits : startX+f*q≤W
  hb : 1≤b
  hbq : b+1≤q
  hnf : n+1=f
  hr : rho<q

def values (s : Shape) : Fin 8 → ℕ := ![s.W,s.startT,s.startX,s.q,s.b,s.n,s.rho,s.f]
def headerFocus : Fin 10 → Fin 17 := ![0,3,4,5,7,8,9,10,11,12]
def tempFocus : Fin 4 → Fin 17 := ![0,1,10,13]
def sourceFocus : Fin 4 → Fin 17 := ![0,2,9,14]
def extractFocus : Fin 7 → Fin 17 := ![14,15,3,5,6,7,8]
def gatherFocus : Fin 6 → Fin 17 := ![3,4,11,13,15,16]
theorem header_injective : Function.Injective headerFocus := by decide
theorem temp_injective : Function.Injective tempFocus := by decide
theorem source_injective : Function.Injective sourceFocus := by decide
theorem extract_injective : Function.Injective extractFocus := by decide
theorem gather_injective : Function.Injective gatherFocus := by decide

def base (hs : Fin 8 → List Bool) : Tapes 17 a :=
  (FixedHeaderBankCopy.headerBank hs).append (SharedBank.empty 9 a)
def headers (s : Shape) (hs : Fin 8 → List Bool) :=
  ActivePrefixOffsetHeadersData.result (base (a := a) hs) headerFocus s.W s.q s.b s.n s.f
def tempWord (s : Shape) := BinaryPrefixFieldTableData.word s.W s.startT (s.n*s.b) s.tempFits
def sourceWord (s : Shape) := BinaryPrefixFieldTableData.word s.W s.startX (s.f*s.q) s.sourceFits
def controlWord (s : Shape) := SelectedSourceBitsStreamData.selected (sourceWord s) s.q s.rho s.n s.f (2^s.W)
def offsetWord (s : Shape) := ActivePrefixSelectedOffsetData.offsets s.W s.startT s.startX
  s.q s.b s.rho s.n s.f s.tempFits s.sourceFits s.hb s.hbq

def tempReady (s : Shape) (hs : Fin 8 → List Bool) :=
  BinaryPrefixFieldTablePlaced.result (headers (a := a) s hs) tempFocus s.W s.startT (s.n*s.b) s.tempFits
def sourceReady (s : Shape) (hs : Fin 8 → List Bool) :=
  BinaryPrefixFieldTablePlaced.result (tempReady (a := a) s hs) sourceFocus s.W s.startX (s.f*s.q) s.sourceFits
def controlReady (s : Shape) (hs : Fin 8 → List Bool) :=
  SelectedSourceBitsStreamPlaced.result (sourceReady (a := a) s hs) extractFocus (sourceWord s)
    s.q s.rho s.n s.f (2^s.W)
def gathered (s : Shape) (hs : Fin 8 → List Bool) :=
  BinaryVaryingOffsetGatherPlaced.result .selected (controlReady (a := a) s hs) gatherFocus
    s.q s.b s.hb s.hbq (tempWord s) (controlWord s) 0 0 0

def headerWords (hs : Fin 8 → List Bool) : Fin 5 → List Bool := ![hs 0,hs 3,hs 4,hs 5,hs 7]
def tempHeaders (s : Shape) (hs : Fin 8 → List Bool) : Fin 3 → List Bool :=
  ![hs 0,hs 1,RecursiveChildQuotientsConstant.bits (s.n*s.b)]
def sourceHeaders (s : Shape) (hs : Fin 8 → List Bool) : Fin 3 → List Bool :=
  ![hs 0,hs 2,RecursiveChildQuotientsConstant.bits (s.f*s.q)]
def extractHeaders (s : Shape) (hs : Fin 8 → List Bool) : Fin 5 → List Bool :=
  ![hs 3,hs 5,hs 6,hs 7,RecursiveChildQuotientsConstant.bits (2^s.W)]
def gatherHeaders (s : Shape) (hs : Fin 8 → List Bool) : Fin 3 → List Bool :=
  ![hs 3,hs 4,RecursiveChildQuotientsConstant.bits (s.n*2^s.W)]

theorem original_sources (hs : Fin 8 → List Bool) :
    SharedBank.payload (base (a := a) hs) headerFocus=ActivePrefixOffsetHeadersData.sources (headerWords hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem temp_sources (s : Shape) (hs : Fin 8 → List Bool) :
    SharedBank.payload (headers (a := a) s hs) tempFocus=BinaryPrefixFieldTablePlaced.sources (tempHeaders s hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem source_sources (s : Shape) (hs : Fin 8 → List Bool) :
    SharedBank.payload (tempReady (a := a) s hs) sourceFocus=BinaryPrefixFieldTablePlaced.sources (sourceHeaders s hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem extract_sources (s : Shape) (hs : Fin 8 → List Bool) :
    SharedBank.payload (sourceReady (a := a) s hs) extractFocus=
      SelectedSourceBitsStreamPlaced.sources (sourceWord s) (extractHeaders s hs) := by
  have hbinary (bs : List Bool) : RadixZeroFill.encodedBinary (q := a) bs=CountedLoopReuseAlphabet.binary bs :=
    CountedLoopReuseAlphabet.encoding_binary bs
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact hbinary _

theorem gather_tapes (s : Shape) (hs : Fin 8 → List Bool) :
    (∀ i : Fin 3, (controlReady (a := a) s hs).tape (gatherFocus ⟨i.val,by omega⟩)=
      RadixZeroFill.encodedBinary (gatherHeaders s hs i)) ∧
    (controlReady (a := a) s hs).tape (gatherFocus 3)=putWord (fun _ => blank) 0 ((tempWord s).map bitSymbol) ∧
    (controlReady (a := a) s hs).tape (gatherFocus 4)=putWord (fun _ => blank) 0 ((controlWord s).map bitSymbol) := by
  refine ⟨?_,rfl,rfl⟩
  intro i; fin_cases i <;> rfl

theorem gather_heads (s : Shape) (hs : Fin 8 → List Bool) :
    (∀ i : Fin 3, (controlReady (a := a) s hs).head (gatherFocus ⟨i.val,by omega⟩)=1) ∧
    (controlReady (a := a) s hs).head (gatherFocus 3)=0 ∧
    (controlReady (a := a) s hs).head (gatherFocus 4)=0 ∧
    (controlReady (a := a) s hs).head (gatherFocus 5)=0 := by
  refine ⟨?_,rfl,rfl,rfl⟩
  intro i; fin_cases i <;> rfl

def emitted (s : Shape) (hs : Fin 8 → List Bool) :=
  setTape (setTape (setTape (controlReady (a := a) s hs) (gatherFocus 3)
    ((controlReady s hs).tape (gatherFocus 3)) (0+(controlWord s).length*s.b))
    (gatherFocus 4) ((controlReady s hs).tape (gatherFocus 4)) (0+(controlWord s).length))
    (gatherFocus 5) (putWord ((controlReady s hs).tape (gatherFocus 5)) 0 ((offsetWord s).map bitSymbol))
    (0+(controlWord s).length*s.q)

theorem gathered_eq (s : Shape) (hs : Fin 8 → List Bool) : gathered (a := a) s hs=emitted s hs := by
  have hl := BinaryVaryingOffsetGatherPlaced.result_payload .selected (controlReady (a := a) s hs)
    gatherFocus gather_injective s.q s.b s.hb s.hbq (tempWord s) (controlWord s) 0 0 0
  change SharedBank.payload (gathered (a := a) s hs) gatherFocus=_ at hl
  have hr : SharedBank.payload (emitted (a := a) s hs) gatherFocus=
      BinaryVaryingOffsetGatherPlaced.after .selected (SharedBank.payload (controlReady s hs) gatherFocus)
        s.q s.b s.hb s.hbq (tempWord s) (controlWord s) 0 0 0 := by
    unfold emitted
    rw [CompactGadgetReservationPlacement.payload_set _ _ gather_injective,
      CompactGadgetReservationPlacement.payload_set _ _ gather_injective,
      CompactGadgetReservationPlacement.payload_set _ _ gather_injective]
    rfl
  have hsl : SharedBank.strip (gathered (a := a) s hs) gatherFocus=
      SharedBank.strip (controlReady s hs) gatherFocus :=
    (BinaryVaryingOffsetGatherPlaced.installed_frame (controlReady s hs) gatherFocus _).symm
  have hsr : SharedBank.strip (emitted (a := a) s hs) gatherFocus=
      SharedBank.strip (controlReady s hs) gatherFocus := by
    simp only [emitted,CompactGadgetReservationPlacement.strip_set]
  have h : SharedBank.bank (gathered (a := a) s hs) gatherFocus=SharedBank.bank (emitted s hs) gatherFocus := by
    unfold SharedBank.bank
    rw [hl,hr,hsl,hsr]
  simpa only [SharedBank.active_bank] using
    congrArg (Placement.active (SharedBank.placement gatherFocus)) h

end
end IntegerMultBounds.Machine.ActivePrefixSelectedOffsetBank
