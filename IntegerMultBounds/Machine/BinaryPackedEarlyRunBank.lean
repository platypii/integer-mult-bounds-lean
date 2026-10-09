import IntegerMultBounds.Machine.BinaryPackedEarlyCorrect
import IntegerMultBounds.Machine.BinarySelectedOffsetLoad
import IntegerMultBounds.Machine.BinaryCorrectionOffsetLoad
import IntegerMultBounds.Machine.BinaryPackedEarlyPrefixParityLoad
import IntegerMultBounds.Machine.BinaryPackedEarlyPrefixNegativeLoad

/-! One retained eighteen-tape bank for the four early actions. Temp/control
shape headers, original q/b/n/controls and paid repetition descriptors survive.
All four child machines share one blank private bank and one erased offset tape. -/
namespace IntegerMultBounds.Machine.BinaryPackedEarlyRunBank
noncomputable section
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
open CompactGadgetReservationPlacement (NativeTapes)

abbrev Work := 55+NativeTapes

def binary (xs : List Bool) := CountedLoopReuseAlphabet.binary (a := prime) xs
/-- `hs` stores q,b,n,rows,gap-prefix,gap-suffix,prefix-repeat. -/
def bank (st sc : Fin 4 → List Bool) (hs : Fin 7 → List Bool) (Z : List Bool) : Tapes 18 prime :=
  ⟨![1,1,1,1,1,1,1,1,0,0,1,1,1,0,1,1,1,1],
   ![binary (st 0),binary (st 1),binary (st 2),binary (st 3),
     binary (sc 0),binary (sc 1),binary (sc 2),binary (sc 3),
     (fun _ => blank),(fun _ => blank),binary (hs 0),binary (hs 1),binary (hs 2),
     BinaryAddressOffsetRepeatAlphabet.word Z,binary (hs 3),binary (hs 4),binary (hs 5),binary (hs 6)]⟩
def store {m : ℕ} (caller : Tapes 18 prime) (x : Fin m → Bool) :=
  setTape caller 8 (BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i))) 0

def gapPorts : Fin 13 → Fin 18 := ![0,1,2,3,9,8,11,10,12,14,15,16,13]
def prefixPorts : Fin 12 → Fin 18 := ![4,5,6,7,9,8,10,11,12,17,14,13]
theorem gap_injective : Function.Injective gapPorts := by decide
theorem prefix_injective : Function.Injective prefixPorts := by decide

def gapNative (i : Fin 13) : Fin Work := Fin.castAdd NativeTapes (Fin.castAdd 42 i)
def prefixNative (i : Fin 12) : Fin Work := Fin.castAdd NativeTapes (Fin.castAdd 43 i)
theorem gap_native_injective : Function.Injective gapNative := by
  intro i j h; exact Fin.castAdd_injective _ _ (Fin.castAdd_injective _ _ h)
theorem prefix_native_injective : Function.Injective prefixNative := by
  intro i j h; exact Fin.castAdd_injective _ _ (Fin.castAdd_injective _ _ h)

def gapCaller (caller : Tapes 18 prime) := SharedBank.payload caller gapPorts
def prefixCaller (caller : Tapes 18 prime) := SharedBank.payload caller prefixPorts

def gapHeaders (hs : Fin 7 → List Bool) : Fin 6 → List Bool := ![hs 1,hs 0,hs 2,hs 3,hs 4,hs 5]
def prefixHeaders (hs : Fin 7 → List Bool) : Fin 5 → List Bool := ![hs 0,hs 1,hs 2,hs 6,hs 3]
def input (caller : Tapes 18 prime) := CleanSubbank.bank (s := Work) caller

theorem gap_payload (caller : Tapes 13 prime) :
    SharedBank.payload (BinarySelectedOffsetLoad.input caller) gapNative=caller :=
  SharedBankFrames.payload_common _ _ _
theorem prefix_payload (caller : Tapes 12 prime) :
    SharedBank.payload (BinaryPackedEarlyPrefixParityLoad.input caller) prefixNative=caller :=
  SharedBankFrames.payload_common _ _ _
theorem gap_clean (caller : Tapes 13 prime) :
    SharedBank.strip (BinarySelectedOffsetLoad.input caller) gapNative=SharedBank.empty Work prime :=
  SharedBankFrames.strip_common_blank caller 42 NativeTapes
theorem prefix_clean (caller : Tapes 12 prime) :
    SharedBank.strip (BinaryPackedEarlyPrefixParityLoad.input caller) prefixNative=SharedBank.empty Work prime :=
  SharedBankFrames.strip_common_blank caller 43 NativeTapes

theorem word_cast {m n : ℕ} (h : n=m) (x : Fin m → Bool) :
    BinaryRadixRangePrepareAlphabet.word (a := prime) (fun i : Fin n => bitSymbol (x (Fin.cast h i)))=
      BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)) := by
  apply congrArg (putWord (fun _ => blank) 0)
  exact BinaryPackedOffsetData.word_cast h.symm x

theorem gap_store {m P N G B : ℕ} (h : RadixRangePadding.volume P N G B=m)
    (caller : Tapes 18 prime) (x : Fin m → Bool) :
    BinaryPackedOffsetOriginalPlaced.store (gapCaller caller) BinarySelectedOffsetLoad.base (fun i => x (Fin.cast h i))=
      gapCaller (store caller x) := by
  have he := CompactGadgetReservationPlacement.payload_set caller gapPorts gap_injective (5 : Fin 13)
    (BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i))) 0
  rw [show gapPorts 5=(8 : Fin 18) from rfl] at he
  simp only [gapCaller,store]
  rw [he]
  change setTape _ (5 : Fin 13) _ 0=_
  rw [word_cast h x]

theorem prefix_store {m P N G B : ℕ} (h : RadixRangePadding.volume P N G B=m)
    (caller : Tapes 18 prime) (x : Fin m → Bool) :
    BinaryPackedOffsetOriginalPlaced.store (prefixCaller caller) BinaryPackedEarlyPrefixParityLoad.base (fun i => x (Fin.cast h i))=
      prefixCaller (store caller x) := by
  have he := CompactGadgetReservationPlacement.payload_set caller prefixPorts prefix_injective (5 : Fin 12)
    (BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i))) 0
  rw [show prefixPorts 5=(8 : Fin 18) from rfl] at he
  simp only [prefixCaller,store]
  rw [he]
  change setTape _ (5 : Fin 12) _ 0=_
  rw [word_cast h x]

theorem gap_frame {m n : ℕ} (caller : Tapes 18 prime) (x : Fin m → Bool) (y : Fin n → Bool) :
    SharedBank.strip (store caller x) gapPorts=SharedBank.strip (store caller y) gapPorts := by
  change SharedBank.strip (setTape caller (gapPorts 5) _ 0) gapPorts=SharedBank.strip (setTape caller (gapPorts 5) _ 0) gapPorts
  rw [CompactGadgetReservationPlacement.strip_set,CompactGadgetReservationPlacement.strip_set]
theorem prefix_frame {m n : ℕ} (caller : Tapes 18 prime) (x : Fin m → Bool) (y : Fin n → Bool) :
    SharedBank.strip (store caller x) prefixPorts=SharedBank.strip (store caller y) prefixPorts := by
  change SharedBank.strip (setTape caller (prefixPorts 5) _ 0) prefixPorts=SharedBank.strip (setTape caller (prefixPorts 5) _ 0) prefixPorts
  rw [CompactGadgetReservationPlacement.strip_set,CompactGadgetReservationPlacement.strip_set]

 theorem gap_lift {m P N G B states : ℕ} (hsize : RadixRangePadding.volume P N G B=m)
    (M : Program Work states prime) (caller : Tapes 18 prime) (x y : Fin m → Bool) (C : ℕ)
    (h : HoareTime M
      (fun z => z=BinarySelectedOffsetLoad.input (BinaryPackedOffsetOriginalPlaced.store (gapCaller caller)
        BinarySelectedOffsetLoad.base (fun i => x (Fin.cast hsize i))))
      (fun z => z=BinarySelectedOffsetLoad.input (BinaryPackedOffsetOriginalPlaced.store (gapCaller caller)
        BinarySelectedOffsetLoad.base (fun i => y (Fin.cast hsize i)))) C) :
    HoareTime (Placement.placed M (CleanSubbank.placement gapNative gapPorts gap_injective))
      (fun z => z=input (store caller x)) (fun z => z=input (store caller y)) C := by
  refine CleanSubbank.realizes M gapNative gapPorts gap_native_injective gap_injective
    (store caller x) (store caller y) _ _ C ?_ ?_ ?_ ?_ ?_ h
  · rw [gap_payload,gap_store]; rfl
  · rw [gap_payload,gap_store]; rfl
  · exact gap_clean _
  · exact gap_clean _
  · exact gap_frame caller x y

 theorem prefix_lift {m P N G B states : ℕ} (hsize : RadixRangePadding.volume P N G B=m)
    (M : Program Work states prime) (caller : Tapes 18 prime) (x y : Fin m → Bool) (C : ℕ)
    (h : HoareTime M
      (fun z => z=BinaryPackedEarlyPrefixParityLoad.input (BinaryPackedOffsetOriginalPlaced.store (prefixCaller caller)
        BinaryPackedEarlyPrefixParityLoad.base (fun i => x (Fin.cast hsize i))))
      (fun z => z=BinaryPackedEarlyPrefixParityLoad.input (BinaryPackedOffsetOriginalPlaced.store (prefixCaller caller)
        BinaryPackedEarlyPrefixParityLoad.base (fun i => y (Fin.cast hsize i)))) C) :
    HoareTime (Placement.placed M (CleanSubbank.placement prefixNative prefixPorts prefix_injective))
      (fun z => z=input (store caller x)) (fun z => z=input (store caller y)) C := by
  refine CleanSubbank.realizes M prefixNative prefixPorts prefix_native_injective prefix_injective
    (store caller x) (store caller y) _ _ C ?_ ?_ ?_ ?_ ?_ h
  · rw [prefix_payload,prefix_store]; rfl
  · rw [prefix_payload,prefix_store]; rfl
  · exact prefix_clean _
  · exact prefix_clean _
  · exact prefix_frame caller x y

end
end IntegerMultBounds.Machine.BinaryPackedEarlyRunBank
