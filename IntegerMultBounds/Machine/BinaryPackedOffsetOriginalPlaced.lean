import IntegerMultBounds.Machine.CompactGadgetReservationPlacement

/-! Actual original-header packed action on six arbitrary caller tapes.
The native private bank is appended blank and returned blank. Placement
preserves all caller spectators, including other offset-producer descriptors. -/
namespace IntegerMultBounds.Machine.BinaryPackedOffsetOriginalPlaced
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationPlacement (NativeTapes nativeSlots native_injective native_payload native_clean payload_set strip_set)
open SharedPlacementAlphabet (setTape)
variable {t : ℕ}

def program (focus : Fin 6 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed BinaryPackedOffsetOriginalRun.program
    (CleanSubbank.placement nativeSlots focus hf)

def store (caller : Tapes t prime) (focus : Fin 6 → Fin t)
    {P N G B : ℕ} (x : Fin (RadixRangePadding.volume P N G B) → Bool) :=
  setTape caller (focus 5) (BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i))) 0

theorem projects (caller : Tapes t prime) (focus : Fin 6 → Fin t)
    (hf : Function.Injective focus) {P N G B : ℕ} (x : Fin (RadixRangePadding.volume P N G B) → Bool) :
    SharedBank.payload (store caller focus x) focus =
      BinaryPackedFieldSwap.store (SharedBank.payload caller focus) 5 x :=
  payload_set caller focus hf 5 _ 0

theorem realizes (caller : Tapes t prime) (focus : Fin 6 → Fin t)
    (hf : Function.Injective focus) {P N G B : ℕ} (x y : Fin (RadixRangePadding.volume P N G B) → Bool) (C : ℕ)
    (hr : HoareTime BinaryPackedOffsetOriginalRun.program
      (fun v => v=BinaryPackedOffsetOriginalRun.input
        (BinaryPackedFieldSwap.store (SharedBank.payload caller focus) 5 x))
      (fun v => v=BinaryPackedOffsetOriginalRun.input
        (BinaryPackedFieldSwap.store (SharedBank.payload caller focus) 5 y)) C) :
    HoareTime (program focus hf)
      (fun v => v=CleanSubbank.bank (s := NativeTapes) (store caller focus x))
      (fun v => v=CleanSubbank.bank (s := NativeTapes) (store caller focus y)) C := by
  apply CleanSubbank.realizes _ nativeSlots focus native_injective hf
    (store caller focus x) (store caller focus y) _ _ C
  · rw [native_payload,projects caller focus hf]
  · rw [native_payload,projects caller focus hf]
  · exact native_clean _
  · exact native_clean _
  · rw [store,store,strip_set,strip_set]
  · exact hr

/-- No action contract is supplied: this invokes the proved fixed machine,
including original-header count construction, both swaps, rotation and erasure. -/
theorem runs (caller : Tapes t prime) (focus : Fin 6 → Fin t) (hf : Function.Injective focus)
    (V : List Bool) (P w G B : ℕ) (hV : V.length=BinaryPackedOffsetData.rows P w G*w)
    (hP : 0<P) (hG : 0<G) (hB : 0<B) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=BinaryRadixRangePrepare.values P G B w i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hsrc : BinaryAdjacentWidthHeadersShared.Sources (SharedBank.payload caller focus)
      BinaryPackedOffsetOriginalRun.headers hs)
    (ht : caller.tape (focus 4)=putWord (fun _ => blank) 0 (V.map bitSymbol))
    (hh : caller.head (focus 4)=0)
    (x : Fin (RadixRangePadding.volume P (2^w) G B) → Bool) :
    HoareTime (program focus hf)
      (fun v => v=CleanSubbank.bank (s := NativeTapes) (store caller focus x))
      (fun v => v=CleanSubbank.bank (s := NativeTapes)
        (store caller focus (BinaryPackedOffsetData.result V P w G B x)))
      (BinaryPackedOffsetOriginalRun.cost P w G B hs) := by
  apply realizes caller focus hf x _ _
  apply BinaryPackedOffsetOriginalRun.runs _ V P w G B hV hP hG hB hs hv hc hsrc
    (fun _ => blank) 0 rfl _ hh x
  have he : StreamedFiberTranslationAlphabet.mapTape (a := prime) (fun _ => blank) = (fun _ => blank) := rfl
  rw [he]
  exact ht

end
end IntegerMultBounds.Machine.BinaryPackedOffsetOriginalPlaced
