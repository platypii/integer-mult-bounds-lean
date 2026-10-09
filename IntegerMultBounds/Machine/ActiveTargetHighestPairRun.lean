import IntegerMultBounds.Machine.ActiveTargetHighestPairData

/-! Actual highest-bit machines for either source order, preserving all ten
numeric words and returning every private tape blank. Arbitrary outer row
counts are repeated physically rather than padded to a power of two. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestPairRun
noncomputable section
open ActiveTargetHighestPairData
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
abbrev swapCount := BinaryRadixEqualShared.count
def count := 11+swapCount+65
def middleBank (v : Tapes 11 prime) := CleanSubbank.bank (s := swapCount) v
def bank (v : Tapes 11 prime) := CleanSubbank.bank (s := 65) (middleBank v)
def lifted (i : Fin 9) : Fin (11+swapCount) := Fin.castAdd swapCount (loadFocus i)
theorem lifted_injective : Function.Injective lifted := (Fin.castAdd_injective _ _).comp load_injective

def swapProgram := extend (BinaryPackedFieldSwap.program swapFocus (10 : Fin 11)) 65
def loadProgram (m : ActivePrefixDirtyControlLoadProducer.Mode) :=
  ActivePrefixDirtyControlLoadPlaced.program (a := prime) m lifted lifted_injective
def programFor (m : ActivePrefixDirtyControlLoadProducer.Mode) := seq swapProgram (seq (loadProgram m) swapProgram)
def earlierProgram := loadProgram .pure
def laterProgram := programFor .pure

def swapCost (g : Geometry) (hs : Fin 10 → List Bool) :=
  BinaryRadixEqualShared.cost (P g) (gap g) (suffix g) 1 (swapHeaders hs)
def earlierCost (g : Geometry) := ActivePrefixDirtyControlLoad.constant*volume g
def laterCost (g : Geometry) (hs : Fin 10 → List Bool) := 2*swapCost g hs+earlierCost g+2

theorem bank_raw (v : Tapes 11 prime) : bank v=SharedBankStageInput.raw v count := by
  change (CleanSubbank.bank (s := swapCount) v).append (SharedBank.empty 65 prime)=_
  rw [SharedBankRawCompose.bank_eq_raw,SharedBankFamily.raw_append v (by omega)]
  rfl

theorem middle_set {m n : ℕ} (hs : Fin 10 → List Bool) (x : Fin m → Bool) (y : Fin n → Bool) :
    setTape (middleBank (caller hs x)) (lifted 8) (ActiveTargetRotation.word y) 0=middleBank (caller hs y) := by
  change setTape ((caller hs x).append (SharedBank.empty swapCount prime))
    (Fin.castAdd swapCount (10 : Fin 11)) _ 0=_
  rw [SharedPlacementAlphabet.setTape_append_left,caller_set]
  rfl

theorem swaps (g : Geometry) (hs : Fin 10 → List Bool) (x : Array g)
    (hv : ∀ i,Counter.value (hs i)=values g i) (hc : ∀ i,GrowingCounterData.Canonical (hs i)) :
    HoareTime swapProgram (fun v => v=bank (caller hs x))
      (fun v => v=bank (caller hs (RadixRangePadding.transpose x))) (swapCost g hs) := by
  have h := BinaryPackedFieldSwap.swaps (caller hs x) swapFocus 10
    (P g) (gap g) (suffix g) 1 (swapHeaders hs) (swap_values g hs hv)
    (by intro i; fin_cases i <;> exact hc _)
    (by have := g.positiveRows; unfold P; positivity) (by unfold gap; positivity)
    (by have := g.positivePayload; unfold suffix; positivity) swap_ne (swap_sources hs x) x
  have he (y : Array g) : BinaryPackedFieldSwap.store (caller hs x) 10 y=caller hs y := caller_set hs x y
  rw [he x,he (RadixRangePadding.transpose x)] at h
  exact hoare_extend_eq h (SharedBank.empty 65 prime)

theorem earlier_runs (g : Geometry) (hs : Fin 10 → List Bool) (x : Array g)
    (hv : ∀ i,Counter.value (hs i)=values g i) (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (habs : W g+6≤2*suffix g) :
    HoareTime earlierProgram (fun v => v=bank (caller hs x))
      (fun v => v=bank (caller hs (result g x))) (earlierCost g) := by
  have hsrc : SharedBank.payload (middleBank (caller hs x)) lifted=
      ActivePrefixDirtyControlLoadPlaced.sources (m := .pure) (loadShape g) g.rows (suffix g)
        (loadHeaders hs) (hs 6) (hs 7) (view (load_volume g) x) := by
    change SharedBank.payload ((caller hs x).append (SharedBank.empty swapCount prime))
      (fun i => Fin.castAdd swapCount (loadFocus i))=_
    rw [SharedBankFrames.payload_append_left,load_sources]
  have h := ActivePrefixDirtyControlLoadPlaced.runs (middleBank (caller hs x)) lifted lifted_injective
    (m := .pure) (loadShape g) g.rows (suffix g) g.positiveRows
    (by have := g.positivePayload; unfold suffix; positivity)
    (by change W g+1*2+2+1+1≤2^(1*1)*suffix g; omega)
    (loadHeaders hs) (hs 6) (hs 7) (view (load_volume g) x) hsrc (load_values g hs hv)
    (fun i => hc (Fin.castAdd 4 i)) (hv 6) (hc 6) (hv 7) (hc 7)
  have he : ActivePrefixDirtyControlLoadPlaced.result (m := .pure) (middleBank (caller hs x)) lifted
      (loadShape g) g.rows (suffix g) (view (load_volume g) x)=middleBank (caller hs (result g x)) := by
    unfold ActivePrefixDirtyControlLoadPlaced.result
    rw [middle_set]
    exact congrArg middleBank (caller_view (load_volume g).symm hs _).symm
  rw [he,←load_volume] at h
  exact h

theorem sandwich_runs (m : ActivePrefixDirtyControlLoadProducer.Mode) (g : Geometry) (hs : Fin 10 → List Bool)
    (hv : ∀ i,Counter.value (hs i)=values g i) (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (f : Array g → Array g)
    (hm : ∀ x,HoareTime (loadProgram m) (fun v => v=bank (caller hs x))
      (fun v => v=bank (caller hs (f x))) (earlierCost g)) (x : Array g) :
    HoareTime (programFor m) (fun v => v=bank (caller hs x))
      (fun v => v=bank (caller hs (RadixRangePadding.transpose (f (RadixRangePadding.transpose x)))))
      (laterCost g hs) := by
  exact ((swaps g hs x hv hc).seq ((hm _).seq (swaps g hs _ hv hc))).consequence
    (fun _ h => h) (fun _ h => h) (by unfold laterCost; omega)

theorem later_runs (g : Geometry) (hs : Fin 10 → List Bool) (x : Array g)
    (hv : ∀ i,Counter.value (hs i)=values g i) (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (habs : W g+6≤2*suffix g) :
    HoareTime laterProgram (fun v => v=bank (caller hs x))
      (fun v => v=bank (caller hs (later g x))) (laterCost g hs) := by
  exact sandwich_runs .pure g hs hv hc (result g) (fun x => earlier_runs g hs x hv hc habs) x

end
end IntegerMultBounds.Machine.ActiveTargetHighestPairRun
