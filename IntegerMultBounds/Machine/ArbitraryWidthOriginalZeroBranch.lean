import IntegerMultBounds.Machine.ArbitraryWidthHighFramedFallback
import IntegerMultBounds.Machine.Branch
import IntegerMultBounds.Machine.BinaryCanonicalData

/-! The zero-width outer branch runs the actual elementary fallback on the
full blank global workspace. A one-step read of the retained canonical width
header distinguishes zero before positive-width metadata preparation. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthOriginalZeroBranch
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedPlacementAlphabet (setTape)
open ArbitraryWidthHighExchangeShared (sourceWord)
open ArbitraryWidthHighFramedFallback (frameSlot)
open ArbitraryWidthHighCommonFallback (sourceSlot elementaryCount)
variable {t : ℕ}

abbrev highCount (t : ℕ) := (((((t+16)+19)+17)+12)+1)+
  ArbitraryWidthHighExchangeJoin.exchangeCount+ArbitraryWidthHighExchangeJoin.movementCount+
  ArbitraryWidthHighRun.paddingCount
abbrev count (t : ℕ) := highCount t+elementaryCount

def input (caller : Tapes t prime) : Tapes (count t) prime :=
  (ArbitraryWidthHighPreparedRun.input (ArbitraryWidthHighCommonPrepare.input caller)).append
    (FixedHeaderBankCopy.empty elementaryCount)

def headerSlot (headers : Fin 6 → Fin t) (i : Fin 6) : Fin (highCount t) :=
  frameSlot (sourceSlot (headers i))
def widthSlot (headers : Fin 6 → Fin t) : Fin (count t) :=
  Fin.castAdd elementaryCount (headerSlot headers 3)

def test (headers : Fin 6 → Fin t) (symbols : Fin (count t) → Fin (prime+4)) : Bool :=
  decide (symbols (widthSlot headers) = blank)

def zeroProgram (headers : Fin 6 → Fin t) (source : Fin t) :=
  ArbitraryWidthElementaryInitializedRun.program (headerSlot headers) (frameSlot (sourceSlot source))

/-- Fixed finite selection; the positive branch is later instantiated with
the concrete positive-width original run. Selection itself preserves all tapes. -/
def program {states : ℕ} (headers : Fin 6 → Fin t) (source : Fin t)
    (positive : Program (count t) states prime) := branch (test headers) (zeroProgram headers source) positive

theorem descriptor_blank_iff (bs : List Bool) :
    BinaryDescriptorStack.descriptor (a := prime) bs 1 = blank ↔ bs = [] := by
  cases bs with
  | nil => simp [BinaryDescriptorStack.descriptor,putWord,BinaryDescriptorStack.empty]
  | cons b bs => cases b <;> simp [BinaryDescriptorStack.descriptor,putWord,bitSymbol,blank,Fin.ext_iff]

theorem canonical_zero_iff (bs : List Bool) (hc : GrowingCounterData.Canonical bs) :
    BinaryDescriptorStack.descriptor (a := prime) bs 1 = blank ↔ Counter.value bs = 0 := by
  rw [descriptor_blank_iff]
  exact ⟨fun h => by rw [h]; rfl, BinaryCanonicalData.zero_nil bs hc⟩

theorem header_cells (caller : Tapes t prime) (headers : Fin 6 → Fin t) (i : Fin 6) :
    (input caller).head (Fin.castAdd elementaryCount (headerSlot headers i)) = caller.head (headers i) ∧
    (input caller).tape (Fin.castAdd elementaryCount (headerSlot headers i)) = caller.tape (headers i) := by
  have h := ArbitraryWidthHighFramedFallback.frame_cells
    (ArbitraryWidthHighCommonPrepare.input caller) (sourceSlot (headers i))
  simpa only [input,headerSlot,ArbitraryWidthHighCommonPrepare.input,sourceSlot,Tapes.append,Fin.addCases_left] using h

theorem test_true_iff (caller : Tapes t prime) (headers : Fin 6 → Fin t) (bs : List Bool)
    (hc : GrowingCounterData.Canonical bs)
    (ht : caller.tape (headers 3) = RadixZeroFill.encodedBinary bs)
    (hh : caller.head (headers 3) = 1) :
    test headers (input caller).reads = true ↔ Counter.value bs = 0 := by
  unfold test Tapes.reads widthSlot
  rw [(header_cells caller headers 3).1,(header_cells caller headers 3).2,ht,hh]
  rw [← BinaryDescriptorStackRoundtrip.descriptor_encoded]
  simp only [decide_eq_true_eq]
  exact canonical_zero_iff bs hc

theorem test_false_iff (caller : Tapes t prime) (headers : Fin 6 → Fin t) (bs : List Bool)
    (hc : GrowingCounterData.Canonical bs)
    (ht : caller.tape (headers 3) = RadixZeroFill.encodedBinary bs)
    (hh : caller.head (headers 3) = 1) :
    test headers (input caller).reads = false ↔ 0 < Counter.value bs := by
  simp only [Bool.eq_false_iff,ne_eq,test_true_iff caller headers bs hc ht hh]
  omega

theorem zero_hoare (caller : Tapes t prime) (headers : Fin 6 → Fin t) (source : Fin t)
    (d : Descriptor) (hs : Fin 6 → List Bool) (hp : d.Positive) (hw : d.width = 0)
    (hv : RecursiveDimensionBank.Headers d hs)
    (ht : ∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (headers i) = 1)
    (x : Fin (volume prime d) → ZMod 2)
    (hf : caller.tape source = sourceWord x) (hhead : caller.head source = 0) :
    HoareTime (zeroProgram headers source) (fun w => w = input caller)
      (fun w => w = input (setTape caller source
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0))
      ((ArbitraryWidthElementary.coefficient+116)*volume prime d) := by
  let base := ArbitraryWidthHighCommonPrepare.input caller
  have h := ArbitraryWidthElementaryInitializedRun.bounded_hoare 0
    (ArbitraryWidthHighPreparedRun.input base) (headerSlot headers) (frameSlot (sourceSlot source)) d hs hp hv (by omega)
    (by
      intro i
      unfold headerSlot
      rw [(ArbitraryWidthHighFramedFallback.frame_cells base (sourceSlot (headers i))).2]
      simpa only [base,ArbitraryWidthHighCommonPrepare.input,sourceSlot,Tapes.append,Fin.addCases_left] using ht i)
    (by
      intro i
      unfold headerSlot
      rw [(ArbitraryWidthHighFramedFallback.frame_cells base (sourceSlot (headers i))).1]
      simpa only [base,ArbitraryWidthHighCommonPrepare.input,sourceSlot,Tapes.append,Fin.addCases_left] using hh i)
    x (by
      rw [(ArbitraryWidthHighFramedFallback.frame_cells base (sourceSlot source)).2]
      simpa only [base,ArbitraryWidthHighCommonPrepare.input,sourceSlot,Tapes.append,Fin.addCases_left] using hf)
    (by
      rw [(ArbitraryWidthHighFramedFallback.frame_cells base (sourceSlot source)).1]
      simpa only [base,ArbitraryWidthHighCommonPrepare.input,sourceSlot,Tapes.append,Fin.addCases_left] using hhead)
  rw [ArbitraryWidthHighFramedFallback.changed_input] at h
  have hout : setTape base (sourceSlot source)
      (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0 =
      ArbitraryWidthHighCommonPrepare.input (setTape caller source
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0) := by
    dsimp only [base]
    unfold ArbitraryWidthHighCommonPrepare.input sourceSlot
    rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left]
  rw [hout] at h
  simpa only [zeroProgram,input,base,Nat.zero_add,Nat.mul_one] using h

end
end IntegerMultBounds.Machine.ArbitraryWidthOriginalZeroBranch
