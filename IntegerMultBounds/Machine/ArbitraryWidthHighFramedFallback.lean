import IntegerMultBounds.Machine.ArbitraryWidthHighPreparedRun
import IntegerMultBounds.Machine.ArbitraryWidthHighCommonFallbackBody

/-! The actual fallback runs within the same blank high execution banks as
its fast sibling, preserving every high bank for the common selector. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighFramedFallback
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedPlacementAlphabet (setTape)
open ArbitraryWidthHighExchangeShared (sourceWord)
open ArbitraryWidthHighExchangeJoin (exchangeCount movementCount)
open ArbitraryWidthHighRun (paddingCount)
variable {t : ℕ}

def frameSlot (focus : Fin t) := Fin.castAdd paddingCount
  (Fin.castAdd movementCount (Fin.castAdd exchangeCount (ArbitraryWidthHighRuntimeHeaderWiring.baseSlot focus)))

theorem frame_cells (base : Tapes t prime) (focus : Fin t) :
    (ArbitraryWidthHighPreparedRun.input base).head (frameSlot focus) = base.head focus ∧
    (ArbitraryWidthHighPreparedRun.input base).tape (frameSlot focus) = base.tape focus := by
  simp only [ArbitraryWidthHighPreparedRun.input,ArbitraryWidthHighExecutionInitialize.input,
    ArbitraryWidthHighBranchPrepare.input,frameSlot,ArbitraryWidthHighRuntimeHeaderWiring.baseSlot,
    Tapes.append,Fin.addCases_left]
  trivial

theorem changed_input (base : Tapes t prime) (focus : Fin t)
    (word : ℤ → Fin (prime+4)) :
    setTape (ArbitraryWidthHighPreparedRun.input base) (frameSlot focus) word 0 =
      ArbitraryWidthHighPreparedRun.input (setTape base focus word 0) := by
  unfold ArbitraryWidthHighPreparedRun.input ArbitraryWidthHighExecutionInitialize.input
    ArbitraryWidthHighBranchPrepare.input frameSlot ArbitraryWidthHighRuntimeHeaderWiring.baseSlot
  repeat rw [SharedPlacementAlphabet.setTape_append_left]

def program (source : Fin t) := ArbitraryWidthElementaryInitializedRun.program
  (fun i => frameSlot (ArbitraryWidthHighCommonPrepare.originalSlot (t := t) i))
  (frameSlot (ArbitraryWidthHighCommonFallback.sourceSlot source))

def bank (caller : Tapes t prime) (d : Descriptor) (hs : Fin 6 → List Bool) :=
  (ArbitraryWidthHighPreparedRun.input (ArbitraryWidthHighCommonPrepare.output caller d hs prime)).append
    (FixedHeaderBankCopy.empty ArbitraryWidthElementary.tapeCount)

theorem realizes_hoare (caller : Tapes t prime) (source : Fin t)
    (d : Descriptor) (hs : Fin 6 → List Bool) (hp : d.Positive)
    (hv : RecursiveDimensionBank.Headers d hs)
    (x : Fin (volume prime d) → ZMod 2)
    (hf : caller.tape source = sourceWord x) (hhead : caller.head source = 0) :
    HoareTime (program source) (fun w => w = bank caller d hs)
      (fun w => w = bank (setTape caller source
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0) d hs)
      (ArbitraryWidthHighCommonFallbackBody.cost d) := by
  let prepared := ArbitraryWidthHighCommonPrepare.output caller d hs prime
  let src := ArbitraryWidthHighCommonFallback.sourceSlot source
  have h := ArbitraryWidthElementaryInitializedRun.realizes_hoare
    (ArbitraryWidthHighPreparedRun.input prepared)
    (fun i => frameSlot (ArbitraryWidthHighCommonPrepare.originalSlot (t := t) i)) (frameSlot src) d hs hp hv
    (by intro i; exact ((frame_cells prepared _).2).trans ((ArbitraryWidthHighCommonPrepare.original_view caller d hs prime i).2))
    (by intro i; exact ((frame_cells prepared _).1).trans ((ArbitraryWidthHighCommonPrepare.original_view caller d hs prime i).1))
    x (by
      rw [(frame_cells prepared src).2]
      simpa only [prepared,src,ArbitraryWidthHighCommonPrepare.output,ArbitraryWidthHighCommonFallback.sourceSlot,
        Tapes.append,Fin.addCases_left] using hf)
    (by
      rw [(frame_cells prepared src).1]
      simpa only [prepared,src,ArbitraryWidthHighCommonPrepare.output,ArbitraryWidthHighCommonFallback.sourceSlot,
        Tapes.append,Fin.addCases_left] using hhead)
  rw [changed_input] at h
  have hout : setTape prepared src (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0 =
      ArbitraryWidthHighCommonPrepare.output (setTape caller source
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0) d hs prime := by
    dsimp only [prepared,src]
    unfold ArbitraryWidthHighCommonPrepare.output ArbitraryWidthHighCommonFallback.sourceSlot
    rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left]
  rw [hout] at h
  exact h

theorem bounded_hoare (cutoff : ℕ) (caller : Tapes t prime) (source : Fin t)
    (d : Descriptor) (hs : Fin 6 → List Bool) (hp : d.Positive)
    (hv : RecursiveDimensionBank.Headers d hs) (hw : d.width ≤ cutoff)
    (x : Fin (volume prime d) → ZMod 2)
    (hf : caller.tape source = sourceWord x) (hhead : caller.head source = 0) :
    HoareTime (program source) (fun w => w = bank caller d hs)
      (fun w => w = bank (setTape caller source
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0) d hs)
      ((ArbitraryWidthElementary.coefficient*(cutoff+1)+116)*volume prime d) := by
  apply (realizes_hoare caller source d hs hp hv x hf hhead).consequence
    (fun _ h => h) (fun _ h => h)
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le d hp
  have hm := Nat.mul_le_mul_right (volume prime d)
    (Nat.mul_le_mul_left ArbitraryWidthElementary.coefficient (Nat.add_le_add_right hw 1))
  unfold ArbitraryWidthHighCommonFallbackBody.cost
  nlinarith

end
end IntegerMultBounds.Machine.ArbitraryWidthHighFramedFallback
