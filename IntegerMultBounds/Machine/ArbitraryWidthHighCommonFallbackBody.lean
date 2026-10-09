import IntegerMultBounds.Machine.ArbitraryWidthHighCommonFallback

/-! Actual fallback after common metadata preparation, preserving that metadata
for the selector's shared cleanup. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighCommonFallbackBody
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedPlacementAlphabet (setTape)
open ArbitraryWidthHighExchangeShared (sourceWord)
open ArbitraryWidthHighCommonFallback (elementaryCount sourceSlot)
variable {t : ℕ}

def program (source : Fin t) := ArbitraryWidthElementaryInitializedRun.program
  (ArbitraryWidthHighCommonPrepare.originalSlot (t := t)) (sourceSlot source)

def bank (caller : Tapes t prime) (d : Descriptor) (hs : Fin 6 → List Bool) :=
  (ArbitraryWidthHighCommonPrepare.output caller d hs prime).append
    (FixedHeaderBankCopy.empty elementaryCount)

def cost (d : Descriptor) :=
  60*volume prime d+ArbitraryWidthElementary.coefficient*(d.width+1)*volume prime d+54*volume prime d+2

theorem realizes_hoare (caller : Tapes t prime) (source : Fin t)
    (d : Descriptor) (hs : Fin 6 → List Bool) (hp : d.Positive)
    (hv : RecursiveDimensionBank.Headers d hs)
    (x : Fin (volume prime d) → ZMod 2)
    (hf : caller.tape source = sourceWord x) (hhead : caller.head source = 0) :
    HoareTime (program source) (fun w => w = bank caller d hs)
      (fun w => w = bank (setTape caller source
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0) d hs) (cost d) := by
  have h := ArbitraryWidthElementaryInitializedRun.realizes_hoare
    (ArbitraryWidthHighCommonPrepare.output caller d hs prime)
    (ArbitraryWidthHighCommonPrepare.originalSlot (t := t)) (sourceSlot source) d hs hp hv
    (by intro i; exact (ArbitraryWidthHighCommonPrepare.original_view caller d hs prime i).2)
    (by intro i; exact (ArbitraryWidthHighCommonPrepare.original_view caller d hs prime i).1)
    x (by simpa only [ArbitraryWidthHighCommonPrepare.output,sourceSlot,Tapes.append,Fin.addCases_left] using hf)
    (by simpa only [ArbitraryWidthHighCommonPrepare.output,sourceSlot,Tapes.append,Fin.addCases_left] using hhead)
  have hout : setTape (ArbitraryWidthHighCommonPrepare.output caller d hs prime)
      (sourceSlot source) (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0 =
      ArbitraryWidthHighCommonPrepare.output (setTape caller source
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0) d hs prime := by
    unfold ArbitraryWidthHighCommonPrepare.output sourceSlot
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
  unfold cost
  nlinarith

end
end IntegerMultBounds.Machine.ArbitraryWidthHighCommonFallbackBody
