import IntegerMultBounds.Machine.ArbitraryWidthHighCommonPrepare
import IntegerMultBounds.Machine.ArbitraryWidthElementaryInitializedRun

/-! Complete actual fallback from original headers and blank private banks,
including common metadata generation and reverse cleanup. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighCommonFallback
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedPlacementAlphabet (setTape)
open ArbitraryWidthHighExchangeShared (sourceWord)
variable {t : ℕ}

abbrev elementaryCount := ArbitraryWidthElementary.tapeCount

def sourceSlot (source : Fin t) : Fin ((t+16)+19) := Fin.castAdd 19 (Fin.castAdd 16 source)

def program (headers : Fin 6 → Fin t) (source : Fin t) := seq
  (seq (extend (ArbitraryWidthHighCommonPrepare.program (a := prime) headers prime) elementaryCount)
    (ArbitraryWidthElementaryInitializedRun.program
      (ArbitraryWidthHighCommonPrepare.originalSlot (t := t)) (sourceSlot source)))
  (extend (ArbitraryWidthHighCommonPrepare.cleanup (a := prime) headers) elementaryCount)

def input (caller : Tapes t prime) :=
  (ArbitraryWidthHighCommonPrepare.input caller).append (FixedHeaderBankCopy.empty elementaryCount)

def cost (d : Descriptor) := ArbitraryWidthHighCommonPrepare.setupCost prime d+
  (60*volume prime d+ArbitraryWidthElementary.coefficient*(d.width+1)*volume prime d+54*volume prime d+2)+
  ArbitraryWidthHighCommonPrepare.cleanupCost prime d+2

theorem realizes_hoare (caller : Tapes t prime) (headers : Fin 6 → Fin t) (source : Fin t)
    (d : Descriptor) (hs : Fin 6 → List Bool) (hp : d.Positive) (he : 0 < d.width)
    (hv : RecursiveDimensionBank.Headers d hs)
    (ht : ∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (headers i) = 1)
    (x : Fin (volume prime d) → ZMod 2)
    (hf : caller.tape source = sourceWord x) (hhead : caller.head source = 0) :
    HoareTime (program headers source) (fun w => w = input caller)
      (fun w => w = input (setTape caller source
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0)) (cost d) := by
  let y := Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x
  let final := setTape caller source (sourceWord y) 0
  have hi := hoare_extend_eq
    (ArbitraryWidthHighCommonPrepare.constructs headers caller prime d hs
      Shared50ModularControl.prime_prime.two_le hp he hv ht hh)
    (FixedHeaderBankCopy.empty elementaryCount)
  have hm := ArbitraryWidthElementaryInitializedRun.realizes_hoare
    (ArbitraryWidthHighCommonPrepare.output caller d hs prime)
    (ArbitraryWidthHighCommonPrepare.originalSlot (t := t)) (sourceSlot source) d hs hp hv
    (by intro i; exact (ArbitraryWidthHighCommonPrepare.original_view caller d hs prime i).2)
    (by intro i; exact (ArbitraryWidthHighCommonPrepare.original_view caller d hs prime i).1)
    x (by simpa only [ArbitraryWidthHighCommonPrepare.output,sourceSlot,Tapes.append,Fin.addCases_left] using hf)
    (by simpa only [ArbitraryWidthHighCommonPrepare.output,sourceSlot,Tapes.append,Fin.addCases_left] using hhead)
  have hout : setTape (ArbitraryWidthHighCommonPrepare.output caller d hs prime)
      (sourceSlot source) (sourceWord y) 0 = ArbitraryWidthHighCommonPrepare.output final d hs prime := by
    unfold ArbitraryWidthHighCommonPrepare.output sourceSlot
    rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left]
  change HoareTime _ _ (fun w => w =
    (setTape (ArbitraryWidthHighCommonPrepare.output caller d hs prime) (sourceSlot source) (sourceWord y) 0).append
      (FixedHeaderBankCopy.empty elementaryCount)) _ at hm
  rw [hout] at hm
  have hn : headers 3 ≠ source := by
    intro h
    have h1 := hh 3
    rw [h,hhead] at h1
    omega
  have hft : final.tape (headers 3) = RadixZeroFill.encodedBinary (hs 3) := by
    simpa only [final,setTape,Function.update_of_ne hn] using ht 3
  have hfh : final.head (headers 3) = 1 := by
    simpa only [final,setTape,Function.update_of_ne hn] using hh 3
  have hc := hoare_extend_eq
    (ArbitraryWidthHighCommonPrepare.cleans headers final prime d hs
      Shared50ModularControl.prime_prime.two_le hp hv hft hfh)
    (FixedHeaderBankCopy.empty elementaryCount)
  exact ((hi.seq hm).seq hc).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

def coefficient (cutoff : ℕ) := ArbitraryWidthHighCommonPrepare.setupCoefficient prime cutoff+
  ArbitraryWidthHighCommonPrepare.cleanupCoefficient prime cutoff+
  ArbitraryWidthElementary.coefficient*(cutoff+1)+118

theorem cost_bounded (cutoff : ℕ) (d : Descriptor) (hp : d.Positive) (hw : d.width ≤ cutoff)
    (hcut : ∀ n, cutoff ≤ n → ArbitraryWidthHighPrepare.highDepth prime n ≤ n) :
    cost d ≤ coefficient cutoff*volume prime d := by
  have hi := ArbitraryWidthHighCommonPrepare.setup_budget prime cutoff d
    Shared50ModularControl.prime_prime.two_le hp hcut
  have hc := ArbitraryWidthHighCommonPrepare.cleanup_budget prime cutoff d
    Shared50ModularControl.prime_prime.two_le hp hcut
  have hm := Nat.mul_le_mul_right (volume prime d)
    (Nat.mul_le_mul_left ArbitraryWidthElementary.coefficient (Nat.add_le_add_right hw 1))
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le d hp
  unfold cost coefficient
  nlinarith

theorem bounded_hoare (cutoff : ℕ) (caller : Tapes t prime) (headers : Fin 6 → Fin t) (source : Fin t)
    (d : Descriptor) (hs : Fin 6 → List Bool) (hp : d.Positive) (he : 0 < d.width)
    (hv : RecursiveDimensionBank.Headers d hs) (hw : d.width ≤ cutoff)
    (hcut : ∀ n, cutoff ≤ n → ArbitraryWidthHighPrepare.highDepth prime n ≤ n)
    (ht : ∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (headers i) = 1)
    (x : Fin (volume prime d) → ZMod 2)
    (hf : caller.tape source = sourceWord x) (hhead : caller.head source = 0) :
    HoareTime (program headers source) (fun w => w = input caller)
      (fun w => w = input (setTape caller source
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0))
      (coefficient cutoff*volume prime d) :=
  (realizes_hoare caller headers source d hs hp he hv ht hh x hf hhead).consequence
    (fun _ h => h) (fun _ h => h) (cost_bounded cutoff d hp hw hcut)

/-- Width zero bypasses the positive-width high metadata constructor. The
actual elementary run leaves both unused metadata banks literally blank. -/
def zeroProgram (headers : Fin 6 → Fin t) (source : Fin t) :=
  ArbitraryWidthElementaryInitializedRun.program (fun i => sourceSlot (headers i)) (sourceSlot source)

theorem zero_width_hoare (caller : Tapes t prime) (headers : Fin 6 → Fin t) (source : Fin t)
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
  have h := ArbitraryWidthElementaryInitializedRun.bounded_hoare 0
    (ArbitraryWidthHighCommonPrepare.input caller)
    (fun i => sourceSlot (headers i)) (sourceSlot source) d hs hp hv (by omega)
    (by intro i; simpa only [ArbitraryWidthHighCommonPrepare.input,sourceSlot,Tapes.append,Fin.addCases_left] using ht i)
    (by intro i; simpa only [ArbitraryWidthHighCommonPrepare.input,sourceSlot,Tapes.append,Fin.addCases_left] using hh i)
    x (by simpa only [ArbitraryWidthHighCommonPrepare.input,sourceSlot,Tapes.append,Fin.addCases_left] using hf)
    (by simpa only [ArbitraryWidthHighCommonPrepare.input,sourceSlot,Tapes.append,Fin.addCases_left] using hhead)
  have hout : setTape (ArbitraryWidthHighCommonPrepare.input caller) (sourceSlot source)
      (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0 =
      ArbitraryWidthHighCommonPrepare.input (setTape caller source
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0) := by
    unfold ArbitraryWidthHighCommonPrepare.input sourceSlot
    rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left]
  rw [hout] at h
  simpa only [zeroProgram,input,Nat.zero_add,Nat.mul_one] using h

end
end IntegerMultBounds.Machine.ArbitraryWidthHighCommonFallback
