module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPiecePlacement
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceRunWithin
public import IntegerMultBounds.Machine.SharedPlacementWithin

/-! The complete bounded piece dispatcher runs on one physically shared
payload tape, retaining the caller frame and restoring its whole private bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPiecePlacementWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedPlacementAlphabet (setTape)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthConsumePlacement (S T)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeShared (rootSource sourceWord)
variable {t : ℕ}

open ArbitraryWidthPaddedPiecePlacement

theorem runs_within (caller : Tapes t prime) (focus : Fin t)
    (v : Descriptor) (hs : Fin 6 → List Bool) (k : ℕ)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (hwidth : v.width < Machine.width^(k+1)) (hrows : roleCount^k ∣ v.rows)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : CallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free hs frame)
    (x : Fin (volume prime v) → ZMod 2)
    (hf : caller.tape focus = sourceWord x) (hh : caller.head focus = 0)
    (lo hi : ℤ)
    (hmargin : ∀ j, lo+(ArbitraryWidthPieceRunWithin.coefficient*volume prime v : ℕ) ≤
      (caller.append (privateBank hs f p node scalar st frame)).head j ∧
      (caller.append (privateBank hs f p node scalar st frame)).head j+
        (ArbitraryWidthPieceRunWithin.coefficient*volume prime v : ℕ) ≤ hi) :
    HoareWithin (program focus)
      (fun w => w = caller.append (privateBank hs f p node scalar st frame))
      (fun w => w = (setTape caller focus
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) 0).append
        (privateBank hs f p node scalar st frame)) (ArbitraryWidthPieceRun.cost v hs) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  let small := bank (sourceWord x) hs f p node scalar st frame
  have hf' : caller.tape focus = small.tape sourceSlot := hf.trans (bank_tape_source _ _ _ _ _ _ _ _).symm
  have hh' : caller.head focus = small.head sourceSlot := hh.trans (bank_head_source _ _ _ _ _ _ _ _).symm
  have hsmall := SharedPlacementAlphabet.shared_margin caller focus sourceSlot (fun _ => blank) 0 hf' hh'
    (by simpa only [small,bank_source,privateBank] using hmargin)
  have hrun := ArbitraryWidthPieceRunWithin.runs_within v hs k hp hv hwidth hrows f p node scalar st ready frame hfree x lo hi
    (by simpa only [small,bank,ArbitraryWidthHighExchangeShared.data_eq] using hsmall)
  simp only [ArbitraryWidthHighExchangeShared.data_eq] at hrun
  change HoareWithin _ (· = small)
    (fun w => w = bank (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x))
      hs f p node scalar st frame) _ _ at hrun
  have hframe : ∀ j, lo ≤ (caller.append (privateBank hs f p node scalar st frame)).head j ∧
      (caller.append (privateBank hs f p node scalar st frame)).head j ≤ hi := by
    intro j
    have hm := hmargin j
    omega
  have h := SharedPlacementAlphabet.shared_within hrun caller focus sourceSlot (fun _ => blank) 0 hf' hh'
    (by simpa only [small,bank_source,privateBank] using hframe)
  simpa only [small,program,bank_tape_source,bank_head_source,bank_source,privateBank] using h

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPiecePlacementWithin
