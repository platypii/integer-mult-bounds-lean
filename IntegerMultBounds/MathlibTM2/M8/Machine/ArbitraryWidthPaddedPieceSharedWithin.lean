module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPieceRunWithin
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPieceShared
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPiecePadding
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPiecePlacement
public import IntegerMultBounds.MathlibTM2.M8.Machine.CallReady

/-! Place the complete physical padding/piece/crop wrapper on a caller's tape. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPieceSharedWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveRowPadding (withRows)
open SharedPlacementAlphabet (setTape)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthConsumePlacement (T)
variable {t : ℕ}

open ArbitraryWidthPaddedPieceShared

theorem runs_within (caller : Tapes t prime) (focus : Fin t) (v : Descriptor) (R' k : ℕ)
    (paddingHeaders : Fin 4 → List Bool) (rootHeaders : Fin 6 → List Bool)
    (hp : v.Positive) (hR : v.rows ≤ R')
    (hpadding : ArbitraryWidthPaddedPiecePadding.Headers v R' paddingHeaders)
    (hroot : RecursiveDimensionBank.Headers (withRows v R') rootHeaders)
    (hwidth : v.width < Machine.width^(k+1)) (hrows : roleCount^k ∣ R')
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : CallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free rootHeaders frame)
    (x : Fin (volume prime v) → ZMod 2)
    (hf : caller.tape focus = sourceWord x) (hh : caller.head focus = 0) (lo hi : ℤ)
    (hmargin : ∀ j, lo+(ArbitraryWidthPaddedPieceRunWithin.coefficient*volume prime (withRows v R') : ℕ) ≤
      (caller.append (privateBank paddingHeaders rootHeaders f p node scalar st frame)).head j ∧
      (caller.append (privateBank paddingHeaders rootHeaders f p node scalar st frame)).head j+
        (ArbitraryWidthPaddedPieceRunWithin.coefficient*volume prime (withRows v R') : ℕ) ≤ hi) :
    HoareWithin (program focus)
      (fun w => w = caller.append (privateBank paddingHeaders rootHeaders f p node scalar st frame))
      (fun w => w = (setTape caller focus
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) 0).append
        (privateBank paddingHeaders rootHeaders f p node scalar st frame))
      (ArbitraryWidthPaddedPieceRun.cost v R' rootHeaders) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  let small := bank (sourceWord x) paddingHeaders rootHeaders f p node scalar st frame
  have hf' : caller.tape focus = small.tape sourceSlot := hf.trans (bank_tape_source _ _ _ _ _ _ _ _ _).symm
  have hh' : caller.head focus = small.head sourceSlot := hh.trans (bank_head_source _ _ _ _ _ _ _ _ _).symm
  have hsmall := SharedPlacementAlphabet.shared_margin caller focus sourceSlot (fun _ => blank) 0 hf' hh'
    (by simpa only [small,bank_source,privateBank] using hmargin)
  have hrun := ArbitraryWidthPaddedPieceRunWithin.runs_within v R' k paddingHeaders rootHeaders hp hR
    hpadding hroot hwidth hrows f p node scalar st ready frame hfree x lo hi hsmall
  change HoareWithin _ (· = small)
    (fun w => w = bank (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x))
      paddingHeaders rootHeaders f p node scalar st frame) _ _ at hrun
  have hframe : ∀ j, lo ≤ (caller.append (privateBank paddingHeaders rootHeaders f p node scalar st frame)).head j ∧
      (caller.append (privateBank paddingHeaders rootHeaders f p node scalar st frame)).head j ≤ hi := by
    intro j
    have hm := hmargin j
    omega
  have h := SharedPlacementAlphabet.shared_within hrun caller focus sourceSlot (fun _ => blank) 0 hf' hh'
    (by simpa only [small,bank_source,privateBank] using hframe)
  simpa only [small,program,bank_tape_source,bank_head_source,bank_source,privateBank] using h

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPieceSharedWithin
