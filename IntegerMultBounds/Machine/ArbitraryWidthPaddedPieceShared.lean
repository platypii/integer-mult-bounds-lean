import IntegerMultBounds.Machine.ArbitraryWidthPaddedPieceRun

/-! Place the complete physical padding/piece/crop wrapper on a caller's tape. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthPaddedPieceShared
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveRowPadding (withRows)
open SharedPlacementAlphabet (setTape)
open ArbitraryWidthHighExchangeShared (sourceWord)
open ArbitraryWidthConsumePlacement (T)
variable {t : ℕ}

def sourceSlot : Fin ArbitraryWidthPaddedPieceRun.tapeCount := Fin.castAdd T (0 : Fin 12)

def bank (source : ℤ → Fin (prime+4))
    (paddingHeaders : Fin 4 → List Bool) (rootHeaders : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (frame : Tapes 1 prime) :=
  (ArbitraryWidthPaddedPiecePadding.bank source (fun _ => blank) paddingHeaders).append
    (ArbitraryWidthPaddedPiecePlacement.privateBank rootHeaders f p node scalar st frame)

def privateBank (paddingHeaders : Fin 4 → List Bool) (rootHeaders : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (frame : Tapes 1 prime) :=
  bank (fun _ => blank) paddingHeaders rootHeaders f p node scalar st frame

theorem bank_source (source target : ℤ → Fin (prime+4))
    (paddingHeaders : Fin 4 → List Bool) (rootHeaders : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (frame : Tapes 1 prime) :
    setTape (bank source paddingHeaders rootHeaders f p node scalar st frame) sourceSlot target 0 =
      bank target paddingHeaders rootHeaders f p node scalar st frame := by
  unfold bank sourceSlot
  rw [SharedPlacementAlphabet.setTape_append_left]
  apply congrArg (fun w : Tapes 12 prime => w.append
    (ArbitraryWidthPaddedPiecePlacement.privateBank rootHeaders f p node scalar st frame))
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem bank_head_source (source : ℤ → Fin (prime+4))
    (paddingHeaders : Fin 4 → List Bool) (rootHeaders : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (frame : Tapes 1 prime) :
    (bank source paddingHeaders rootHeaders f p node scalar st frame).head sourceSlot = 0 := by
  simp only [bank,sourceSlot,Tapes.append,Fin.addCases_left]
  rfl

theorem bank_tape_source (source : ℤ → Fin (prime+4))
    (paddingHeaders : Fin 4 → List Bool) (rootHeaders : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (frame : Tapes 1 prime) :
    (bank source paddingHeaders rootHeaders f p node scalar st frame).tape sourceSlot = source := by
  simp only [bank,sourceSlot,Tapes.append,Fin.addCases_left]
  rfl

def program (focus : Fin t) := Placement.placed ArbitraryWidthPaddedPieceRun.program
  (SharedPlacementAlphabet.sharedPlacement focus sourceSlot)

/-- Concrete caller-source contract, including physical pad/crop costs and
restoration of the full private bank; only canonical headers and blank-stack
invariants are supplied, never traces of any inner execution. -/
theorem runs (caller : Tapes t prime) (focus : Fin t) (v : Descriptor) (R' k : ℕ)
    (paddingHeaders : Fin 4 → List Bool) (rootHeaders : Fin 6 → List Bool)
    (hp : v.Positive) (hR : v.rows ≤ R')
    (hpadding : ArbitraryWidthPaddedPiecePadding.Headers v R' paddingHeaders)
    (hroot : RecursiveDimensionBank.Headers (withRows v R') rootHeaders)
    (hwidth : v.width < 125000^(k+1)) (hrows : Shared50TapeGlobal.roleCount^k ∣ R')
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Shared50RecursiveCallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free rootHeaders frame)
    (x : Fin (volume prime v) → ZMod 2)
    (hf : caller.tape focus = sourceWord x) (hh : caller.head focus = 0) :
    HoareTime (program focus)
      (fun w => w = caller.append (privateBank paddingHeaders rootHeaders f p node scalar st frame))
      (fun w => w = (setTape caller focus
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) 0).append
        (privateBank paddingHeaders rootHeaders f p node scalar st frame))
      (ArbitraryWidthPaddedPieceRun.cost v R' rootHeaders) := by
  have hrun := ArbitraryWidthPaddedPieceRun.runs v R' k paddingHeaders rootHeaders hp hR
    hpadding hroot hwidth hrows f p node scalar st ready frame hfree x
  change HoareTime _
    (fun w => w = bank (sourceWord x) paddingHeaders rootHeaders f p node scalar st frame)
    (fun w => w = bank (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x))
      paddingHeaders rootHeaders f p node scalar st frame) _ at hrun
  have h := SharedPlacementAlphabet.shared_hoare hrun caller focus sourceSlot (fun _ => blank) 0
    (by simpa only [bank_tape_source] using hf) (by simpa only [bank_head_source] using hh)
  simpa only [program,bank_tape_source,bank_head_source,bank_source,privateBank] using h

end
end IntegerMultBounds.Machine.ArbitraryWidthPaddedPieceShared
