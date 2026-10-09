import IntegerMultBounds.Machine.ArbitraryWidthPieceRun
import IntegerMultBounds.Machine.ArbitraryWidthHighExchangeShared

/-! The actual piece dispatcher on one physically shared payload tape. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthPaddedPiecePlacement
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedPlacementAlphabet (setTape)
open ArbitraryWidthConsumePlacement (S T)
open ArbitraryWidthHighExchangeShared (rootSource sourceWord)
variable {t : ℕ}

def sourceSlot : Fin T := Fin.natAdd 14 (Fin.castAdd 6 (Fin.castAdd 12 rootSource))

def bank (source : ℤ → Fin (prime+4)) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (frame : Tapes 1 prime) :=
  ArbitraryWidthPieceSetup.input (ArbitraryWidthPieceSetup.bare
    (ArbitrarySliceCall.rootBank (Shared50RecursiveCallSemantics.childRoles source)
      hs f p node scalar st) frame)

def privateBank (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (st : Tapes 2 prime) (frame : Tapes 1 prime) :=
  bank (fun _ => blank) hs f p node scalar st frame

private theorem setTape_append_right {l r a : ℕ} (v : Tapes l a) (w : Tapes r a)
    (i : Fin r) (f : ℤ → Fin (a+4)) (p : ℤ) :
    setTape (v.append w) (Fin.natAdd l i) f p = v.append (setTape w i f p) := by
  unfold setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases with
  | left j =>
    simp [Function.update_apply,Fin.ext_iff]
    intro h; have hj := j.isLt; omega
  | right j => simp [Function.update_apply,Fin.ext_iff]

theorem bank_source (source target : ℤ → Fin (prime+4)) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (frame : Tapes 1 prime) :
    setTape (bank source hs f p node scalar st frame) sourceSlot target 0 =
      bank target hs f p node scalar st frame := by
  unfold bank ArbitraryWidthPieceSetup.input ArbitraryWidthPieceSetup.bare sourceSlot
  rw [setTape_append_right,SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_left,ArbitraryWidthHighExchangeShared.rootBank_source]
  simp only [Shared50RecursiveCallSemantics.childRoles,SharedPlacementAlphabet.setTape_setTape]

theorem bank_head_source (source : ℤ → Fin (prime+4)) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (frame : Tapes 1 prime) : (bank source hs f p node scalar st frame).head sourceSlot = 0 := by
  unfold bank ArbitraryWidthPieceSetup.input ArbitraryWidthPieceSetup.bare sourceSlot
  simp only [Tapes.append,Fin.addCases_right,Fin.addCases_left]
  simpa only [ArbitraryWidthHighExchangeShared.bank,ArbitraryWidthHighExchange.bank,
    ArbitraryWidthHighExchangeShared.sourceSlot,Tapes.append,Fin.addCases_left] using
    ArbitraryWidthHighExchangeShared.bank_head_source source hs [] f p node scalar st

theorem bank_tape_source (source : ℤ → Fin (prime+4)) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (frame : Tapes 1 prime) : (bank source hs f p node scalar st frame).tape sourceSlot = source := by
  unfold bank ArbitraryWidthPieceSetup.input ArbitraryWidthPieceSetup.bare sourceSlot
  simp only [Tapes.append,Fin.addCases_right,Fin.addCases_left]
  simpa only [ArbitraryWidthHighExchangeShared.bank,ArbitraryWidthHighExchange.bank,
    ArbitraryWidthHighExchangeShared.sourceSlot,Tapes.append,Fin.addCases_left] using
    ArbitraryWidthHighExchangeShared.bank_tape_source source hs [] f p node scalar st

def program (focus : Fin t) := Placement.placed ArbitraryWidthPieceRun.program
  (SharedPlacementAlphabet.sharedPlacement focus sourceSlot)

theorem runs (caller : Tapes t prime) (focus : Fin t)
    (v : Descriptor) (hs : Fin 6 → List Bool) (k : ℕ)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (hwidth : v.width < 125000^(k+1)) (hrows : Shared50TapeGlobal.roleCount^k ∣ v.rows)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Shared50RecursiveCallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free hs frame)
    (x : Fin (volume prime v) → ZMod 2)
    (hf : caller.tape focus = sourceWord x) (hh : caller.head focus = 0) :
    HoareTime (program focus)
      (fun w => w = caller.append (privateBank hs f p node scalar st frame))
      (fun w => w = (setTape caller focus
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) 0).append
        (privateBank hs f p node scalar st frame)) (ArbitraryWidthPieceRun.cost v hs) := by
  have hrun := ArbitraryWidthPieceRun.runs v hs k hp hv hwidth hrows f p node scalar st ready frame hfree x
  simp only [ArbitraryWidthHighExchangeShared.data_eq] at hrun
  change HoareTime _ (fun w => w = bank (sourceWord x) hs f p node scalar st frame)
    (fun w => w = bank (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x))
      hs f p node scalar st frame) _ at hrun
  have h := SharedPlacementAlphabet.shared_hoare hrun caller focus sourceSlot (fun _ => blank) 0
    (by simpa only [bank_tape_source] using hf) (by simpa only [bank_head_source] using hh)
  simpa only [program,bank_tape_source,bank_head_source,bank_source,privateBank] using h

end
end IntegerMultBounds.Machine.ArbitraryWidthPaddedPiecePlacement
