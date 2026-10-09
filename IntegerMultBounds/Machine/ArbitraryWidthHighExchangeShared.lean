import IntegerMultBounds.Machine.ArbitraryWidthHighExchange
import IntegerMultBounds.Machine.SharedPlacementAlphabet

/-! Actual high exchange on a caller's physically shared source tape. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighExchangeShared
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedPlacementAlphabet (setTape)
open ArbitrarySliceCall (rootCount commonCount rootBank data)
variable {t : ℕ}

private theorem common_le : commonCount ≤ rootCount :=
  SharedBankFamily.common_le_tapeCount
    (Shared50RecursiveControl.block Shared50RecursiveImplementation.returnCapacity
      Shared50RecursiveImplementation.width Shared50RecursiveImplementation.pcStack
      (Shared50RecursiveImplementation.implementation Shared50RecursiveImplementation.returnWidth))

def commonSource : Fin commonCount := Fin.castAdd (7+7) Shared50NodeSegments.io
def rootSource : Fin rootCount := Fin.castLE common_le commonSource
def sourceSlot : Fin ArbitraryWidthHighExchange.tapeCount := Fin.castAdd 16 rootSource

def sourceWord {v : Descriptor} (x : Fin (volume prime v) → ZMod 2) :=
  RecursiveShiftRoleBank.source (Shared50RecursiveNodeSemantics.encoded x)

theorem data_eq {v : Descriptor} (x : Fin (volume prime v) → ZMod 2) :
    data x = Shared50RecursiveCallSemantics.childRoles (sourceWord x) :=
  Shared50RecursiveCallReady.source_roles _

theorem data_head_source {v : Descriptor} (x : Fin (volume prime v) → ZMod 2) :
    (data x).head Shared50NodeSegments.io = 0 := by
  simp only [data_eq,Shared50RecursiveCallSemantics.childRoles,setTape,Function.update_self]

theorem data_tape_source {v : Descriptor} (x : Fin (volume prime v) → ZMod 2) :
    (data x).tape Shared50NodeSegments.io = sourceWord x := by
  simp only [data_eq,Shared50RecursiveCallSemantics.childRoles,setTape,Function.update_self]

private theorem raw_setTape {k n a : ℕ} (hk : k ≤ n) (w : Tapes k a) (i : Fin k)
    (out : ℤ → Fin (a+4)) (p : ℤ) :
    SharedBankStageInput.raw (setTape w i out p) n =
      setTape (SharedBankStageInput.raw w n) (Fin.castLE hk i) out p := by
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals by_cases hj : j.val < k
  all_goals by_cases he : j.val = i.val
  all_goals simp [SharedBankStageInput.raw,setTape,Function.update_apply,Fin.ext_iff,hj,he]

theorem rootBank_source (payload : Tapes Shared50NodeSegments.payloadCount prime)
    (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (st : Tapes 2 prime) (out : ℤ → Fin (prime+4)) :
    setTape (rootBank payload hs f p node scalar st) rootSource out 0 =
      rootBank (setTape payload Shared50NodeSegments.io out 0) hs f p node scalar st := by
  unfold rootBank Shared50RecursiveBank.bank
  rw [Shared50RecursiveCallSemantics.bank_setTape]
  exact (raw_setTape common_le _ _ out 0).symm

def bank (source : ℤ → Fin (prime+4)) (hs : Fin 6 → List Bool) (rs : List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) :=
  ArbitraryWidthHighExchange.bank (Shared50RecursiveCallSemantics.childRoles source) hs rs f p node scalar st

def privateBank (hs : Fin 6 → List Bool) (rs : List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) :=
  bank (fun _ => blank) hs rs f p node scalar st

theorem bank_source (source target : ℤ → Fin (prime+4)) (hs : Fin 6 → List Bool) (rs : List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) :
    setTape (bank source hs rs f p node scalar st) sourceSlot target 0 =
      bank target hs rs f p node scalar st := by
  unfold bank ArbitraryWidthHighExchange.bank sourceSlot
  rw [SharedPlacementAlphabet.setTape_append_left,rootBank_source]
  simp only [Shared50RecursiveCallSemantics.childRoles,SharedPlacementAlphabet.setTape_setTape]

theorem cleared_source (source : ℤ → Fin (prime+4)) (hs : Fin 6 → List Bool) (rs : List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) :
    setTape (bank source hs rs f p node scalar st) sourceSlot (fun _ => blank) 0 =
      privateBank hs rs f p node scalar st := bank_source _ _ _ _ _ _ _ _ _

theorem bank_head_source (source : ℤ → Fin (prime+4)) (hs : Fin 6 → List Bool) (rs : List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) :
    (bank source hs rs f p node scalar st).head sourceSlot = 0 := by
  unfold bank ArbitraryWidthHighExchange.bank sourceSlot
  simp only [Tapes.append,Fin.addCases_left]
  unfold rootBank rootSource
  simp only [SharedBankStageInput.raw,Fin.val_castLE,dite_eq_left commonSource.isLt]
  change (RecursiveCallBank.bank (Shared50RecursiveCallSemantics.childRoles source) hs f p
    (node.append (scalar.append (SharedBank.empty 0 prime))) st).head
      (Fin.castAdd (7+7) Shared50NodeSegments.io) = 0
  simp only [RecursiveCallBank.bank,RecursiveShiftRoleBank.common,Tapes.append,Fin.addCases_left,
    Shared50RecursiveCallSemantics.childRoles,setTape,Function.update_self]


theorem bank_tape_source (source : ℤ → Fin (prime+4)) (hs : Fin 6 → List Bool) (rs : List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) :
    (bank source hs rs f p node scalar st).tape sourceSlot = source := by
  unfold bank ArbitraryWidthHighExchange.bank sourceSlot
  simp only [Tapes.append,Fin.addCases_left]
  unfold rootBank rootSource
  simp only [SharedBankStageInput.raw,Fin.val_castLE,dite_eq_left commonSource.isLt]
  change (RecursiveCallBank.bank (Shared50RecursiveCallSemantics.childRoles source) hs f p
    (node.append (scalar.append (SharedBank.empty 0 prime))) st).tape
      (Fin.castAdd (7+7) Shared50NodeSegments.io) = source
  simp only [RecursiveCallBank.bank,RecursiveShiftRoleBank.common,Tapes.append,Fin.addCases_left,
    Shared50RecursiveCallSemantics.childRoles,setTape,Function.update_self]


def program (focus : Fin t) := Placement.placed ArbitraryWidthHighExchange.program
  (SharedPlacementAlphabet.sharedPlacement focus sourceSlot)

theorem realizes_hoare (caller : Tapes t prime) (focus : Fin t)
    (v : Descriptor) (hs : Fin 6 → List Bool) (rs : List Bool) (rho : ℕ)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (hr : Counter.value rs = rho) (cr : GrowingCounterData.Canonical rs) (hfit : rho ≤ v.width)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Shared50RecursiveCallReady.Ready f p node scalar st)
    (x : Fin (volume prime v) → ZMod 2)
    (hf : caller.tape focus = sourceWord x) (hh : caller.head focus = 0) :
    HoareTime (program focus)
      (fun w => w = caller.append (privateBank hs rs f p node scalar st))
      (fun w => w = (setTape caller focus
        (sourceWord (ArbitraryWidthHighExchangeSemantics.array v rho hfit x)) 0).append
        (privateBank hs rs f p node scalar st))
      (ArbitraryWidthHighExchange.coefficient*(rho+1)*volume prime v) := by
  have hrun := ArbitraryWidthHighExchange.realizes_hoare v hs rs rho hp hv hr cr hfit f p node scalar st ready x
  simp only [data_eq] at hrun
  change HoareTime _ (fun w => w = bank (sourceWord x) hs rs f p node scalar st)
    (fun w => w = bank (sourceWord (ArbitraryWidthHighExchangeSemantics.array v rho hfit x)) hs rs f p node scalar st) _ at hrun
  have h := SharedPlacementAlphabet.shared_hoare hrun caller focus sourceSlot (fun _ => blank) 0
    (by simpa only [bank_tape_source] using hf) (by simpa only [bank_head_source] using hh)
  simpa only [program,bank_tape_source,bank_head_source,bank_source,privateBank] using h

end
end IntegerMultBounds.Machine.ArbitraryWidthHighExchangeShared
