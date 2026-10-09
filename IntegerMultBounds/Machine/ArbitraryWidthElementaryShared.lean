import IntegerMultBounds.Machine.ArbitraryWidthElementary
import IntegerMultBounds.Machine.ArbitraryWidthHighExchangeShared

/-! The actual bounded-width fallback shares the caller's source tape. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthElementaryShared
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedPlacementAlphabet (setTape)
open ArbitraryWidthHighExchangeShared (sourceWord rootSource sourceSlot)
variable {t : ℕ}

def bank (source : ℤ → Fin (prime+4)) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) :=
  ArbitraryWidthElementary.input (Shared50RecursiveCallSemantics.childRoles source) hs f p node scalar st

def privateBank (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (st : Tapes 2 prime) := bank (fun _ => blank) hs f p node scalar st

theorem bank_source (source target : ℤ → Fin (prime+4)) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) :
    setTape (bank source hs f p node scalar st) sourceSlot target 0 =
      bank target hs f p node scalar st := by
  unfold bank ArbitraryWidthElementary.input sourceSlot
  rw [SharedPlacementAlphabet.setTape_append_left,ArbitraryWidthHighExchangeShared.rootBank_source]
  simp only [Shared50RecursiveCallSemantics.childRoles,SharedPlacementAlphabet.setTape_setTape]

theorem bank_head_source (source : ℤ → Fin (prime+4)) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) :
    (bank source hs f p node scalar st).head sourceSlot = 0 := by
  have h := ArbitraryWidthHighExchangeShared.bank_head_source source hs [] f p node scalar st
  simpa only [bank,ArbitraryWidthElementary.input,ArbitraryWidthHighExchangeShared.bank,
    ArbitraryWidthHighExchange.bank,sourceSlot,Tapes.append,Fin.addCases_left] using h

theorem bank_tape_source (source : ℤ → Fin (prime+4)) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) :
    (bank source hs f p node scalar st).tape sourceSlot = source := by
  have h := ArbitraryWidthHighExchangeShared.bank_tape_source source hs [] f p node scalar st
  simpa only [bank,ArbitraryWidthElementary.input,ArbitraryWidthHighExchangeShared.bank,
    ArbitraryWidthHighExchange.bank,sourceSlot,Tapes.append,Fin.addCases_left] using h

def program (focus : Fin t) := Placement.placed ArbitraryWidthElementary.program
  (SharedPlacementAlphabet.sharedPlacement focus sourceSlot)

theorem realizes_hoare (caller : Tapes t prime) (focus : Fin t)
    (v : Descriptor) (hs : Fin 6 → List Bool)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Shared50RecursiveCallReady.Ready f p node scalar st)
    (x : Fin (volume prime v) → ZMod 2)
    (hf : caller.tape focus = sourceWord x) (hh : caller.head focus = 0) :
    HoareTime (program focus)
      (fun w => w = caller.append (privateBank hs f p node scalar st))
      (fun w => w = (setTape caller focus
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) 0).append
        (privateBank hs f p node scalar st))
      (ArbitraryWidthElementary.coefficient*(v.width+1)*volume prime v) := by
  have hrun := ArbitraryWidthElementary.realizes_hoare v hs hp hv f p node scalar st ready x
  simp only [ArbitraryWidthHighExchangeShared.data_eq] at hrun
  change HoareTime _ (fun w => w = bank (sourceWord x) hs f p node scalar st)
    (fun w => w = bank (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) hs f p node scalar st) _ at hrun
  have h := SharedPlacementAlphabet.shared_hoare hrun caller focus sourceSlot (fun _ => blank) 0
    (by simpa only [bank_tape_source] using hf) (by simpa only [bank_head_source] using hh)
  simpa only [program,bank_tape_source,bank_head_source,bank_source,privateBank] using h

theorem bounded_hoare (cutoff : ℕ) (caller : Tapes t prime) (focus : Fin t)
    (v : Descriptor) (hs : Fin 6 → List Bool)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs) (hw : v.width ≤ cutoff)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Shared50RecursiveCallReady.Ready f p node scalar st)
    (x : Fin (volume prime v) → ZMod 2)
    (hf : caller.tape focus = sourceWord x) (hh : caller.head focus = 0) :
    HoareTime (program focus)
      (fun w => w = caller.append (privateBank hs f p node scalar st))
      (fun w => w = (setTape caller focus
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) 0).append
        (privateBank hs f p node scalar st))
      (ArbitraryWidthElementary.coefficient*(cutoff+1)*volume prime v) :=
  (realizes_hoare caller focus v hs hp hv f p node scalar st ready x hf hh).consequence
    (fun _ h => h) (fun _ h => h)
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right hw 1)))

theorem bounded_budget (cutoff e V : ℕ) (τ : ℝ) (he : 0 < e) (hτ : 0 < τ) :
    ((ArbitraryWidthElementary.coefficient*(cutoff+1)*V : ℕ) : ℝ) ≤
      ((ArbitraryWidthElementary.coefficient*(cutoff+1) : ℕ) : ℝ)*(V : ℝ)*(e : ℝ)^τ :=
  ArbitraryWidthElementary.bounded_budget cutoff e V τ he hτ

end
end IntegerMultBounds.Machine.ArbitraryWidthElementaryShared
