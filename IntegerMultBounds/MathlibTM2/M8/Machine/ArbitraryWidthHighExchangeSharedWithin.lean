module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeShared
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeWithin
public import IntegerMultBounds.Machine.HoareWithinPlacement

/-! The bounded high-prefix exchange runs on the caller's shared source tape,
with every complementary tape retained literally by physical placement. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeSharedWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedPlacementAlphabet (setTape)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceCall (rootCount commonCount rootBank data)
variable {t : ℕ}

open ArbitraryWidthHighExchangeShared

theorem realizes_within (caller : Tapes t prime) (focus : Fin t)
    (v : Descriptor) (hs : Fin 6 → List Bool) (rs : List Bool) (rho : ℕ)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (hr : Counter.value rs = rho) (cr : GrowingCounterData.Canonical rs) (hfit : rho ≤ v.width)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : CallReady.Ready f p node scalar st)
    (x : Fin (volume prime v) → ZMod 2)
    (hf : caller.tape focus = sourceWord x) (hh : caller.head focus = 0)
    (lo hi : ℤ)
    (hmargin : ∀ j, lo+(ArbitraryWidthHighExchangeWithin.coefficient*volume prime v : ℕ) ≤
      (caller.append (privateBank hs rs f p node scalar st)).head j ∧
      (caller.append (privateBank hs rs f p node scalar st)).head j+
        (ArbitraryWidthHighExchangeWithin.coefficient*volume prime v : ℕ) ≤ hi) :
    HoareWithin (program focus)
      (fun w => w = caller.append (privateBank hs rs f p node scalar st))
      (fun w => w = (setTape caller focus
        (sourceWord (ArbitraryWidthHighExchangeSemantics.array v rho hfit x)) 0).append
        (privateBank hs rs f p node scalar st))
      (ArbitraryWidthHighExchange.coefficient*(rho+1)*volume prime v) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  let small := bank (sourceWord x) hs rs f p node scalar st
  let initial := caller.append (privateBank hs rs f p node scalar st)
  let e := SharedPlacementAlphabet.sharedPlacement focus sourceSlot
  have hf' : caller.tape focus = small.tape sourceSlot := hf.trans (bank_tape_source _ _ _ _ _ _ _ _).symm
  have hh' : caller.head focus = small.head sourceSlot := hh.trans (bank_head_source _ _ _ _ _ _ _ _).symm
  have ha : Placement.active e initial = small := by
    change Placement.active (SharedPlacementAlphabet.sharedPlacement focus sourceSlot)
      (caller.append (privateBank hs rs f p node scalar st)) = small
    rw [← cleared_source (sourceWord x) hs rs f p node scalar st,SharedPlacementAlphabet.active_shared,
      hf',hh',SharedPlacementAlphabet.setTape_setTape,SharedPlacementAlphabet.setTape_self]
  have hsmallMargin : ∀ j, lo+(ArbitraryWidthHighExchangeWithin.coefficient*volume prime v : ℕ) ≤ small.head j ∧
      small.head j+(ArbitraryWidthHighExchangeWithin.coefficient*volume prime v : ℕ) ≤ hi := by
    intro j
    have hm := hmargin (e (Fin.castAdd t j))
    change lo+_ ≤ (Placement.active e initial).head j ∧ (Placement.active e initial).head j+_ ≤ hi at hm
    rwa [ha] at hm
  have hrun := ArbitraryWidthHighExchangeWithin.realizes_within v hs rs rho hp hv hr cr hfit
    f p node scalar st ready x lo hi (by simpa only [data_eq,small,ArbitraryWidthHighExchangeShared.bank] using hsmallMargin)
  simp only [data_eq] at hrun
  change HoareWithin _ (· = small)
    (fun w => w = bank (sourceWord (ArbitraryWidthHighExchangeSemantics.array v rho hfit x)) hs rs f p node scalar st)
    _ _ at hrun
  have hplaced := HoareWithin.placed_heads_at hrun e initial ha (by
    intro j
    have hm := hmargin (e (Fin.natAdd ArbitraryWidthHighExchange.tapeCount j))
    change lo ≤ initial.head _ ∧ initial.head _ ≤ hi
    change lo+_ ≤ initial.head _ ∧ initial.head _+_ ≤ hi at hm
    omega)
  apply hplaced.consequence (fun _ h => h) _ le_rfl (fun _ h => h)
  rintro w ⟨y,rfl,rfl⟩
  dsimp only [initial,e]
  rw [SharedPlacementAlphabet.replace_shared]
  simp only [bank_tape_source,bank_head_source,bank_source,privateBank]

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeSharedWithin
