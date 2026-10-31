module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.FamilyLeafWithin
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.LeafCoreWithin

/-! The actual original-header execution supplies the generic leaf core's
uniform prefix-space predicate on all equal-volume views. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.LeafCoreWithin
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open SharedBankStageInput (raw)
open RecursiveInterchangeLayout (Descriptor volume)
open CommonBank (bank)
open Routines (hdr)
open LeafCore
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
noncomputable section
variable [M8.Machine.Net] {T : ℕ}

theorem core_space (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n)
    (io : Fin T) (Good : Descriptor → Tapes T prime → Prop)
    (hgood : ∀ v roles, Good v roles → LeafCore.Good io v roles) :
    Family.CoreSpace (core io) Good (M8.Machine.ArbitraryWidthOriginalTotalRunWithin.coefficient cutoff) := by
  intro v u hu hvol roles f p node scalar c st hg lo hi hm z hz
  obtain ⟨_,hhead,x,hx⟩ := hgood v roles hg
  let y : Fin (volume prime u) → ZMod 2 := fun i => x (Fin.cast hvol i)
  have hy : roles.tape io = sourceWord y := hx.trans (sourceWord_cast hvol x).symm
  have h := core_runs_within (u := u) cutoff hcut roles f p node scalar c st io hu y hhead hy lo hi (by
    rw [hvol]
    exact hm _)
  exact h.invariant hz

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.LeafCoreWithin
