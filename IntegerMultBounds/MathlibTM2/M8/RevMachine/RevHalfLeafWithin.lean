module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.FamilyLeafCoreWithin
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Rev97Node

/-! Concrete reversed-family leaves use the actual bounded original-header
core, including offset setup, saved views, restoration and counter advance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevNode
open IntegerMultBounds.Machine
open NodePark (childRoles)
open NodeBank (io)
noncomputable section
variable (N : RevNetwork)

theorem Good.to_leafCore {v roles} (h : Good N v roles) : LeafCore.Good (io N) v roles := by
  obtain ⟨hp,x,rfl⟩ := h
  refine ⟨hp,?_,x,?_⟩
  · simp [childRoles,SharedPlacementAlphabet.setTape]
  · simp only [childRoles,SharedPlacementAlphabet.setTape,Function.update_self]
    rfl

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevNode

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
open IntegerMultBounds.Machine Networks
open Networks.Shared50ModularControl (prime)
open Family (Frame)
open NodeBank (tapes io)
open SharedBankStageInput (raw)
noncomputable section
variable [M8.Machine.Net] (N : RevNetwork) {k : ℕ}
  {capacity : Fintype.card (Graph.PC (pcs N).length) ≤ 2^k}

def leafSpaceConstant (cutoff : ℕ) : ℕ :=
  Family.leafSpaceConstant (M8.Machine.ArbitraryWidthOriginalTotalRunWithin.coefficient cutoff)

theorem leaf_heads_within (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n)
    (σ : Frame (pcs N) capacity) (i : ℕ) (hi : i < σ.n % N.width)
    (y : Tapes (CommonBank.count (tapes N)) prime)
    (hy : ∃ roles, RevNode.Good N σ.v roles ∧ y = σ.at roles
      (Family.leafC σ.b N.width σ.n (σ.n % N.width-i))) (lo upper : ℤ)
    (hmargin : ∀ n j, lo+(leafSpaceConstant cutoff*RecursiveInterchangeLayout.volume prime σ.v : ℕ) ≤
      (raw y n).head j ∧ (raw y n).head j+
        (leafSpaceConstant cutoff*RecursiveInterchangeLayout.volume prime σ.v : ℕ) ≤ upper)
    {z} (hz : RunInvariant (Family.leaf (LeafCore.core (io N))).program
      (· = raw y (Family.leaf (LeafCore.core (io N))).tapes) z) :
    ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper := by
  obtain ⟨roles,hg,rfl⟩ := hy
  have hspace := LeafCoreWithin.core_space cutoff hcut (io N) (RevNode.Good N)
    (fun _ _ h => RevNode.Good.to_leafCore N h)
  obtain ⟨roles',hg',h⟩ := Family.leaf_runs_within (m := N.width) (r := σ.n % N.width-i) (Rev97Node.leafCore N) hspace
    σ.hpos σ.hb σ.hw (by omega) (by have := Nat.mod_le σ.n N.width; omega) σ.hfree hg lo upper
    (by simpa only [Family.Frame.at,leafSpaceConstant] using hmargin)
  exact h.invariant hz

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
