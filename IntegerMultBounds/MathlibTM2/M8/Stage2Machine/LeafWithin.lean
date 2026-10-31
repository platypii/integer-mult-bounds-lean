module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Leaf
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreWithin
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.LeafCoreWithin

/-! The residual leaf phase consumes the actual stage-1 prefix certificate;
its established array semantics and runtime remain unchanged. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.LeafWithin
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedBankStageInput (raw)
open RevMachine
open Leaf (leafBank)
noncomputable section
variable [M8.Machine.Net]

theorem leaf_phase (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (c : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime)
    (u : Descriptor) (hp : u.Positive) (lo upper : ℤ)
    (hmargin : ∀ X j, lo+(M8.Machine.ArbitraryWidthOriginalTotalRunWithin.coefficient cutoff*volume prime u : ℕ) ≤
      (raw (leafBank f p node scalar c st u X) (LeafCore.core (NodeBank.io rev97m)).tapes).head j ∧
      (raw (leafBank f p node scalar c st u X) (LeafCore.core (NodeBank.io rev97m)).tapes).head j+
        (M8.Machine.ArbitraryWidthOriginalTotalRunWithin.coefficient cutoff*volume prime u : ℕ) ≤ upper) :
    Core.PhaseWithin (LeafCore.core (NodeBank.io rev97m)).program
      (fun u X => raw (leafBank f p node scalar c st u X) (LeafCore.core (NodeBank.io rev97m)).tapes)
      u u (Stage2Wrapper.Moves prime u Prod.swap)
      (M8.Machine.ArbitraryWidthOriginalTotalRun.cost u (Routines.hdr u))
      (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  intro X
  have h := LeafCoreWithin.core_runs_within (u := u) cutoff hcut (FamilyStep.rolesAt u X)
    f p node scalar c st (NodeBank.io rev97m) hp (fun i => X i)
    (by simp [FamilyStep.rolesAt,FamilyRoot.rolesOf,NodePark.childRoles,SharedPlacementAlphabet.setTape])
    (by
      simp only [FamilyStep.rolesAt,FamilyRoot.rolesOf,NodePark.childRoles,
        SharedPlacementAlphabet.setTape,Function.update_self]
      rfl) lo upper (hmargin X)
  apply HoareWithin.of_time_invariant ((Leaf.leaf_phase f p node scalar c st hp) X)
  intro z hz
  exact h.invariant hz

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.LeafWithin
