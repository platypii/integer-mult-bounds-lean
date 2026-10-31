module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleRun
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleOpSpace

/-! One workspace contract for every kind of executed atom family. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleRun
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open FlatCoordinateSchedule (bits)
open AtomRoleLoop (levelBank)
open AtomRolePlan (Kind)
open AtomStep (words)
noncomputable section
variable {t f N : ℕ}

theorem kloop_heads {b : ℕ} (hb0 : 0 < b) (K : Kind f N) (act : RecursiveViewedAction.Action t)
    (v : Descriptor) (hw : v.width = N*b) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (aux : Tapes 2 prime) (hf : 0 < f)
    (data : RecursiveViewedAction.Data t v) (lo hi : ℤ)
    (hbank : ∀ i, lo ≤ (levelBank (ftapes (kform K) act) hs aux data (words b (K.sel 0))).head i ∧
      (levelBank (ftapes (kform K) act) hs aux data (words b (K.sel 0))).head i ≤ hi)
    {c} (hc : RunInvariant (fprogram (kform K) act).2
      (· = LevelLoop.bank (levelBank (ftapes (kform K) act) hs aux data (words b (K.sel 0))) f) c) :
    ∀ i, min lo 0-(AtomStepCost.constant act * volume prime v + 1 + AtomRoleSteps.stepCost N +
        3*(bits (f-1)).length+8 : ℕ) ≤ c.head i ∧
      c.head i ≤ max hi (((bits (f-1)).length : ℤ)+1)+
        (AtomStepCost.constant act * volume prime v + 1 + AtomRoleSteps.stepCost N +
          3*(bits (f-1)).length+8 : ℕ) := by
  obtain ⟨z,hz,n,hrun⟩ := hc
  subst z
  cases K with
  | cross i₀ j₀ hi₀ hj =>
    exact AtomRoleOp.cross_loop_heads f hb0 act v hw hp hs hv aux hf data i₀ j₀ hi₀ hj lo hi hbank hrun
  | within g j₀ i₀ hji hi₀ =>
    exact AtomRoleOp.within_loop_heads f hb0 act v hw hp hs hv aux hf data g j₀ i₀ hji hi₀ lo hi hbank hrun
  | rev i₀ j₀ hi0 hi₀ hj =>
    exact AtomRoleOp.rev_loop_heads f hb0 act v hw hp hs hv aux hf data i₀ j₀ hi0 hi₀ hj lo hi hbank hrun

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleRun
