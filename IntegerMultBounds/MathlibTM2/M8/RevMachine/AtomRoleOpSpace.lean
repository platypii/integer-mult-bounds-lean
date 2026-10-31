module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleOp
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleLoopSpace

/-! The three executed atom families share the same stage workspace bound.
Counter readiness is discharged by the same contracts as their time proofs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleOp
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewRoleBank (Selection)
open AtomStep (machine words)
open AtomRoleLoop (levelBank)
open FlatCoordinateSchedule (bits)
variable {t u N b : ℕ}
noncomputable section
variable (f : ℕ) (hb0 : 0 < b) (act : RecursiveViewedAction.Action t) (v : Descriptor)
  (hw : v.width = N*b) (hp : v.Positive) (hs : Fin 6 → List Bool)
  (hv : RecursiveDimensionBank.Headers v hs) (aux : Tapes u prime) (hf : 0 < f)
  (data : RecursiveViewedAction.Data t v)
include hb0 hw hp hv hf

theorem cross_loop_heads (i₀ j₀ : ℕ) (hi : i₀ + (f-1) < N) (hj : j₀ + (f-1) < N)
    (lo hiHead : ℤ)
    (hbank : ∀ i, lo ≤ (levelBank (machine (u := u) (crossFamily f i₀ j₀ hi hj 0) act).tapes hs aux data (words b (crossFamily f i₀ j₀ hi hj 0))).head i ∧ (levelBank (machine (u := u) (crossFamily f i₀ j₀ hi hj 0) act).tapes hs aux data (words b (crossFamily f i₀ j₀ hi hj 0))).head i ≤ hiHead)
    {c} {n : ℕ}
    (hrun : Machine.run (LevelLoop.program (seq (machine (u := u) (crossFamily f i₀ j₀ hi hj 0) act).program
        (AtomRoleSteps.crossSteps _ (tapes_ge (u := u) (crossFamily f i₀ j₀ hi hj 0) act)))
        (machine (u := u) (crossFamily f i₀ j₀ hi hj 0) act).program) n
      ((LevelLoop.bank (levelBank (machine (u := u) (crossFamily f i₀ j₀ hi hj 0) act).tapes hs aux data (words b (crossFamily f i₀ j₀ hi hj 0))) f).start (LevelLoop.program (seq (machine (u := u) (crossFamily f i₀ j₀ hi hj 0) act).program
        (AtomRoleSteps.crossSteps _ (tapes_ge (u := u) (crossFamily f i₀ j₀ hi hj 0) act)))
        (machine (u := u) (crossFamily f i₀ j₀ hi hj 0) act).program)) = some c) :
    ∀ i, min lo 0-(AtomStepCost.constant act * volume prime v + 1 + AtomRoleSteps.stepCost N +
        3*(bits (f-1)).length+8 : ℕ) ≤ c.head i ∧
      c.head i ≤ max hiHead (((bits (f-1)).length : ℤ)+1)+
        (AtomStepCost.constant act * volume prime v + 1 + AtomRoleSteps.stepCost N +
          3*(bits (f-1)).length+8 : ℕ) := by
  exact AtomRoleLoop.loop_heads hb0 _ (crossFamily f i₀ j₀ hi hj) act (fun l => rfl)
    v hw hp hs hv aux f hf _ _
    (fun l hl d => cross_counter_hoare f act v hs aux d i₀ j₀ hi hj l hl)
    data lo hiHead hbank hrun

theorem within_loop_heads (g : RecursiveAffineDimensions.Group) (j₀ i₀ : ℕ) (hji : j₀ < i₀)
    (hi : i₀ + (f-1) < N)
    (lo hiHead : ℤ)
    (hbank : ∀ i, lo ≤ (levelBank (machine (u := u) (withinFamily f g j₀ i₀ hji hi 0) act).tapes hs aux data (words b (withinFamily f g j₀ i₀ hji hi 0))).head i ∧ (levelBank (machine (u := u) (withinFamily f g j₀ i₀ hji hi 0) act).tapes hs aux data (words b (withinFamily f g j₀ i₀ hji hi 0))).head i ≤ hiHead)
    {c} {n : ℕ}
    (hrun : Machine.run (LevelLoop.program (seq (machine (u := u) (withinFamily f g j₀ i₀ hji hi 0) act).program
        (AtomRoleSteps.withinSteps _ (tapes_ge (u := u) (withinFamily f g j₀ i₀ hji hi 0) act)))
        (machine (u := u) (withinFamily f g j₀ i₀ hji hi 0) act).program) n
      ((LevelLoop.bank (levelBank (machine (u := u) (withinFamily f g j₀ i₀ hji hi 0) act).tapes hs aux data (words b (withinFamily f g j₀ i₀ hji hi 0))) f).start (LevelLoop.program (seq (machine (u := u) (withinFamily f g j₀ i₀ hji hi 0) act).program
        (AtomRoleSteps.withinSteps _ (tapes_ge (u := u) (withinFamily f g j₀ i₀ hji hi 0) act)))
        (machine (u := u) (withinFamily f g j₀ i₀ hji hi 0) act).program)) = some c) :
    ∀ i, min lo 0-(AtomStepCost.constant act * volume prime v + 1 + AtomRoleSteps.stepCost N +
        3*(bits (f-1)).length+8 : ℕ) ≤ c.head i ∧
      c.head i ≤ max hiHead (((bits (f-1)).length : ℤ)+1)+
        (AtomStepCost.constant act * volume prime v + 1 + AtomRoleSteps.stepCost N +
          3*(bits (f-1)).length+8 : ℕ) := by
  exact AtomRoleLoop.loop_heads hb0 _ (withinFamily f g j₀ i₀ hji hi) act (fun l => rfl)
    v hw hp hs hv aux f hf _ _
    (fun l hl d => within_counter_hoare f act v hs aux d g j₀ i₀ hji hi l hl)
    data lo hiHead hbank hrun

theorem rev_loop_heads (i₀ j₀ : ℕ) (hi0 : f-1 ≤ i₀) (hi : i₀ < N) (hj : j₀ + (f-1) < N)
    (lo hiHead : ℤ)
    (hbank : ∀ i, lo ≤ (levelBank (machine (u := u) (revFamily f i₀ j₀ hi0 hi hj 0) act).tapes hs aux data (words b (revFamily f i₀ j₀ hi0 hi hj 0))).head i ∧ (levelBank (machine (u := u) (revFamily f i₀ j₀ hi0 hi hj 0) act).tapes hs aux data (words b (revFamily f i₀ j₀ hi0 hi hj 0))).head i ≤ hiHead)
    {c} {n : ℕ}
    (hrun : Machine.run (LevelLoop.program (seq (machine (u := u) (revFamily f i₀ j₀ hi0 hi hj 0) act).program
        (AtomRoleSteps.revSteps _ (tapes_ge (u := u) (revFamily f i₀ j₀ hi0 hi hj 0) act)))
        (machine (u := u) (revFamily f i₀ j₀ hi0 hi hj 0) act).program) n
      ((LevelLoop.bank (levelBank (machine (u := u) (revFamily f i₀ j₀ hi0 hi hj 0) act).tapes hs aux data (words b (revFamily f i₀ j₀ hi0 hi hj 0))) f).start (LevelLoop.program (seq (machine (u := u) (revFamily f i₀ j₀ hi0 hi hj 0) act).program
        (AtomRoleSteps.revSteps _ (tapes_ge (u := u) (revFamily f i₀ j₀ hi0 hi hj 0) act)))
        (machine (u := u) (revFamily f i₀ j₀ hi0 hi hj 0) act).program)) = some c) :
    ∀ i, min lo 0-(AtomStepCost.constant act * volume prime v + 1 + AtomRoleSteps.stepCost N +
        3*(bits (f-1)).length+8 : ℕ) ≤ c.head i ∧
      c.head i ≤ max hiHead (((bits (f-1)).length : ℤ)+1)+
        (AtomStepCost.constant act * volume prime v + 1 + AtomRoleSteps.stepCost N +
          3*(bits (f-1)).length+8 : ℕ) := by
  exact AtomRoleLoop.loop_heads hb0 _ (revFamily f i₀ j₀ hi0 hi hj) act (fun l => rfl)
    v hw hp hs hv aux f hf _ _
    (fun l hl d => rev_counter_hoare f act v hs aux d i₀ j₀ hi0 hi hj l hl)
    data lo hiHead hbank hrun

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleOp
