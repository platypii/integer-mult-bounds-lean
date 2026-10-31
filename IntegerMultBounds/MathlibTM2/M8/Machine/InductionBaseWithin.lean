module

public import IntegerMultBounds.MathlibTM2.M8.Machine.InductionBase
public import IntegerMultBounds.Machine.RunWithin

/-! The stage-1 depth-zero frame has linear runtime, so the same existing
execution certifies every prefix inside its reserved head margin. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Machine.InductionBase
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Control
open Implementation (implementation widthSlot pcStack)
open BaseExecution (entryConfig)
open Shared50RecursiveBank (bank)
open CallReady (Ready)
open Shared50RecursiveNodeSemantics (encoded)
open Shared50RecursiveNodeRows (transpose)
open NodeLayout (wires)
open RecursiveRoleSerialization (roles)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedBankStageInput (raw)
variable {k : ℕ}

theorem run_within (capacity : Fintype.card PC ≤ 2^k) (target : PC)
    (v : Descriptor) (shape : Depth.Shape 0 v)
    (hs old : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (hold : ∀ i, (old i).length ≤ 2*volume prime v)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Ready f p node scalar st) (x : Fin (volume prime v) → ZMod 2) :
    let initial := raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs f p node scalar
      (SharedBank.empty 0 prime) (RecursiveChildCallSetup.savedStacks old st
        (FiniteReturnStack.address capacity (encoding target))))
      (tapeCount capacity widthSlot pcStack (implementation k))
    ∀ lo hi : ℤ, (∀ j, lo+(Budget.budget k 0 (volume prime v) : ℕ) ≤ initial.head j ∧
      initial.head j+(Budget.budget k 0 (volume prime v) : ℕ) ≤ hi) →
      ∃ n ≤ Budget.budget k 0 (volume prime v),
        RunWithin (Control.program capacity widthSlot pcStack (implementation k))
          (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) n
          (initial.start (Control.program capacity widthSlot pcStack (implementation k)))
          (entryConfig capacity target
            (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded (transpose (one_dvd v.rows) x))))
              old f p node scalar (SharedBank.empty 0 prime) st)) := by
  intro initial lo hi hbank
  obtain ⟨n,hn,hr⟩ := run capacity target v shape hs old hv hold f p node scalar st ready x
  exact ⟨n,hn,RunWithin.heads_of_run_le hr hn lo hi hbank⟩

end
end IntegerMultBounds.MathlibTM2.M8.Machine.InductionBase
