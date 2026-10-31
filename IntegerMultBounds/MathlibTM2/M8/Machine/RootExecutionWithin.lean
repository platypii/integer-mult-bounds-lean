module

public import IntegerMultBounds.MathlibTM2.M8.Machine.InductionWithin
public import IntegerMultBounds.MathlibTM2.M8.Machine.Root
public import IntegerMultBounds.Machine.RunWithinComposition

/-! The actual root setup and recursive power-width transpose share one
linear-volume workspace reserve. A halting witness covers every actual prefix. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.RootExecutionWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Control
open Implementation (implementation widthSlot pcStack returnWidth returnCapacity)
open BaseExecution (entryConfig)
open Shared50RecursiveBank (bank)
open CallReady (Ready)
open Shared50RecursiveNodeSemantics (encoded)
open Shared50RecursiveNodeRows (transpose)
open NodeLayout (wires)
open RecursiveRoleSerialization (roles)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedBankStageInput (raw)
variable {k depth : ℕ}

/-- Root setup is linear; the recursive coefficient is independent of depth. -/
def coefficient : ℕ := 74+returnWidth+InductionWithin.coefficient returnWidth

def budget (depth V : ℕ) : ℕ :=
  (74+returnWidth)*V+Budget.budget returnWidth depth V

theorem run_within (v : Descriptor) (shape : Depth.Shape depth v)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Ready f p node scalar st) (x : Fin (volume prime v) → ZMod 2)
    (lo hi : ℤ)
    (hmargin : ∀ j, lo+(coefficient*volume prime v : ℕ) ≤
      (raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs f p node scalar
        (SharedBank.empty 0 prime) st) Root.tapeCount).head j ∧
      (raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs f p node scalar
        (SharedBank.empty 0 prime) st) Root.tapeCount).head j+(coefficient*volume prime v : ℕ) ≤ hi) :
    ∃ n ≤ budget depth (volume prime v), ∃ c,
      RunWithin Implementation.program (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) n
        ((raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs f p node scalar
          (SharedBank.empty 0 prime) st) Root.tapeCount).start Implementation.program) c ∧
      step Implementation.program c = none ∧
      c.tapes = raw (bank (roles (RecursiveRowsSerialization.sourceData wires
        (encoded (transpose (one_dvd v.rows) x)))) hs f p node scalar (SharedBank.empty 0 prime) st)
        Root.tapeCount := by
  let before := raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs f p node scalar
    (SharedBank.empty 0 prime) st) Root.tapeCount
  obtain ⟨ns,z,hns,hrs,hh,hpost⟩ := Root.setup_hoare
    (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs f p node scalar st before rfl
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v shape.positive
  have hsetup := Root.setup_cost_linear v shape.positive hs hv
  have hns' := hns.trans hsetup
  have hbudget : (73+returnWidth)*volume prime v+
      InductionWithin.coefficient returnWidth*volume prime v ≤ coefficient*volume prime v := by
    dsimp only [coefficient]
    nlinarith only [hV]
  have hgraphMargin : ∀ j, lo+(InductionWithin.coefficient returnWidth*volume prime v : ℕ) ≤ z.tapes.head j ∧
      z.tapes.head j+(InductionWithin.coefficient returnWidth*volume prime v : ℕ) ≤ hi := by
    intro j
    have ht := run_head_travel hrs j
    change before.head j-(ns : ℕ) ≤ z.tapes.head j ∧ z.tapes.head j ≤ before.head j+(ns : ℕ) at ht
    have hm := hmargin j
    dsimp only [before] at ht
    omega
  rw [hpost] at hgraphMargin
  obtain ⟨nb,hnb,hrb⟩ := InductionWithin.contract returnCapacity
    (InductionWithin.coefficient returnWidth) lo hi le_rfl depth .halt v shape hs hs hv
    (RecursiveRowsNode.header_length v shape.positive hs hv) f p node scalar st ready x hgraphMargin
  change RunWithin _ _ nb ((raw _ Root.tapeCount).start (Control.program returnCapacity widthSlot pcStack
    (implementation returnWidth))) _ at hrb
  dsimp only [Control.rootCode] at hpost
  rw [← hpost] at hrb
  have hws := RunWithin.heads_of_run_le hrs hns' lo hi (by
    intro j
    change lo+((73+returnWidth)*volume prime v : ℕ) ≤ before.head j ∧
      before.head j+((73+returnWidth)*volume prime v : ℕ) ≤ hi
    dsimp only [before]
    have hm := hmargin j
    omega)
  have hw := hws.seq hh hrb
  refine ⟨ns+1+nb,?_,_,hw,?_,?_⟩
  · dsimp only [budget]
    have := Nat.mul_le_mul_left (74+returnWidth) hV
    nlinarith only [hns',hnb,hV]
  · exact seq_halt_right Root.setup _ (BaseExecution.halt_entry returnCapacity _)
  · rfl

end
end IntegerMultBounds.MathlibTM2.M8.Machine.RootExecutionWithin
