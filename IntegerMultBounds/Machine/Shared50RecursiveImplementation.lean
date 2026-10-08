import IntegerMultBounds.Machine.Shared50RecursiveBankNodes
import IntegerMultBounds.Machine.Shared50RecursiveCallLayout
import IntegerMultBounds.Machine.Shared50RecursiveNodeLayout
import IntegerMultBounds.Machine.Shared50RecursiveControl
import IntegerMultBounds.Machine.RecursiveDigitRoleBank
import IntegerMultBounds.Machine.RecursiveChildReturnRoleBank

/-! One concrete fixed recursive graph: all implementation fields are actual
physical programs on the common bank. No runtime width or recursion depth is a
program parameter. Correctness of the whole recursive execution is separate. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveImplementation
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50NodeSegments (payloadCount io)
open Shared50NodePieceTransport (worldSlot)
open Shared50RecursiveCallLayout (parked active_ne_io)
open Shared50RecursiveControl (PC)
attribute [local irreducible] Shared50PieceSchedule.pieces Shared50FixedControl.control

abbrev commonCount := Shared50RecursiveBank.Count payloadCount 0

def width : Fin commonCount := RecursiveCallBank.headerSlot 3
def descriptorStack : Fin commonCount := Shared50RecursiveBank.returnSlot 0
def pcStack : Fin commonCount := Shared50RecursiveBank.returnSlot 1

/-- Only the fixed return-address bit capacity parametrizes the implementation;
every call site parks the other World streams in the same finite order. -/
def implementation (k : ℕ) : Shared50RecursiveControl.Implementation commonCount prime k where
  base := SharedBankFamily.ofProgram
    (RecursiveDigitRoleBank.program (u := Shared50RecursiveBank.AuxCount 0) io)
  split := Shared50RecursiveBankNodes.entry (u := 0)
    Shared50RecursiveNodeLayout.wires Shared50RecursiveNodeLayout.wires_injective
  merge := Shared50RecursiveBankNodes.exit (u := 0) Shared50RecursiveNodeLayout.mergeRoute
    Shared50RecursiveNodeLayout.wires Shared50RecursiveNodeLayout.wires_injective
  restore := SharedBankFamily.ofProgram
    (RecursiveChildReturnRoleBank.restoreProgram (t := payloadCount) (u := 3+(1+(1+0))))
  segment := Shared50RecursiveBankNodes.segment (u := 0)
  gate := Shared50RecursiveBankNodes.gate (u := 0)
  enter := fun w i j code => RecursiveCallProtocol.enter (u := 1+(1+0))
    (parked w) (worldSlot w) io (active_ne_io w) i j code
  recover := fun w _ _ => RecursiveCallProtocol.recover (u := 1+(1+0))
    (parked w) (worldSlot w) io (active_ne_io w)

/-- A single compile-time return width for the full literal schedule. -/
def returnWidth : ℕ := Classical.choose Shared50RecursiveControl.capacity_exists

theorem returnCapacity : Fintype.card PC ≤ 2^returnWidth :=
  Classical.choose_spec Shared50RecursiveControl.capacity_exists

/-- The actual closed cyclic machine, including guard and decoded returns. -/
def graph := Shared50RecursiveControl.program returnCapacity width pcStack (implementation returnWidth)

def headerField (i : Fin 6) : BinaryDescriptorFrames.Slot descriptorStack :=
  ⟨RecursiveCallBank.headerSlot i,by
    intro he
    have hv := congrArg Fin.val he
    have hi := i.isLt
    simp only [RecursiveCallBank.headerSlot,descriptorStack,Shared50RecursiveBank.returnSlot,
      Fin.val_natAdd,Fin.val_castAdd] at hv
    omega⟩

def rootFields : List (BinaryDescriptorFrames.Slot descriptorStack) :=
  List.ofFn headerField

/-- Root header saving and the real halt-sentinel push precede the same fixed
graph used by every child. Proving its total execution remains an obligation. -/
def program := Shared50RecursiveControl.rootProgram returnCapacity width pcStack descriptorStack
  rootFields (implementation returnWidth)

end
end IntegerMultBounds.Machine.Shared50RecursiveImplementation
