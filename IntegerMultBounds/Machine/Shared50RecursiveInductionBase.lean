import IntegerMultBounds.Machine.Shared50RecursiveBudget
import IntegerMultBounds.Machine.Shared50RecursiveBasePermutation

/-! The actual graph's induction base, in the canonical binary source-bank
interface and logical-volume budget used by the recursive case. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveInductionBase
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50NodeSegments (payloadCount io)
open Shared50RecursiveControl
open Shared50RecursiveImplementation (implementation width pcStack)
open Shared50RecursiveBaseExecution (entryConfig)
open Shared50RecursiveBank (bank)
open Shared50RecursiveCallReady (Ready)
open Shared50RecursiveNodeSemantics (encoded)
open Shared50RecursiveNodeRows (transpose)
open Shared50RecursiveNodeLayout (wires)
open RecursiveRoleSerialization (roles)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedBankStageInput (raw)
variable {k : ℕ}
attribute [local irreducible] Shared50PieceSchedule.pieces Shared50FixedControl.control

/-- Binary canonical input is actually transposed and returned to the decoded
caller in the fixed graph, with every stack and spectator retained. -/
theorem run (capacity : Fintype.card PC ≤ 2^k) (target : PC)
    (v : Descriptor) (shape : Shared50RecursiveDepth.Shape 0 v)
    (hs old : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (hold : ∀ i, (old i).length ≤ 2*volume prime v)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Ready f p node scalar st) (x : Fin (volume prime v) → ZMod 2) :
    ∃ n ≤ Shared50RecursiveBudget.budget k 0 (volume prime v),
      Machine.run (Shared50RecursiveControl.program capacity width pcStack (implementation k)) n
        ((raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs f p node scalar
          (SharedBank.empty 0 prime) (RecursiveChildCallSetup.savedStacks old st
            (FiniteReturnStack.address capacity (encoding target))))
          (tapeCount capacity width pcStack (implementation k))).start
          (Shared50RecursiveControl.program capacity width pcStack (implementation k))) =
      some (entryConfig capacity target
        (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded (transpose (one_dvd v.rows) x))))
          old f p node scalar (SharedBank.empty 0 prime) st)) := by
  have hw := Shared50RecursiveDepth.base_width shape
  let rr := roles (RecursiveRowsSerialization.sourceData wires (encoded x))
  have ht : rr.tape io = RecursiveShiftRoleBank.source (encoded x) := by
    change (roles (RecursiveRowsSerialization.sourceData wires (encoded x))).tape io = _
    rw [Shared50RecursiveCallReady.source_roles]
    simp only [Shared50RecursiveCallSemantics.childRoles,SharedPlacementAlphabet.setTape,Function.update_self]
  obtain ⟨n,hn,htrace⟩ := Shared50RecursiveBaseExecution.guard_base_return capacity target v hw shape.positive
    rr old hs hv f p node scalar (SharedBank.empty 0 prime) st ready.descriptor ready.pc (encoded x) rfl ht
  have hout : RecursiveShiftRoleBank.updated rr io (RecursiveDigitRoleBank.array hw (encoded x)) =
      roles (RecursiveRowsSerialization.sourceData wires (encoded (transpose (one_dvd v.rows) x))) := by
    rw [Shared50RecursiveBasePermutation.array_transpose]
    exact Shared50RecursiveBasePermutation.source_roles_updated (encoded x) _
  rw [hout] at htrace
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v shape.positive
  have hreturn := Shared50RecursiveBudget.return_cost_bound (volume prime v) hV old hs hold
    (RecursiveRowsNode.header_length v shape.positive hs hv)
  refine ⟨n,?_,htrace⟩
  unfold Shared50RecursiveBudget.budget Shared50RecursiveBudget.base
  nlinarith

end
end IntegerMultBounds.Machine.Shared50RecursiveInductionBase
