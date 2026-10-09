import IntegerMultBounds.Machine.Shared50RecursiveInductionBase
import IntegerMultBounds.Machine.Shared50RecursiveNodeExecution
import IntegerMultBounds.Machine.Shared50RecursiveCallInductionBridge
import IntegerMultBounds.Machine.Shared50RecursiveBudgetAssembly

/-! Depth induction for one actual fixed recursive graph. Every child call
uses the graph's physical entry and decoded recovery edge, with the exact
logical-volume budget and the allocated nested stack invariants. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveInduction
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50TapeGlobal (roleCount)
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
open RecursiveInterchangeLayout (Descriptor volume role)
open SharedBankStageInput (raw)
variable {k : ℕ}
attribute [local irreducible] Shared50PieceSchedule.pieces Shared50FixedControl.control
  Shared50RecursiveCallLayout.parked

/-- The recursion contract, including exact restored caller state. -/
def Contract (capacity : Fintype.card PC ≤ 2^k) (depth : ℕ) : Prop :=
  ∀ (target : PC) (v : Descriptor) (_shape : Shared50RecursiveDepth.Shape depth v)
    (hs old : Fin 6 → List Bool) (_hv : RecursiveDimensionBank.Headers v hs)
    (_hold : ∀ i, (old i).length ≤ 2*volume prime v)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (_ready : Ready f p node scalar st) (x : Fin (volume prime v) → ZMod 2),
    ∃ n ≤ Shared50RecursiveBudget.budget k depth (volume prime v),
      Machine.run (Shared50RecursiveControl.program capacity width pcStack (implementation k)) n
        ((raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs f p node scalar
          (SharedBank.empty 0 prime) (RecursiveChildCallSetup.savedStacks old st
            (FiniteReturnStack.address capacity (encoding target))))
          (tapeCount capacity width pcStack (implementation k))).start
          (Shared50RecursiveControl.program capacity width pcStack (implementation k))) =
      some (entryConfig capacity target
        (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded (transpose (one_dvd v.rows) x))))
          old f p node scalar (SharedBank.empty 0 prime) st))

/-- The recursive contract supplies every literal physical call trace. -/
theorem calls {depth b : ℕ} {v : Descriptor} (capacity : Fintype.card PC ≤ 2^k)
    (ih : Contract capacity depth) (hw : v.width=125000*b) (hp : v.Positive)
    (childShape : ∀ i j : Fin 125000,
      Shared50RecursiveDepth.Shape depth (RecursiveAffineViews.cross prime b v i j))
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Ready f p node (SharedBank.empty 1 prime) st) :
    Shared50RecursiveNodeExecution.Calls capacity hw hs f p node st
      (Shared50RecursiveBudget.budget k depth (volume prime v)) := by
  intro site w i j hi data hdata
  obtain ⟨bits,rfl⟩ := hdata
  let mid := Shared50RecursiveCallReady.parkedBank w bits hs f p node
    (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st
  have htrace : ∀ ch : Fin 6 → List Bool,
      RecursiveDimensionBank.Headers (RecursiveInterchangeLayout.child prime 1 b v i j) ch →
      ∃ n ≤ Shared50RecursiveBudget.budget k depth (volume prime v),
        Machine.run (Shared50RecursiveControl.program capacity width pcStack (implementation k)) n
          (entryConfig capacity .guard (RecursiveCallProtocol.childBank mid ch
            (node.append ((SharedBank.empty 1 prime).append (SharedBank.empty 0 prime)))
            (RecursiveChildCallSetup.savedStacks hs st (returnCode capacity site)))) =
        some (entryConfig capacity (.recover site) (SharedPlacementAlphabet.setTape mid
          (RecursiveCallBank.role (u := 1+(1+0)) io).val
          (RecursiveShiftRoleBank.source (Shared50RecursiveChildPermutation.array hw i j (encoded (bits w)))) 0)) := by
    intro ch hch
    have hr := Shared50RecursiveCallInductionBridge.ready_original w bits hs f p node
      (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st ready
    have hold : ∀ z, (hs z).length ≤ 2*volume prime (RecursiveAffineViews.cross prime b v i j) := by
      rw [RecursiveAffineViews.cross_volume prime b v i j hw]
      exact RecursiveRowsNode.header_length v hp hs hv
    obtain ⟨n,hn,ht⟩ := ih (.recover site) (RecursiveAffineViews.cross prime b v i j)
      (childShape i j) ch hs hch hold (mid.tape (RecursiveCallBank.controlSlot 2))
      (mid.head (RecursiveCallBank.controlSlot 2)) node (SharedBank.empty 1 prime) st hr
      (Shared50RecursiveChildPermutation.toChild hw i j (bits w))
    rw [RecursiveAffineViews.cross_volume prime b v i j hw] at hn
    have hin := Shared50RecursiveCallInductionBridge.input_bank w i j hw bits hs ch f p node
      (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st
      (RecursiveChildCallSetup.savedStacks hs st (returnCode capacity site))
    have hout := Shared50RecursiveCallInductionBridge.returned_bank w i j hw bits hs f p node
      (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st
    change Machine.run _ n (entryConfig capacity .guard _) = some (entryConfig capacity (.recover site) _) at ht
    dsimp only [mid] at ht
    dsimp only [returnCode] at hin
    dsimp only at hout
    rw [← hin,hout] at ht
    exact ⟨n,hn,ht⟩
  have hcall := Shared50RecursivePieceExecution.call_actual (capacity := capacity) (hw := hw)
    (hp := hp) (hs := hs) (hv := hv) (f := f) (p := p) (node := node) (st := st)
    site w i j hi (Shared50NodeGates.encoded bits (fun _ => blank))
    (Shared50RecursiveChildPermutation.array hw i j (encoded (bits w))) rfl ready.payload _ htrace
  have he : Shared50NodeGates.encoded bits (fun _ => blank) (Shared50NodePieceTransport.worldSlot w) =
      encoded (bits w) := funext (Shared50NodePieceTransport.encoded_entry bits _ w)
  simpa only [Shared50RecursivePieceExecution.actualCallBound,Shared50RecursiveChildPermutation.child,he] using hcall

/-- Complete termination, transpose correctness and charged runtime for the
fixed recursive controller on all power-width nodes. -/
theorem contract (capacity : Fintype.card PC ≤ 2^k) (depth : ℕ) : Contract capacity depth := by
  induction depth with
  | zero => exact Shared50RecursiveInductionBase.run capacity
  | succ depth ih =>
    intro target v shape hs old hv hold f p node scalar st ready x
    have hscalar := ready.scalar
    subst scalar
    have saved := RecursiveStackAllocation.saved_stacks_available old st
      (FiniteReturnStack.address capacity (encoding target)) ready.descriptor ready.pc
    have hw := Shared50RecursiveDepth.split_width shape
    have hd := Shared50RecursiveDepth.split_divides shape
    have hpRole := Shared50RecursiveDepth.split_positive shape
    have hrolevol : volume prime (role v roleCount) = volume prime v/roleCount :=
      (Shared50RecursiveDepth.selected_volume_role shape (0 : Fin 125000) (0 : Fin 125000)).symm.trans
        (Shared50RecursiveDepth.selected_volume shape (0 : Fin 125000) (0 : Fin 125000))
    have allCalls : ∀ rs : List Bool,
        RecursiveDimensionBank.Headers (role v roleCount) (RecursiveRowsNodeHeaders.headers hs rs) →
        Shared50RecursiveNodeExecution.Calls capacity (v := role v roleCount) hw
          (RecursiveRowsNodeHeaders.headers hs rs) f p (RecursiveViewFrame.savedStack hs node)
          (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target)))
          (Shared50RecursiveBudget.budget k depth (volume prime v/roleCount)) := by
      intro rs hrs
      rw [← hrolevol]
      exact calls capacity ih hw hpRole (fun i j => Shared50RecursiveDepth.selected_shape shape i j)
        _ hrs f p _ _ ⟨ready.payload,RecursiveRowsNode.saved_available hs node ready.node,rfl,saved.1,saved.2⟩
    obtain ⟨n,hn,ht⟩ := Shared50RecursiveNodeExecution.guard_return (v := v) capacity target hw shape.positive hd
      old hs hv f p node st ready.node ready.descriptor ready.pc x
      (Shared50RecursiveBudget.budget k depth (volume prime v/roleCount)) allCalls
    have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v shape.positive
    have hroleLe : volume prime (role v roleCount) ≤ volume prime v := by
      rw [hrolevol]
      exact Nat.div_le_self _ _
    have hret := Shared50RecursiveBudget.return_cost_bound (volume prime v) hV old hs hold
      (RecursiveRowsNode.header_length v shape.positive hs hv)
    have hbound := Shared50RecursiveBudgetAssembly.node_bound k depth (volume prime v)
      (volume prime (role v roleCount)) (RecursiveChildCallReturn.cost old hs) hV hroleLe hret
    exact ⟨n,hn.trans hbound,ht⟩

/-- The explicit graph execution interface, with generalized depth. -/
theorem run (capacity : Fintype.card PC ≤ 2^k) (depth : ℕ) : Contract capacity depth :=
  contract capacity depth

end
end IntegerMultBounds.Machine.Shared50RecursiveInduction
