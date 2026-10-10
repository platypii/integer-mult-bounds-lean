import IntegerMultBounds.Machine.GuardedFiniteReturnExtraPath
import IntegerMultBounds.Machine.CompactComplexFixedNodePaths

/-! The original fixed cyclic node table physically decodes its genuine saved
PC from guard0 and enters the original call's continuation. Only the saved
stack changes; its guard/pop transitions and both table joins are paid. -/
namespace IntegerMultBounds.Machine.CompactComplexFixedNodeSavedReturnPath
noncomputable section
open Networks
open CompactComplexFixedNodePaths (nodePath)
open CompactComplexFixedNodeTable
open CompactComplexScheduledPCLayout
open CompactComplexCompletedLiveLower (Event schedule)
variable {t : ℕ}
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites schedule
  CompactComplexRolePhaseSite.roleCount CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth
  tableProgramsWith returnPrograms CompactComplexFixedNodePaths.nodeEdges

theorem saved_return_path (ht : 0<t) (stack : Fin t)
    (childReturn : ComplexRecursiveCallSchema.Call → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (event : Event → Σ q,Program t q 2)
    (isStopped : Fin (controls 0).1 → Bool) (call : ComplexRecursiveCallSchema.Call)
    (v : Tapes t 2) (older : ℤ → Fin 6) (origin : ℤ)
    (hw : 0<CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))
    (hs : v.tape stack=FiniteReturnStack.wordPart older origin
      (CompactComplexCallReturn.code call)
      (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
    (hh : v.head stack=origin+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))
    (hf : ∀ j<CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3),
      older (origin+j)=blank) :
    nodePath ht stack childReturn controls event isStopped 0 v
      (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)+5)
      (CompactComplexScheduledPCDecode.savedPC call) (SharedPlacementAlphabet.setTape v stack older origin) := by
  let w := CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)
  let room : originalCount≤2^w := CompactComplexCallReturn.roomFor ComplexRecursiveCallSchema.sites.length (25^3)
  let address := CompactComplexScheduledPCDecode.callAddress call
  let E := CompactComplexFixedNodePaths.nodeEdges ht childReturn controls event isStopped
  have hs' : v.tape stack=FiniteReturnStack.wordPart older origin
      (FiniteReturnStack.address room address) w le_rfl := by
    rw [←CompactComplexScheduledPCDecode.saved_code call]
    exact hs
  change FiniteFlowPath.Path (GuardedFiniteReturnExtraFlow.family stack (fun i => (tableProgramsWith (returnPrograms ht childReturn) controls (fun j => event (schedule.get j)) i).1) (fun i => (tableProgramsWith (returnPrograms ht childReturn) controls (fun j => event (schedule.get j)) i).2))
    (GuardedFiniteReturnExtraFlow.next room (fun i => (tableProgramsWith (returnPrograms ht childReturn) controls (fun j => event (schedule.get j)) i).1) E) 0 v (w+5)
    (Fin.castAdd (4+schedule.length) address).succ.succ (SharedPlacementAlphabet.setTape v stack older origin)
  exact @GuardedFiniteReturnExtraPath.return_path originalCount (4+schedule.length) w t 2
    room hw stack
    (fun i => (tableProgramsWith (returnPrograms ht childReturn) controls (fun j => event (schedule.get j)) i).1)
    (fun i => (tableProgramsWith (returnPrograms ht childReturn) controls (fun j => event (schedule.get j)) i).2)
    E address v older origin hs' hh hf

end
end IntegerMultBounds.Machine.CompactComplexFixedNodeSavedReturnPath
