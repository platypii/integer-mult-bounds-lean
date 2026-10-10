import IntegerMultBounds.Machine.CompactComplexFixedNodePaths

/-! A reached empty-stack return guard genuinely halts the original fixed node
controller. The two physical guard steps preserve the complete computed bank;
this lemma does not supply the preceding recursive execution path. -/
namespace IntegerMultBounds.Machine.CompactComplexFixedNodeRootExit
noncomputable section
open Networks
open CompactComplexFixedNodeTable
open CompactComplexFixedNodePaths
open CompactComplexScheduledPCLayout (originalCount)
open CompactComplexCompletedLiveLower (schedule Event)
variable {t : ℕ}
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites schedule
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth

private theorem root_trace_with {N extra k : ℕ} (hN : N≤2^k) (stack : Fin t)
    (programs : Fin (N+extra) → Σ q,Program t q 2)
    (edges : ∀ pc,Fin (programs pc).1 → Option (Fin (N+extra+2))) (v : Tapes t 2)
    (hb : v.tape stack (v.head stack-1)=blank) :
    ∃ c,FiniteFlow.Trace
      (GuardedFiniteReturnExtraFlow.family (k:=k) stack (fun pc => (programs pc).1) (fun pc => (programs pc).2))
      (GuardedFiniteReturnExtraFlow.next hN (fun pc => (programs pc).1) edges) 0 v 2 0 c ∧ c.tapes=v := by
  have hr := FiniteReturnGuard.exact_run stack v
  rw [hb] at hr
  simp only [decide_true] at hr
  refine ⟨FiniteReturnGuard.terminal v true,FiniteFlow.Trace.stop 0 v 2 _ hr
    (FiniteReturnGuard.terminal_halt stack v true) rfl,rfl⟩

theorem root_trace (ht : 0<t) (stack : Fin t)
    (childReturn : ComplexRecursiveCallSchema.Call → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (event : Event → Σ q,Program t q 2)
    (isStopped : Fin (controls 0).1 → Bool) (v : Tapes t 2)
    (hb : v.tape stack (v.head stack-1)=blank) :
    ∃ c,FiniteFlow.Trace (nodeFamily ht stack childReturn controls event)
      (nodeNext ht childReturn controls event isStopped) 0 v 2 0 c ∧ c.tapes=v :=
  root_trace_with (N:=originalCount) (extra:=4+schedule.length)
    (k:=CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))
    (CompactComplexCallReturn.roomFor ComplexRecursiveCallSchema.sites.length (25^3)) stack
    (tableProgramsWith (returnPrograms ht childReturn) controls (fun i => event (schedule.get i)))
    (nodeEdges ht childReturn controls event isStopped) v hb

/-- Once the actual root path reaches its empty guard, no execution oracle is
needed to obtain genuine halting on the original fixed transition table. -/
theorem path_halts (ht : 0<t) (stack : Fin t)
    (childReturn : ComplexRecursiveCallSchema.Call → Σ q,Program t q 2)
    (controls : Fin 4 → Σ q,Program t q 2) (event : Event → Σ q,Program t q 2)
    (isStopped : Fin (controls 0).1 → Bool) (before after : Tapes t 2) (n : ℕ)
    (hp : nodePath ht stack childReturn controls event isStopped
      (controlPCFor originalCount schedule.length 0) before n 0 after)
    (hb : after.tape stack (after.head stack-1)=blank) :
    HoareTime (fixedProgram ht stack childReturn controls event isStopped)
      (fun v => v=before) (fun v => v=after) (n+2) := by
  rw [fixedProgram_eq]
  obtain ⟨c,htail,hc⟩ := root_trace ht stack childReturn controls event isStopped after hb
  have h := FiniteFlowPath.path_then_trace_hoare hp htail
  rw [hc] at h
  exact h

end
end IntegerMultBounds.Machine.CompactComplexFixedNodeRootExit
