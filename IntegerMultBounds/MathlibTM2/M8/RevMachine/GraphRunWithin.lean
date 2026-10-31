module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphRun
public import IntegerMultBounds.Machine.FiniteFlowWithin
public import IntegerMultBounds.Machine.SharedBankFamilyWithin

/-! The graph's existing block-and-edge decomposition also certifies every
prefix. Padding and the real controller join are included in the same bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphRun
open IntegerMultBounds.Machine
open Graph
open SharedBankStageInput (raw)
noncomputable section
variable {Seg Call : Type} {t a k : ℕ} (pieces : List (Piece Seg Call))
  (capacity : Fintype.card (PC pieces.length) ≤ 2^k) (stack : Fin t) (ht : 0 < t)
  (impl : Implementation t a k Seg Call)

/-- A padded block and its actual state-selected edge preserve the same tape predicate. -/
theorem member_jump_within (pc target : PC pieces.length) (before after : Tapes t a)
    {H : TapePred (tapeCount pieces capacity stack ht impl) a} {n : ℕ}
    {c : Config (tapeCount pieces capacity stack ht impl)
      (states pieces capacity stack ht impl (encoding pieces pc)) a}
    (hr : RunWithin (family pieces capacity stack ht impl (encoding pieces pc)) H n
      ((raw before (tapeCount pieces capacity stack ht impl)).start
        (family pieces capacity stack ht impl (encoding pieces pc))) c)
    (hh : step (family pieces capacity stack ht impl (encoding pieces pc)) c = none)
    (hbank : c.tapes = raw after (tapeCount pieces capacity stack ht impl))
    (he : next pieces capacity stack ht impl (encoding pieces pc) c.state = some (encoding pieces target)) :
    RunWithin (program pieces capacity stack ht impl) H (n+1)
      (entryConfig pieces capacity stack ht impl pc before)
      (entryConfig pieces capacity stack ht impl target after) := by
  have hj := FiniteFlow.block_then_jump_within (family pieces capacity stack ht impl)
    (next pieces capacity stack ht impl) (encoding pieces .prepare) (encoding pieces pc)
    (encoding pieces target) hr hh he
  rw [hbank] at hj
  exact hj

/-- Entering the root's halt block is a genuine halt of the full graph. -/
theorem entry_halt (y : Tapes t a) :
    step (program pieces capacity stack ht impl)
      (entryConfig pieces capacity stack ht impl .halt y) = none := by
  have hp : step (family pieces capacity stack ht impl (encoding pieces .halt))
      ((raw y (tapeCount pieces capacity stack ht impl)).start
        (family pieces capacity stack ht impl (encoding pieces .halt))) = none := by
    unfold family states
    rw [(encoding pieces).symm_apply_apply PC.halt]
    simp only [SharedBankFamily.program,SharedBankFamily.uniform,SharedBankFamily.pad,
      SharedBankFamily.padProgram]
    dsimp only [block,SharedBankFamily.ofProgram]
    simp [step,reindex,extend,skip]
  have hn : ∀ st, next pieces capacity stack ht impl (encoding pieces .halt) st = none := by
    unfold next states
    rw [(encoding pieces).symm_apply_apply PC.halt]
    intro st
    rfl
  exact FiniteFlow.halt (family pieces capacity stack ht impl) (next pieces capacity stack ht impl)
    (encoding pieces .prepare) (encoding pieces .halt) _ hp (hn _)

theorem block_jump_within_heads (pc target : PC pieces.length) (before after : Tapes t a) (B : ℕ)
    (h : HoareTime (block pieces capacity stack ht impl pc).program
      (· = raw before (block pieces capacity stack ht impl pc).tapes)
      (· = raw after (block pieces capacity stack ht impl pc).tapes) B)
    (he : ∀ st, edge pieces capacity stack ht impl pc st = some target)
    (lo hi : ℤ) (hlo : lo ≤ 0) (hhi : 0 ≤ hi)
    (hheads : ∀ c, RunInvariant (block pieces capacity stack ht impl pc).program
      (· = raw before (block pieces capacity stack ht impl pc).tapes) c →
      ∀ i, lo ≤ c.head i ∧ c.head i ≤ hi) :
    ∃ n ≤ B+1, RunWithin (program pieces capacity stack ht impl)
      (fun v => ∀ i, lo ≤ v.head i ∧ v.head i ≤ hi) n
      (entryConfig pieces capacity stack ht impl pc before)
      (entryConfig pieces capacity stack ht impl target after) := by
  have hp : ∃ n ≤ B, ∃ c : Config (tapeCount pieces capacity stack ht impl)
      (states pieces capacity stack ht impl (encoding pieces pc)) a,
      RunWithin (family pieces capacity stack ht impl (encoding pieces pc))
        (fun v => ∀ i, lo ≤ v.head i ∧ v.head i ≤ hi) n
        ((raw before (tapeCount pieces capacity stack ht impl)).start
          (family pieces capacity stack ht impl (encoding pieces pc))) c ∧
      step (family pieces capacity stack ht impl (encoding pieces pc)) c = none ∧
      c.tapes = raw after (tapeCount pieces capacity stack ht impl) := by
    unfold family states tapeCount
    rw [(encoding pieces).symm_apply_apply pc]
    exact SharedBankFamily.pad_within_heads _
      (SharedBankFamily.block_le (block pieces capacity stack ht impl) pc)
      (SharedBankFamily.common_le _) before after B h lo hi hlo hhi hheads
  obtain ⟨n,hn,c,hr,hh,hbank⟩ := hp
  have he' : ∀ st, next pieces capacity stack ht impl (encoding pieces pc) st =
      some (encoding pieces target) := by
    unfold next states
    rw [(encoding pieces).symm_apply_apply pc]
    intro st
    rw [he st]
    rfl
  exact ⟨n+1,by omega,member_jump_within pieces capacity stack ht impl pc target before after hr hh hbank (he' c.state)⟩

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphRun
