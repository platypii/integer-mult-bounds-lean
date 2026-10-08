import IntegerMultBounds.Machine.Shared50RecursiveExecution

/-! Physical block contracts lift to actual cyclic graph traces. Padding and
the controller edge retain the exact bank, and the edge costs one transition. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveBlockExecution
noncomputable section
open Shared50RecursiveControl SharedBankStageInput
variable {t a k : ℕ}

/-- Execute a padded member, then take its actual next-table edge. -/
theorem member_jump (capacity : Fintype.card PC ≤ 2^k) (width stack : Fin t)
    (impl : Implementation t a k) (i j : Fin (Fintype.card PC))
    (before after : Tapes t a) (B : ℕ)
    (h : HoareTime (family capacity width stack impl i)
      (fun w => w = raw before (tapeCount capacity width stack impl))
      (fun w => w = raw after (tapeCount capacity width stack impl)) B)
    (he : ∀ st, next capacity width stack impl i st = some j) :
    ∃ steps ≤ B+1, run (program capacity width stack impl) steps
      (((raw before (tapeCount capacity width stack impl)).start
        (family capacity width stack impl i)).mapState
          (FiniteFlow.embed (states capacity width stack impl) i)) =
      some (((raw after (tapeCount capacity width stack impl)).start
        (family capacity width stack impl j)).mapState
          (FiniteFlow.embed (states capacity width stack impl) j)) := by
  obtain ⟨n,c,hn,hr,hhalt,hbank⟩ := h _ rfl
  have hj := FiniteFlow.block_then_jump (family capacity width stack impl) (next capacity width stack impl)
    (encoding .guard) i j _ n c hr hhalt (he c.state)
  rw [hbank] at hj
  exact ⟨n+1,by omega,hj⟩

/-- A clean actual block runs on the compiled graph without an external bank
placement assumption. Its finite edge adds exactly one charged transition. -/
theorem block_jump (capacity : Fintype.card PC ≤ 2^k) (width stack : Fin t)
    (impl : Implementation t a k) (pc target : PC) (before after : Tapes t a) (B : ℕ)
    (h : HoareTime (block capacity width stack impl pc).program
      (fun w => w = raw before (block capacity width stack impl pc).tapes)
      (fun w => w = raw after (block capacity width stack impl pc).tapes) B)
    (he : ∀ st, edge capacity width stack impl pc st = some target) :
    ∃ steps ≤ B+1, run (program capacity width stack impl) steps
      (((raw before (tapeCount capacity width stack impl)).start
        (family capacity width stack impl (encoding pc))).mapState
          (FiniteFlow.embed (states capacity width stack impl) (encoding pc))) =
      some (((raw after (tapeCount capacity width stack impl)).start
        (family capacity width stack impl (encoding target))).mapState
          (FiniteFlow.embed (states capacity width stack impl) (encoding target))) := by
  have hpad := SharedBankFamily.realizes (block capacity width stack impl) pc before after B h
  have hi : encoding.symm (encoding pc) = pc := encoding.symm_apply_apply _
  apply member_jump capacity width stack impl (encoding pc) (encoding target) before after B
  · unfold family states tapeCount
    rw [hi]
    exact hpad
  · unfold next states
    rw [hi]
    intro st
    rw [he st]
    rfl

end
end IntegerMultBounds.Machine.Shared50RecursiveBlockExecution
