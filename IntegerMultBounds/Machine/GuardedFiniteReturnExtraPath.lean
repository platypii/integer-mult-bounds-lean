import IntegerMultBounds.Machine.GuardedFiniteReturnExtraFlow
import IntegerMultBounds.Machine.FiniteFlowPath

/-! Actual occupied guard and saved PC pop form a nonhalting path in the same
finite table. Both physical jumps are charged; no continuation run is assumed. -/
namespace IntegerMultBounds.Machine.GuardedFiniteReturnExtraPath
noncomputable section
open GuardedFiniteReturnExtraFlow
variable {N extra k t a : ℕ}

theorem return_path (hN : N≤2^k) (hk : 0<k) (stack : Fin t) (rest : Fin (N+extra) → ℕ)
    (blocks : ∀ pc, Program t (rest pc) a)
    (edges : ∀ pc, Fin (rest pc) → Option (Fin (N+extra+2))) (pc : Fin N)
    (v : Tapes t a) (f : ℤ → Fin (a+4)) (p : ℤ)
    (ht : v.tape stack=FiniteReturnStack.wordPart f p (FiniteReturnStack.address hN pc) k le_rfl)
    (hh : v.head stack=p+k) (hf : ∀ j<k, f (p+j)=blank) :
    FiniteFlowPath.Path (family stack rest blocks) (next hN rest edges) 0 v (k+5)
      (Fin.castAdd extra pc).succ.succ (SharedPlacementAlphabet.setTape v stack f p) := by
  have hb := frame_occupied hN hk pc v stack f p ht hh
  have hg := FiniteReturnGuard.exact_run stack v
  rw [show decide (v.tape stack (v.head stack-1)=blank)=false by simp [hb]] at hg
  have hguard := FiniteFlowPath.block_path (family:=family stack rest blocks)
    (next:=next hN rest edges) 0 popPC v 2 (FiniteReturnGuard.terminal v false) hg
    (FiniteReturnGuard.terminal_halt stack v false)
    (by dsimp [next,states,Fin.cases,Fin.induction,FiniteReturnGuard.terminal]; rfl)
  obtain ⟨hr,hs⟩ := FiniteReturnStack.pop_exact (FiniteReturnStack.address hN pc) f p hf
  let c := FiniteReturnStack.cfg (.inr (0,FiniteReturnStack.address hN pc)) f p
  have ha : Placement.active (FiniteReturnStackAt.placement stack) v=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart f p (FiniteReturnStack.address hN pc) k le_rfl) (p+k) := by
    rw [FiniteReturnStackAt.active_bank,ht,hh]
  have hr' : run (FiniteReturnStack.pop a k) (k+1)
      ((Placement.active (FiniteReturnStackAt.placement stack) v).start (FiniteReturnStack.pop a k))=some c := by
    rw [ha]; exact hr
  have he : next hN rest edges popPC (Placement.result (FiniteReturnStackAt.placement stack) v c).state=
      some (Fin.castAdd extra pc).succ.succ := by
    change (FiniteReturnDispatch.select hN (FiniteReturnStack.encode k
      (.inr (0,FiniteReturnStack.address hN pc)))).map (fun pc => (Fin.castAdd extra pc).succ.succ)=_
    rw [FiniteReturnDispatch.select_return]
    rfl
  have hpop := FiniteFlowPath.block_path (family:=family stack rest blocks)
    (next:=next hN rest edges) popPC (Fin.castAdd extra pc).succ.succ v (k+1)
    (Placement.result (FiniteReturnStackAt.placement stack) v c)
    (Placement.placed_run _ _ v hr') (Placement.placed_halt _ _ v hs) he
  have hct : (Placement.result (FiniteReturnStackAt.placement stack) v c).tapes=
      SharedPlacementAlphabet.setTape v stack f p := by
    change Placement.replace (FiniteReturnStackAt.placement stack) v (FiniteReturnStack.bank f p)=_
    exact FiniteReturnStackAt.replace_bank _ _ _ _
  have hpop' : FiniteFlowPath.Path (family stack rest blocks) (next hN rest edges)
      popPC v (k+1+1) (Fin.castAdd extra pc).succ.succ (SharedPlacementAlphabet.setTape v stack f p) := by
    exact hct ▸ hpop
  have h := FiniteFlowPath.append hguard hpop'
  simpa only [FiniteReturnGuard.terminal,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

end
end IntegerMultBounds.Machine.GuardedFiniteReturnExtraPath
