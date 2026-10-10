import IntegerMultBounds.Machine.CompactSpectatorStoppedLeafFlow

/-! The actual occupied return guard and binary-pop block of the stopped-leaf
cyclic table decode saved PCs into the continuation bank after four fixed PCs.
The entire stack frame is erased before the continuation begins. -/
namespace IntegerMultBounds.Machine.CompactSpectatorStoppedReturnFlow
noncomputable section
variable {k N w : ℕ}
abbrev popPC : Fin (N+4) := ⟨1,by omega⟩

/-- The occupied stack guard enters the actual decoder in three transitions. -/
theorem guard_pop (hN : N≤2^k) (stack : Fin (CompactSpectatorStoppedLeafCaller.total (w:=w))) (rest : Fin N → ℕ)
    (blocks : ∀ pc, Program (CompactSpectatorStoppedLeafCaller.total (w:=w)) (rest pc) 2)
    (edges : ∀ pc, Fin (rest pc) → Option (Fin (N+4))) (entry : Fin (N+4))
    (v : Tapes (CompactSpectatorStoppedLeafCaller.total (w:=w)) 2) (hb : v.tape stack (v.head stack-1)≠blank) :
    run (CompactSpectatorStoppedLeafFlow.program hN stack rest blocks edges entry) 3
      ((v.start (FiniteReturnGuard.program stack)).mapState (FiniteFlow.embed (CompactSpectatorStoppedLeafFlow.states (w:=w) (r:=k) rest) 0))=
      some ((v.start (Placement.placed (FiniteReturnStack.pop 2 k) (FiniteReturnStackAt.placement stack))).mapState
        (FiniteFlow.embed (CompactSpectatorStoppedLeafFlow.states (w:=w) (r:=k) rest) popPC)) := by
  have hr := FiniteReturnGuard.exact_run stack v
  rw [show decide (v.tape stack (v.head stack-1)=blank)=false by simp [hb]] at hr
  exact FiniteFlow.block_then_jump (CompactSpectatorStoppedLeafFlow.family stack rest blocks) (CompactSpectatorStoppedLeafFlow.next (w:=w) hN rest edges)
    entry 0 popPC v 2 (FiniteReturnGuard.terminal v false) hr
    (FiniteReturnGuard.terminal_halt stack v false) (by dsimp [CompactSpectatorStoppedLeafFlow.next,CompactSpectatorStoppedLeafFlow.states,Fin.cases,Fin.induction,FiniteReturnGuard.terminal]; rfl)

/-- Pop physically erases the fixed-width frame and enters the decoded continuation. -/
theorem pop_jump (hN : N≤2^k) (stack : Fin (CompactSpectatorStoppedLeafCaller.total (w:=w))) (rest : Fin N → ℕ)
    (blocks : ∀ pc, Program (CompactSpectatorStoppedLeafCaller.total (w:=w)) (rest pc) 2)
    (edges : ∀ pc, Fin (rest pc) → Option (Fin (N+4))) (entry : Fin (N+4)) (pc : Fin N)
    (v : Tapes (CompactSpectatorStoppedLeafCaller.total (w:=w)) 2) (f : ℤ → Fin 6) (p : ℤ)
    (ht : v.tape stack=FiniteReturnStack.wordPart f p (FiniteReturnStack.address hN pc) k le_rfl)
    (hh : v.head stack=p+k) (hf : ∀ j<k, f (p+j)=blank) :
    run (CompactSpectatorStoppedLeafFlow.program hN stack rest blocks edges entry) (k+2)
      ((v.start (Placement.placed (FiniteReturnStack.pop 2 k) (FiniteReturnStackAt.placement stack))).mapState
        (FiniteFlow.embed (CompactSpectatorStoppedLeafFlow.states (w:=w) (r:=k) rest) popPC))=
      some (((SharedPlacementAlphabet.setTape v stack f p).start (blocks pc)).mapState
        (FiniteFlow.embed (CompactSpectatorStoppedLeafFlow.states (w:=w) (r:=k) rest) pc.succ.succ.succ.succ)) := by
  obtain ⟨hr,hs⟩ := FiniteReturnStack.pop_exact (FiniteReturnStack.address hN pc) f p hf
  let c := FiniteReturnStack.cfg (.inr (0,FiniteReturnStack.address hN pc)) f p
  have ha : Placement.active (FiniteReturnStackAt.placement stack) v=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart f p (FiniteReturnStack.address hN pc) k le_rfl) (p+k) := by
    rw [FiniteReturnStackAt.active_bank,ht,hh]
  have hr' : run (FiniteReturnStack.pop 2 k) (k+1)
      ((Placement.active (FiniteReturnStackAt.placement stack) v).start (FiniteReturnStack.pop 2 k))=some c := by
    rw [ha]; exact hr
  have he : CompactSpectatorStoppedLeafFlow.next (w:=w) hN rest edges popPC (Placement.result (FiniteReturnStackAt.placement stack) v c).state=
      some pc.succ.succ.succ.succ := by
    change (FiniteReturnDispatch.select hN (FiniteReturnStack.encode k
      (.inr (0,FiniteReturnStack.address hN pc)))).map (fun pc => pc.succ.succ.succ.succ)=_
    rw [FiniteReturnDispatch.select_return]
    rfl
  have jump := FiniteFlow.block_then_jump (CompactSpectatorStoppedLeafFlow.family stack rest blocks) (CompactSpectatorStoppedLeafFlow.next (w:=w) hN rest edges)
    entry popPC pc.succ.succ.succ.succ v (k+1) (Placement.result (FiniteReturnStackAt.placement stack) v c)
    (Placement.placed_run _ _ v hr') (Placement.placed_halt _ _ v hs) he
  have hct : (Placement.result (FiniteReturnStackAt.placement stack) v c).tapes=
      SharedPlacementAlphabet.setTape v stack f p := by
    have hc : c.tapes=FiniteReturnStack.bank f p := rfl
    rw [Placement.result_tapes,hc]
    exact FiniteReturnStackAt.replace_bank _ _ _ _
  change run _ _ _=some (((Placement.result (FiniteReturnStackAt.placement stack) v c).tapes.start
    (CompactSpectatorStoppedLeafFlow.family stack rest blocks pc.succ.succ.succ.succ)).mapState (FiniteFlow.embed (CompactSpectatorStoppedLeafFlow.states (w:=w) (r:=k) rest) pc.succ.succ.succ.succ)) at jump
  rw [hct] at jump
  exact jump

/-- A positive-width saved PC is visibly occupied, regardless of its bit value. -/
theorem frame_occupied (hN : N≤2^k) (hk : 0<k) (pc : Fin N)
    (v : Tapes (CompactSpectatorStoppedLeafCaller.total (w:=w)) 2) (stack : Fin (CompactSpectatorStoppedLeafCaller.total (w:=w))) (f : ℤ → Fin 6) (p : ℤ)
    (ht : v.tape stack=FiniteReturnStack.wordPart f p (FiniteReturnStack.address hN pc) k le_rfl)
    (hh : v.head stack=p+k) : v.tape stack (v.head stack-1)≠blank := by
  rw [ht,hh]
  have hz : p+(k:ℤ)-1=p+((k-1:ℕ):ℤ) := by omega
  rw [hz,FiniteReturnStack.prefix_at f p (FiniteReturnStack.address hN pc) k le_rfl ⟨k-1,by omega⟩]
  cases FiniteReturnStack.address hN pc ⟨k-1,by omega⟩ <;> simp [bitSymbol,blank,Fin.ext_iff]

/-- Guard, actual pop, and decoded continuation entry form one concrete run.
No execution contract about any continuation is needed to reach its start. -/
theorem return_ready (hN : N≤2^k) (hk : 0<k) (stack : Fin (CompactSpectatorStoppedLeafCaller.total (w:=w))) (rest : Fin N → ℕ)
    (blocks : ∀ pc, Program (CompactSpectatorStoppedLeafCaller.total (w:=w)) (rest pc) 2)
    (edges : ∀ pc, Fin (rest pc) → Option (Fin (N+4))) (entry : Fin (N+4)) (pc : Fin N)
    (v : Tapes (CompactSpectatorStoppedLeafCaller.total (w:=w)) 2) (f : ℤ → Fin 6) (p : ℤ)
    (ht : v.tape stack=FiniteReturnStack.wordPart f p (FiniteReturnStack.address hN pc) k le_rfl)
    (hh : v.head stack=p+k) (hf : ∀ j<k, f (p+j)=blank) :
    run (CompactSpectatorStoppedLeafFlow.program hN stack rest blocks edges entry) (k+5)
      ((v.start (FiniteReturnGuard.program stack)).mapState (FiniteFlow.embed (CompactSpectatorStoppedLeafFlow.states (w:=w) (r:=k) rest) 0))=
      some (((SharedPlacementAlphabet.setTape v stack f p).start (blocks pc)).mapState
        (FiniteFlow.embed (CompactSpectatorStoppedLeafFlow.states (w:=w) (r:=k) rest) pc.succ.succ.succ.succ)) := by
  have hg := guard_pop hN stack rest blocks edges entry v (frame_occupied hN hk pc v stack f p ht hh)
  have hp := pop_jump hN stack rest blocks edges entry pc v f p ht hh hf
  rw [show k+5=3+(k+2) by omega,run_add,hg]
  simp only [Option.bind_some]
  exact hp


end
end IntegerMultBounds.Machine.CompactSpectatorStoppedReturnFlow
