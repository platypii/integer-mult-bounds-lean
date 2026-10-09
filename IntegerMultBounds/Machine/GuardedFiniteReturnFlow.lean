import IntegerMultBounds.Machine.FiniteReturnGuard
import IntegerMultBounds.Machine.FiniteReturnFlow

/-! One fixed cyclic table contains an empty-stack guard, the binary pop
machine, and every continuation. The guard supplies the root exit: occupied saved frames
physically decode their PC and enter its continuation, while the empty root
stack halts without attempting a pop. -/
namespace IntegerMultBounds.Machine.GuardedFiniteReturnFlow
noncomputable section
variable {k N t a : ℕ}

abbrev states (rest : Fin N → ℕ) : Fin (N+2) → ℕ :=
  Fin.cases 4 (Fin.cases (Fintype.card (FiniteReturnStack.Control k)) rest)
abbrev popPC : Fin (N+2) := ⟨1,by omega⟩
def family (stack : Fin t) (rest : Fin N → ℕ)
    (blocks : ∀ pc, Program t (rest pc) a) : ∀ pc, Program t (states (k := k) rest pc) a :=
  Fin.cases (FiniteReturnGuard.program stack)
    (Fin.cases (Placement.placed (FiniteReturnStack.pop a k) (FiniteReturnStackAt.placement stack)) blocks)
def next (hN : N≤2^k) (rest : Fin N → ℕ)
    (edges : ∀ pc, Fin (rest pc) → Option (Fin (N+2))) : FiniteFlow.Next (states (k := k) rest) :=
  Fin.cases (fun st => if st.val=3 then some popPC else none)
    (Fin.cases (fun st => (FiniteReturnDispatch.select hN st).map (fun pc => pc.succ.succ)) edges)
def program (hN : N≤2^k) (stack : Fin t) (rest : Fin N → ℕ)
    (blocks : ∀ pc, Program t (rest pc) a)
    (edges : ∀ pc, Fin (rest pc) → Option (Fin (N+2))) (entry : Fin (N+2)) :=
  FiniteFlow.program (family stack rest blocks) (next hN rest edges) entry

/-- Root exit costs precisely two physical transitions and preserves the whole bank. -/
theorem root_halt (hN : N≤2^k) (stack : Fin t) (rest : Fin N → ℕ)
    (blocks : ∀ pc, Program t (rest pc) a)
    (edges : ∀ pc, Fin (rest pc) → Option (Fin (N+2))) (entry : Fin (N+2))
    (v : Tapes t a) (hb : v.tape stack (v.head stack-1)=blank) :
    run (program hN stack rest blocks edges entry) 2
      ((v.start (FiniteReturnGuard.program stack)).mapState (FiniteFlow.embed (states rest) 0))=
      some ((FiniteReturnGuard.terminal v true).mapState (FiniteFlow.embed (states rest) 0)) ∧
    step (program hN stack rest blocks edges entry)
      ((FiniteReturnGuard.terminal v true).mapState (FiniteFlow.embed (states rest) 0))=none := by
  have hr := FiniteReturnGuard.exact_run stack v
  rw [hb] at hr
  simp only [decide_true] at hr
  exact ⟨FiniteFlow.block_run (family stack rest blocks) (next hN rest edges) entry 0 2 _ _ hr,
    FiniteFlow.halt (family stack rest blocks) (next hN rest edges) entry 0 _
      (FiniteReturnGuard.terminal_halt stack v true) (by dsimp [next,states,Fin.cases,Fin.induction,FiniteReturnGuard.terminal]; rfl)⟩

/-- The occupied stack guard enters the actual decoder in three transitions. -/
theorem guard_pop (hN : N≤2^k) (stack : Fin t) (rest : Fin N → ℕ)
    (blocks : ∀ pc, Program t (rest pc) a)
    (edges : ∀ pc, Fin (rest pc) → Option (Fin (N+2))) (entry : Fin (N+2))
    (v : Tapes t a) (hb : v.tape stack (v.head stack-1)≠blank) :
    run (program hN stack rest blocks edges entry) 3
      ((v.start (FiniteReturnGuard.program stack)).mapState (FiniteFlow.embed (states rest) 0))=
      some ((v.start (Placement.placed (FiniteReturnStack.pop a k) (FiniteReturnStackAt.placement stack))).mapState
        (FiniteFlow.embed (states rest) popPC)) := by
  have hr := FiniteReturnGuard.exact_run stack v
  rw [show decide (v.tape stack (v.head stack-1)=blank)=false by simp [hb]] at hr
  exact FiniteFlow.block_then_jump (family stack rest blocks) (next hN rest edges)
    entry 0 popPC v 2 (FiniteReturnGuard.terminal v false) hr
    (FiniteReturnGuard.terminal_halt stack v false) (by dsimp [next,states,Fin.cases,Fin.induction,FiniteReturnGuard.terminal]; rfl)

/-- Pop physically erases the fixed-width frame and enters the decoded continuation. -/
theorem pop_jump (hN : N≤2^k) (stack : Fin t) (rest : Fin N → ℕ)
    (blocks : ∀ pc, Program t (rest pc) a)
    (edges : ∀ pc, Fin (rest pc) → Option (Fin (N+2))) (entry : Fin (N+2)) (pc : Fin N)
    (v : Tapes t a) (f : ℤ → Fin (a+4)) (p : ℤ)
    (ht : v.tape stack=FiniteReturnStack.wordPart f p (FiniteReturnStack.address hN pc) k le_rfl)
    (hh : v.head stack=p+k) (hf : ∀ j<k, f (p+j)=blank) :
    run (program hN stack rest blocks edges entry) (k+2)
      ((v.start (Placement.placed (FiniteReturnStack.pop a k) (FiniteReturnStackAt.placement stack))).mapState
        (FiniteFlow.embed (states rest) popPC))=
      some (((SharedPlacementAlphabet.setTape v stack f p).start (blocks pc)).mapState
        (FiniteFlow.embed (states rest) pc.succ.succ)) := by
  obtain ⟨hr,hs⟩ := FiniteReturnStack.pop_exact (FiniteReturnStack.address hN pc) f p hf
  let c := FiniteReturnStack.cfg (.inr (0,FiniteReturnStack.address hN pc)) f p
  have ha : Placement.active (FiniteReturnStackAt.placement stack) v=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart f p (FiniteReturnStack.address hN pc) k le_rfl) (p+k) := by
    rw [FiniteReturnStackAt.active_bank,ht,hh]
  have hr' : run (FiniteReturnStack.pop a k) (k+1)
      ((Placement.active (FiniteReturnStackAt.placement stack) v).start (FiniteReturnStack.pop a k))=some c := by
    rw [ha]; exact hr
  have he : next hN rest edges popPC (Placement.result (FiniteReturnStackAt.placement stack) v c).state=
      some pc.succ.succ := by
    change (FiniteReturnDispatch.select hN (FiniteReturnStack.encode k
      (.inr (0,FiniteReturnStack.address hN pc)))).map (fun pc => pc.succ.succ)=_
    rw [FiniteReturnDispatch.select_return]
    rfl
  have jump := FiniteFlow.block_then_jump (family stack rest blocks) (next hN rest edges)
    entry popPC pc.succ.succ v (k+1) (Placement.result (FiniteReturnStackAt.placement stack) v c)
    (Placement.placed_run _ _ v hr') (Placement.placed_halt _ _ v hs) he
  have hct : (Placement.result (FiniteReturnStackAt.placement stack) v c).tapes=
      SharedPlacementAlphabet.setTape v stack f p := by
    change Placement.replace (FiniteReturnStackAt.placement stack) v (FiniteReturnStack.bank f p)=_
    exact FiniteReturnStackAt.replace_bank _ _ _ _
  change run _ _ _=some (((Placement.result (FiniteReturnStackAt.placement stack) v c).tapes.start
    (family stack rest blocks pc.succ.succ)).mapState (FiniteFlow.embed (states rest) pc.succ.succ)) at jump
  rw [hct] at jump
  exact jump

/-- A positive-width saved PC is visibly occupied, regardless of its bit value. -/
theorem frame_occupied (hN : N≤2^k) (hk : 0<k) (pc : Fin N)
    (v : Tapes t a) (stack : Fin t) (f : ℤ → Fin (a+4)) (p : ℤ)
    (ht : v.tape stack=FiniteReturnStack.wordPart f p (FiniteReturnStack.address hN pc) k le_rfl)
    (hh : v.head stack=p+k) : v.tape stack (v.head stack-1)≠blank := by
  rw [ht,hh]
  have hz : p+(k:ℤ)-1=p+((k-1:ℕ):ℤ) := by omega
  rw [hz,FiniteReturnStack.prefix_at f p (FiniteReturnStack.address hN pc) k le_rfl ⟨k-1,by omega⟩]
  cases FiniteReturnStack.address hN pc ⟨k-1,by omega⟩ <;> simp [bitSymbol,blank,Fin.ext_iff]

/-- Guard, actual pop, and decoded continuation entry form one concrete run.
No execution contract about any continuation is needed to reach its start. -/
theorem return_ready (hN : N≤2^k) (hk : 0<k) (stack : Fin t) (rest : Fin N → ℕ)
    (blocks : ∀ pc, Program t (rest pc) a)
    (edges : ∀ pc, Fin (rest pc) → Option (Fin (N+2))) (entry : Fin (N+2)) (pc : Fin N)
    (v : Tapes t a) (f : ℤ → Fin (a+4)) (p : ℤ)
    (ht : v.tape stack=FiniteReturnStack.wordPart f p (FiniteReturnStack.address hN pc) k le_rfl)
    (hh : v.head stack=p+k) (hf : ∀ j<k, f (p+j)=blank) :
    run (program hN stack rest blocks edges entry) (k+5)
      ((v.start (FiniteReturnGuard.program stack)).mapState (FiniteFlow.embed (states rest) 0))=
      some (((SharedPlacementAlphabet.setTape v stack f p).start (blocks pc)).mapState
        (FiniteFlow.embed (states rest) pc.succ.succ)) := by
  have hg := guard_pop hN stack rest blocks edges entry v (frame_occupied hN hk pc v stack f p ht hh)
  have hp := pop_jump hN stack rest blocks edges entry pc v f p ht hh hf
  rw [show k+5=3+(k+2) by omega,run_add,hg]
  simp only [Option.bind_some]
  exact hp

/-- Finite control size depends only on fixed blocks and PC width, never stack depth. -/
theorem control_size (rest : Fin N → ℕ) :
    Fintype.card (FiniteFlow.Control (states (k := k) rest))=
      4+Fintype.card (FiniteReturnStack.Control k)+∑ pc,rest pc := by
  rw [FiniteFlow.control_card]
  simp [states,Fin.sum_univ_succ,Nat.add_assoc]

/-- Fixed continuation edges may re-enter the recursive entry or return guard.
Only the block's actual terminal control state is consulted. -/
theorem continuation_jump (hN : N≤2^k) (stack : Fin t) (rest : Fin N → ℕ)
    (blocks : ∀ pc, Program t (rest pc) a)
    (edges : ∀ pc, Fin (rest pc) → Option (Fin (N+2))) (entry : Fin (N+2))
    (pc : Fin N) (dest : Fin (N+2)) (v : Tapes t a) (n : ℕ) (c : Config t (rest pc) a)
    (hr : run (blocks pc) n (v.start (blocks pc))=some c)
    (hh : step (blocks pc) c=none) (he : edges pc c.state=some dest) :
    run (program hN stack rest blocks edges entry) (n+1)
      ((v.start (blocks pc)).mapState (FiniteFlow.embed (states (k := k) rest) pc.succ.succ))=
      some ((c.tapes.start (family stack rest blocks dest)).mapState (FiniteFlow.embed (states rest) dest)) :=
  FiniteFlow.block_then_jump (family stack rest blocks) (next hN rest edges)
    entry pc.succ.succ dest v n c hr hh (by simpa [next,states,Fin.cases,Fin.induction,Fin.induction.go] using he)

end
end IntegerMultBounds.Machine.GuardedFiniteReturnFlow
