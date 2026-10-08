import IntegerMultBounds.Machine.FiniteFlow
import IntegerMultBounds.Machine.FiniteReturnDispatch

/-! A cyclic fixed controller with a real binary-pop block at PC zero and fixed
continuations at successor PCs. Continuations may jump to any block, including
the same recursive entry or the shared pop block. No recursion depth is compiled
into the machine. This is control plumbing, not a recursive algorithm proof. -/
namespace IntegerMultBounds.Machine.FiniteReturnFlow
variable {k N t u a : ℕ}
noncomputable section

def states (rest : Fin N → ℕ) : Fin (N+1) → ℕ :=
  Fin.cases (Fintype.card (FiniteReturnStack.Control k)) rest

def family (e : Fin (1+u) ≃ Fin t) (rest : Fin N → ℕ)
    (blocks : ∀ pc, Program t (rest pc) a) : ∀ pc, Program t (states (k := k) rest pc) a :=
  Fin.cases (Placement.placed (FiniteReturnStack.pop a k) e) blocks

/-- Pop chooses a successor block from the physically decoded address; every
other terminal state uses its fixed caller-supplied cyclic edge table. -/
def next (hN : N ≤ 2^k) (rest : Fin N → ℕ)
    (edges : ∀ pc, Fin (rest pc) → Option (Fin (N+1))) : FiniteFlow.Next (states (k := k) rest) :=
  Fin.cases (fun st => (FiniteReturnDispatch.select hN st).map Fin.succ) edges

def program (hN : N ≤ 2^k) (e : Fin (1+u) ≃ Fin t) (rest : Fin N → ℕ)
    (blocks : ∀ pc, Program t (rest pc) a)
    (edges : ∀ pc, Fin (rest pc) → Option (Fin (N+1))) (entry : Fin (N+1)) :=
  FiniteFlow.program (family e rest blocks) (next hN rest edges) entry

/-- The actual binary stack chooses the next cyclic block in k+2 transitions,
leaving the complete other bank intact and erasing only the popped frame. -/
theorem pop_jump (hN : N ≤ 2^k) (e : Fin (1+u) ≃ Fin t) (rest : Fin N → ℕ)
    (blocks : ∀ pc, Program t (rest pc) a)
    (edges : ∀ pc, Fin (rest pc) → Option (Fin (N+1))) (entry : Fin (N+1)) (pc : Fin N)
    (v : Tapes t a) (f : ℤ → Fin (a+4)) (p : ℤ)
    (hv : Placement.active e v = FiniteReturnStack.bank
      (FiniteReturnStack.wordPart f p (FiniteReturnStack.address hN pc) k le_rfl) (p+k))
    (hf : ∀ j < k, f (p+j) = blank) :
    run (program hN e rest blocks edges entry) (k+2)
      ((v.start (family (k := k) e rest blocks 0)).mapState (FiniteFlow.embed (states rest) 0)) =
      some (((Placement.replace e v (FiniteReturnStack.bank f p)).start (blocks pc)).mapState
        (FiniteFlow.embed (states (k := k) rest) pc.succ)) := by
  obtain ⟨hr,hh⟩ := FiniteReturnStack.pop_exact (FiniteReturnStack.address hN pc) f p hf
  let c := FiniteReturnStack.cfg (.inr (0,FiniteReturnStack.address hN pc)) f p
  have hr' : run (FiniteReturnStack.pop a k) (k+1)
      ((Placement.active e v).start (FiniteReturnStack.pop a k)) = some c := by
    rw [hv]
    exact hr
  have he : next hN rest edges 0 (Placement.result e v c).state = some pc.succ := by
    change (FiniteReturnDispatch.select hN (FiniteReturnStack.encode k
      (.inr (0,FiniteReturnStack.address hN pc)))).map Fin.succ = _
    rw [FiniteReturnDispatch.select_return]
    rfl
  exact FiniteFlow.block_then_jump (family e rest blocks) (next hN rest edges)
    entry 0 pc.succ v (k+1) (Placement.result e v c)
    (Placement.placed_run _ e v hr') (Placement.placed_halt _ e v hh) he

/-- Any fixed continuation may re-enter any PC, including its own entry or
zero (the actual pop block), without changing machine size or allocating code. -/
theorem continuation_jump (hN : N ≤ 2^k) (e : Fin (1+u) ≃ Fin t) (rest : Fin N → ℕ)
    (blocks : ∀ pc, Program t (rest pc) a)
    (edges : ∀ pc, Fin (rest pc) → Option (Fin (N+1))) (entry : Fin (N+1))
    (pc : Fin N) (dest : Fin (N+1)) (v : Tapes t a) (n : ℕ) (c : Config t (rest pc) a)
    (hr : run (blocks pc) n (v.start (blocks pc)) = some c)
    (hh : step (blocks pc) c = none) (he : edges pc c.state = some dest) :
    run (program hN e rest blocks edges entry) (n+1)
      ((v.start (blocks pc)).mapState (FiniteFlow.embed (states (k := k) rest) pc.succ)) =
      some ((c.tapes.start (family e rest blocks dest)).mapState (FiniteFlow.embed (states rest) dest)) :=
  FiniteFlow.block_then_jump (family e rest blocks) (next hN rest edges)
    entry pc.succ dest v n c hr hh he

end
end IntegerMultBounds.Machine.FiniteReturnFlow
