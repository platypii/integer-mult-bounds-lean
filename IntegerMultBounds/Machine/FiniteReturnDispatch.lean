import IntegerMultBounds.Machine.FiniteReturnStack
import IntegerMultBounds.Machine.FiniteDispatch
import IntegerMultBounds.Machine.Placement

/-! Actual binary return-stack decoding followed by a fixed finite family of
same-bank continuations. The stack's physical placement, PC width, and family
are fixed; runtime recursion depth affects only the stack's head position. -/
namespace IntegerMultBounds.Machine.FiniteReturnDispatch
open FiniteReturnStack (Code Control encode address)
variable {k N t u a : ℕ}
noncomputable section

/-- The table recognizes precisely the finite PC halt states produced by pop. -/
def select (hN : N ≤ 2^k) (st : Fin (Fintype.card (Control k))) : Option (Fin N) :=
  if h : ∃ pc : Fin N, encode k (.inr (0,address hN pc)) = st then some h.choose else none

theorem select_return (hN : N ≤ 2^k) (pc : Fin N) :
    select hN (encode k (.inr (0,address hN pc))) = some pc := by
  unfold select
  split_ifs with h
  · exact congrArg some (FiniteReturnStack.return_state_injective hN h.choose_spec)
  · exact (h ⟨pc,rfl⟩).elim

/-- One fixed dispatcher contains the pop machine and every continuation. -/
def program (hN : N ≤ 2^k) (e : Fin (1+u) ≃ Fin t) (states : Fin N → ℕ)
    (family : ∀ pc, Program t (states pc) a) :=
  FiniteDispatch.program (Placement.placed (FiniteReturnStack.pop a k) e) states family (select hN)

/-- The binary stack is physically popped and erased before the selected
continuation runs. Older stack cells and every other tape are exactly framed.
The cost includes k+1 decoding steps and the one-step branch into the family. -/
theorem dispatch_hoare (hN : N ≤ 2^k) (e : Fin (1+u) ≃ Fin t) (states : Fin N → ℕ)
    (family : ∀ pc, Program t (states pc) a) (pc : Fin N)
    (v : Tapes t a) (f : ℤ → Fin (a+4)) (p : ℤ) (B : ℕ) (post : TapePred t a)
    (hv : Placement.active e v =
      FiniteReturnStack.bank (FiniteReturnStack.wordPart f p (address hN pc) k le_rfl) (p+k))
    (hf : ∀ j < k, f (p+j) = blank)
    (hc : HoareTime (family pc)
      (fun w => w = Placement.replace e v (FiniteReturnStack.bank f p)) post B) :
    HoareTime (program hN e states family) (fun w => w = v) post (k+2+B) := by
  obtain ⟨hr,hh⟩ := FiniteReturnStack.pop_exact (address hN pc) f p hf
  let c := FiniteReturnStack.cfg (.inr (0,address hN pc)) f p
  have hr' : run (FiniteReturnStack.pop a k) (k+1) ((Placement.active e v).start (FiniteReturnStack.pop a k)) =
      some c := by rw [hv]; exact hr
  have hwhole := Placement.placed_run (FiniteReturnStack.pop a k) e v hr'
  have hhalt := Placement.placed_halt (FiniteReturnStack.pop a k) e v hh
  have hs : select hN (Placement.result e v c).state = some pc := select_return hN pc
  have hcont : HoareTime (family pc) (fun w => w = (Placement.result e v c).tapes) post B := hc
  exact FiniteDispatch.hoare_selected (Placement.placed (FiniteReturnStack.pop a k) e)
    states family (select hN) v (Placement.result e v c) pc (k+1) B post hwhole hhalt hs hcont

/-- Exact run and terminal continuation state, for composition with subsequent
finite controller branches rather than just tape-level Hoare contracts. -/
theorem dispatch_exact (hN : N ≤ 2^k) (e : Fin (1+u) ≃ Fin t) (states : Fin N → ℕ)
    (family : ∀ pc, Program t (states pc) a) (pc : Fin N)
    (v : Tapes t a) (f : ℤ → Fin (a+4)) (p : ℤ)
    (hv : Placement.active e v =
      FiniteReturnStack.bank (FiniteReturnStack.wordPart f p (address hN pc) k le_rfl) (p+k))
    (hf : ∀ j < k, f (p+j) = blank) (m : ℕ) (d : Config t (states pc) a)
    (hrun : run (family pc) m ((Placement.replace e v (FiniteReturnStack.bank f p)).start (family pc)) = some d)
    (hhalt : step (family pc) d = none) :
    run (program hN e states family) (k+2+m) (v.start (program hN e states family)) =
      some (d.mapState (FiniteDispatch.right states pc)) ∧
    step (program hN e states family) (d.mapState (FiniteDispatch.right states pc)) = none := by
  obtain ⟨hr,hh⟩ := FiniteReturnStack.pop_exact (address hN pc) f p hf
  let c := FiniteReturnStack.cfg (.inr (0,address hN pc)) f p
  have hr' : run (FiniteReturnStack.pop a k) (k+1) ((Placement.active e v).start (FiniteReturnStack.pop a k)) =
      some c := by rw [hv]; exact hr
  refine ⟨?_,FiniteDispatch.halt_selected _ states family (select hN) pc d hhalt⟩
  exact FiniteDispatch.run_selected (Placement.placed (FiniteReturnStack.pop a k) e)
    states family (select hN) v (Placement.result e v c) pc d (k+1) m
    (Placement.placed_run _ e v hr') (Placement.placed_halt _ e v hh) (select_return hN pc) hrun

end
end IntegerMultBounds.Machine.FiniteReturnDispatch
