import IntegerMultBounds.Machine.CompactSpectatorStoppedLeafDispatch
import IntegerMultBounds.Machine.GuardedFiniteReturnFlow

/-! One cyclic finite table contains the physical return guard/pop, both
actual directional stopped leaves, and the remaining literal continuations.
Leaf terminal states always enter the guard; original return addresses keep
their original width and enter the continuation at offset4. -/
namespace IntegerMultBounds.Machine.CompactSpectatorStoppedLeafFlow
noncomputable section
open CompactSpectatorStoppedLeafCaller
open CompactSpectatorLeafOriginal
open CompactSpectatorLeafPlacement
open CompactSpectatorLeafGuardOriginal (Direction)
open CompactComplexRecursiveGeometry
open CompactGadgetReservationShape (Shape)
open RecursiveChildQuotientsConstant (bits)
variable {w N r : ℕ}

def leaf (dir : Direction) : Σ q,Program (total (w:=w)) q 2 :=
  ⟨_,CompactSpectatorStoppedLeafDispatch.program (w:=w) dir⟩
def states (rest : Fin N → ℕ) : Fin (N+4) → ℕ :=
  Fin.cases 4 (Fin.cases (Fintype.card (FiniteReturnStack.Control r))
    (Fin.cases (leaf (w:=w) .forward).1 (Fin.cases (leaf (w:=w) .inverse).1 rest)))
def family (stack : Fin (total (w:=w))) (rest : Fin N → ℕ)
    (blocks : ∀ pc,Program (total (w:=w)) (rest pc) 2) :
    ∀ pc,Program (total (w:=w)) (states (w:=w) (r:=r) rest pc) 2 :=
  Fin.cases (FiniteReturnGuard.program stack)
    (Fin.cases (Placement.placed (FiniteReturnStack.pop 2 r) (FiniteReturnStackAt.placement stack))
      (Fin.cases (leaf (w:=w) .forward).2 (Fin.cases (leaf (w:=w) .inverse).2 blocks)))
def next (hN : N≤2^r) (rest : Fin N → ℕ)
    (edges : ∀ pc,Fin (rest pc) → Option (Fin (N+4))) : FiniteFlow.Next (states (w:=w) (r:=r) rest) :=
  Fin.cases (fun st => if st.val=3 then some (1 : Fin (N+4)) else none)
    (Fin.cases (fun st => (FiniteReturnDispatch.select hN st).map (fun pc => pc.succ.succ.succ.succ))
      (Fin.cases (fun _ => some (0 : Fin (N+4))) (Fin.cases (fun _ => some (0 : Fin (N+4))) edges)))
def program (hN : N≤2^r) (stack : Fin (total (w:=w))) (rest : Fin N → ℕ)
    (blocks : ∀ pc,Program (total (w:=w)) (rest pc) 2)
    (edges : ∀ pc,Fin (rest pc) → Option (Fin (N+4))) (entry : Fin (N+4)) :=
  FiniteFlow.program (family stack rest blocks) (next hN rest edges) entry

def leafEmbed (rest : Fin N → ℕ) : (dir : Direction) →
    Fin (leaf (w:=w) dir).1 → Fin (Fintype.card (FiniteFlow.Control (states (w:=w) (r:=r) rest)))
  | .forward => FiniteFlow.embed (states (w:=w) (r:=r) rest) 2
  | .inverse => FiniteFlow.embed (states (w:=w) (r:=r) rest) 3

private theorem leaf_to_guard (hN : N≤2^r) (stack : Fin (total (w:=w))) (rest : Fin N → ℕ)
    (blocks : ∀ pc,Program (total (w:=w)) (rest pc) 2)
    (edges : ∀ pc,Fin (rest pc) → Option (Fin (N+4))) (entry : Fin (N+4))
    (dir : Direction) (v after : Tapes (total (w:=w)) 2) (b : ℕ)
    (hh : HoareTime (leaf (w:=w) dir).2 (fun x => x=v) (fun x => x=after) b) :
    ∃ n,n≤b+1 ∧ run (program hN stack rest blocks edges entry) n
      ((v.start (leaf (w:=w) dir).2).mapState (leafEmbed rest dir))=
        some ((after.start (FiniteReturnGuard.program stack)).mapState (FiniteFlow.embed (states (w:=w) (r:=r) rest) 0)) := by
  obtain ⟨n,c,hn,hr,hhalt,hpost⟩ := hh v rfl
  change c.tapes=after at hpost
  cases dir
  · have he : next hN rest edges 2 c.state=some 0 := rfl
    have ht := FiniteFlow.block_then_jump (family stack rest blocks) (next hN rest edges) entry 2 0 v n c hr hhalt he
    change run (program hN stack rest blocks edges entry) (n+1)
      ((v.start (leaf (w:=w) .forward).2).mapState (leafEmbed rest .forward))=
        some ((c.tapes.start (FiniteReturnGuard.program stack)).mapState
          (FiniteFlow.embed (states (w:=w) (r:=r) rest) 0)) at ht
    rw [hpost] at ht
    exact ⟨n+1,by omega,ht⟩
  · have he : next hN rest edges 3 c.state=some 0 := rfl
    have ht := FiniteFlow.block_then_jump (family stack rest blocks) (next hN rest edges) entry 3 0 v n c hr hhalt he
    change run (program hN stack rest blocks edges entry) (n+1)
      ((v.start (leaf (w:=w) .inverse).2).mapState (leafEmbed rest .inverse))=
        some ((c.tapes.start (FiniteReturnGuard.program stack)).mapState
          (FiniteFlow.embed (states (w:=w) (r:=r) rest) 0)) at ht
    rw [hpost] at ht
    exact ⟨n+1,by omega,ht⟩

theorem positive_ready (hN : N≤2^r) (stack : Fin (total (w:=w))) (rest : Fin N → ℕ)
    (blocks : ∀ pc,Program (total (w:=w)) (rest pc) 2)
    (edges : ∀ pc,Fin (rest pc) → Option (Fin (N+4))) (entry : Fin (N+4)) (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hw : ButterflySpectatorSemantics.Width rows s.bits (2^ell) q f)
    (caller : Tapes (callerCount w) 2)
    (hd : SharedBank.payload caller common=payload (CompactSpectatorLeafAxis.word f)
      (nodeValues s rows ell q rho visit hactive pair))
    (ht : caller.tape ⟨1,by unfold callerCount; omega⟩=RadixZeroFill.encodedBinary (bits (k+1)))
    (hh : caller.head ⟨1,by unfold callerCount; omega⟩=1) :
    ∃ n,n≤positivePhaseCost dir s rows ell q rho visit hactive pair+2 ∧ run (program hN stack rest blocks edges entry) n
      (((CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes) caller)).start (leaf (w:=w) dir).2).mapState
        (leafEmbed rest dir))=
      some (((CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes) (updateSource caller (CompactSpectatorLeafAxis.word
          (CompactSpectatorLeafGuardOriginal.result dir s rows ell q rho visit f))))).start
        (FiniteReturnGuard.program stack)).mapState (FiniteFlow.embed (states (w:=w) (r:=r) rest) 0)) := by
  exact leaf_to_guard hN stack rest blocks edges entry dir _ _ _ (CompactSpectatorStoppedLeafDispatch.positive_runs dir s rows ell q rho visit hactive pair hG hA hr f hw caller hd ht hh)

theorem scalar_ready (hN : N≤2^r) (stack : Fin (total (w:=w))) (rest : Fin N → ℕ)
    (blocks : ∀ pc,Program (total (w:=w)) (rest pc) 2)
    (edges : ∀ pc,Fin (rest pc) → Option (Fin (N+4))) (entry : Fin (N+4)) (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left : ℕ}
    (visit : Visit s.active left 1) (slot : Fin arity)
    (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hw : ButterflySpectatorSemantics.Width rows s.bits (2^ell) q f)
    (caller : Tapes (callerCount w) 2)
    (hd : SharedBank.payload caller common=payload (CompactSpectatorLeafAxis.word f)
      (scalarValues s rows ell q rho slot pair left))
    (ht : caller.tape ⟨1,by unfold callerCount; omega⟩=RadixZeroFill.encodedBinary (bits 0))
    (hh : caller.head ⟨1,by unfold callerCount; omega⟩=1) :
    ∃ n,n≤CompactSpectatorLeafGuardOriginal.phaseCost dir s rows ell q rho (Visit.child visit slot) arity
        (s.active-(left+slot.val+1)) pair.source.val pair.target.val+2 ∧ run (program hN stack rest blocks edges entry) n
      (((CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes) caller)).start (leaf (w:=w) dir).2).mapState
        (leafEmbed rest dir))=
      some (((CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes) (updateSource caller (CompactSpectatorLeafAxis.word
          (CompactSpectatorLeafGuardOriginal.result dir s rows ell q rho (Visit.child visit slot) f))))).start
        (FiniteReturnGuard.program stack)).mapState (FiniteFlow.embed (states (w:=w) (r:=r) rest) 0)) := by
  exact leaf_to_guard hN stack rest blocks edges entry dir _ _ _ (CompactSpectatorStoppedLeafDispatch.scalar_runs dir s rows ell q rho visit slot pair hG hA hr f hw caller hd ht hh)

end
end IntegerMultBounds.Machine.CompactSpectatorStoppedLeafFlow
