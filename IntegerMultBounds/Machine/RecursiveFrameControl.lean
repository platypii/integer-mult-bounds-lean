import IntegerMultBounds.Machine.BinaryDescriptorFrames
import IntegerMultBounds.Machine.FiniteReturnStackAt

/-! Concrete descriptor-frame and finite return-PC stack wiring. Calls save
runtime descriptors and a fixed call-site PC; returns restore descriptors then
branch on the physically decoded PC. Any intervening child body remains an
explicit contract here: this file does not assert a recursive multiplier. -/
namespace IntegerMultBounds.Machine.RecursiveFrameControl
open BinaryDescriptorFrames
open FiniteReturnStack (Code Control address)
open SharedPlacementAlphabet (setTape)
variable {t a k N b : ℕ}
noncomputable section

/-- Push the descriptor fields and then the return address on their own tapes. -/
def callProgram (stack : Fin t) (ops : List (Slot stack)) (pcStack : Fin t) (code : Code k) :
    Program t (pushStates ops+Fintype.card (Control k)) a :=
  seq (pushProgram stack ops) (FiniteReturnStackAt.pushProgram pcStack code)

theorem call_hoare (stack : Fin t) (ops : List (Slot stack)) (pcStack : Fin t) (code : Code k)
    (xs : Fin t → List Bool) (v : Tapes t a)
    (hs : ∀ i ∈ ops, v.head i = 1 ∧ v.tape i = BinaryDescriptorStack.descriptor (xs i)) :
    HoareTime (callProgram stack ops pcStack code) (fun w => w = v)
      (fun w => w = FiniteReturnStackAt.pushed pcStack code (saved stack ops xs v)) (cost ops xs+1+k) :=
  (BinaryDescriptorFrames.push_hoare stack ops xs v hs).seq
    (FiniteReturnStackAt.push_hoare pcStack code (saved stack ops xs v))

/-- The separate PC push leaves the entire saved descriptor stack intact. -/
theorem call_saved_stack (stack : Fin t) (ops : List (Slot stack)) (pcStack : Fin t)
    (hsep : stack ≠ pcStack) (code : Code k) (xs : Fin t → List Bool) (v : Tapes t a) :
    (FiniteReturnStackAt.pushed pcStack code (saved stack ops xs v)).head stack =
      v.head stack+span ops xs ∧
    (FiniteReturnStackAt.pushed pcStack code (saved stack ops xs v)).tape stack =
      (saved stack ops xs v).tape stack := by
  have h := FiniteReturnStackAt.pushed_frame pcStack stack hsep code (saved stack ops xs v)
  exact ⟨h.1.trans (saved_head stack ops xs v),h.2⟩

/-- Neither stack operation touches any other tape or head. -/
theorem call_frame (stack : Fin t) (ops : List (Slot stack)) (pcStack i : Fin t)
    (hs : i ≠ stack) (hp : i ≠ pcStack) (code : Code k) (xs : Fin t → List Bool) (v : Tapes t a) :
    (FiniteReturnStackAt.pushed pcStack code (saved stack ops xs v)).head i = v.head i ∧
    (FiniteReturnStackAt.pushed pcStack code (saved stack ops xs v)).tape i = v.tape i := by
  have h := FiniteReturnStackAt.pushed_frame pcStack i hp code (saved stack ops xs v)
  have h' := saved_frame stack ops xs v i hs
  exact ⟨h.1.trans h'.1,h.2.trans h'.2⟩

/-- Restore runtime fields before decoding the binary PC and running its
selected fixed continuation. No decoded address is lost in a Hoare abstraction. -/
def returnProgram (hN : N ≤ 2^k) (stack : Fin t) (ops : List (Slot stack))
    (pcStack : Fin t) (states : Fin N → ℕ) (family : ∀ pc, Program t (states pc) a) :=
  seq (popProgram stack ops) (FiniteReturnStackAt.dispatchProgram hN pcStack states family)

theorem return_hoare (hN : N ≤ 2^k) (stack : Fin t) (ops : List (Slot stack)) (hu : ops.Nodup)
    (pcStack : Fin t) (hslots : ∀ i ∈ ops, pcStack ≠ i.val)
    (states : Fin N → ℕ) (family : ∀ pc, Program t (states pc) a) (pc : Fin N)
    (xs : Fin t → List Bool) (v : Tapes t a) (f : ℤ → Fin (a+4)) (p : ℤ)
    (hd : ∀ i ∈ ops, v.head i = 0 ∧ v.tape i = fun _ => blank) (hfree : Free stack ops xs v)
    (hpct : v.tape pcStack = FiniteReturnStack.wordPart f p (address hN pc) k le_rfl)
    (hpch : v.head pcStack = p+k) (hpcfree : ∀ j < k, f (p+j) = blank)
    (B : ℕ) (post : TapePred t a)
    (hc : HoareTime (family pc) (fun w => w = setTape (restored ops xs v) pcStack f p) post B) :
    HoareTime (returnProgram hN stack ops pcStack states family)
      (fun w => w = saved stack ops xs v) post (cost ops xs+1+(k+2+B)) := by
  have hf := restored_frame ops xs v pcStack hslots
  exact (BinaryDescriptorFrames.pop_hoare stack ops hu xs v hd hfree).seq
    (FiniteReturnStackAt.dispatch_hoare hN pcStack states family pc (restored ops xs v) f p B post
      (hf.2.trans hpct) (hf.1.trans hpch) hpcfree hc)

/-- The exact continuation terminal state survives both the return decoder
and the preceding descriptor-pop program, ready for a finite-flow edge. -/
theorem return_exact (hN : N ≤ 2^k) (stack : Fin t) (ops : List (Slot stack)) (hu : ops.Nodup)
    (pcStack : Fin t) (hslots : ∀ i ∈ ops, pcStack ≠ i.val)
    (states : Fin N → ℕ) (family : ∀ pc, Program t (states pc) a) (pc : Fin N)
    (xs : Fin t → List Bool) (v : Tapes t a) (f : ℤ → Fin (a+4)) (p : ℤ)
    (hd : ∀ i ∈ ops, v.head i = 0 ∧ v.tape i = fun _ => blank) (hfree : Free stack ops xs v)
    (hpct : v.tape pcStack = FiniteReturnStack.wordPart f p (address hN pc) k le_rfl)
    (hpch : v.head pcStack = p+k) (hpcfree : ∀ j < k, f (p+j) = blank)
    (steps : ℕ) (d : Config t (states pc) a)
    (hr : run (family pc) steps ((setTape (restored ops xs v) pcStack f p).start (family pc)) = some d)
    (halt : step (family pc) d = none) :
    ∃ prefixSteps, prefixSteps ≤ cost ops xs ∧
      run (returnProgram hN stack ops pcStack states family) (prefixSteps+1+(k+2+steps))
        ((saved stack ops xs v).start (returnProgram hN stack ops pcStack states family)) =
        some ((d.mapState (FiniteDispatch.right states pc)).mapState (Fin.natAdd (popStates ops))) ∧
      step (returnProgram hN stack ops pcStack states family)
        ((d.mapState (FiniteDispatch.right states pc)).mapState (Fin.natAdd (popStates ops))) = none := by
  obtain ⟨prefixSteps,c,hbound,hfirst,hhalt,hout⟩ := BinaryDescriptorFrames.pop_hoare stack ops hu xs v hd hfree _ rfl
  have hf := restored_frame ops xs v pcStack hslots
  obtain ⟨hrun,hstop⟩ := FiniteReturnStackAt.dispatch_exact hN pcStack states family pc (restored ops xs v) f p
    (hf.2.trans hpct) (hf.1.trans hpch) hpcfree steps d hr halt
  refine ⟨prefixSteps,hbound,?_,seq_halt_right _ _ hstop⟩
  have hm : (restored ops xs v).start (FiniteReturnStackAt.dispatchProgram hN pcStack states family) =
      {state := (FiniteReturnStackAt.dispatchProgram hN pcStack states family).start,head := c.head,tape := c.tape} := by
    rw [← hout]; rfl
  rw [hm] at hrun
  exact seq_run _ _ hfirst hhalt hrun

/-- A literal call/body/return assembly. The supplied body's contract must
prove the recursive work and the exact saved-stack/blank-destination invariant. -/
def withBodyProgram (hN : N ≤ 2^k) (stack : Fin t) (src dst : List (Slot stack))
    (pcStack : Fin t) (pc : Fin N) (body : Program t b a)
    (states : Fin N → ℕ) (family : ∀ pc, Program t (states pc) a) :=
  seq (seq (callProgram stack src pcStack (address hN pc)) body)
    (returnProgram hN stack dst pcStack states family)

theorem withBody_hoare (hN : N ≤ 2^k) (stack : Fin t) (src dst : List (Slot stack)) (hu : dst.Nodup)
    (pcStack : Fin t) (hslots : ∀ i ∈ dst, pcStack ≠ i.val) (pc : Fin N)
    (body : Program t b a) (states : Fin N → ℕ) (family : ∀ pc, Program t (states pc) a)
    (xs : Fin t → List Bool) (v u : Tapes t a) (f : ℤ → Fin (a+4)) (p : ℤ)
    (hs : ∀ i ∈ src, v.head i = 1 ∧ v.tape i = BinaryDescriptorStack.descriptor (xs i))
    (hd : ∀ i ∈ dst, u.head i = 0 ∧ u.tape i = fun _ => blank) (hfree : Free stack dst xs u)
    (hpct : u.tape pcStack = FiniteReturnStack.wordPart f p (address hN pc) k le_rfl)
    (hpch : u.head pcStack = p+k) (hpcfree : ∀ j < k, f (p+j) = blank)
    (bodyCost continuationCost : ℕ) (post : TapePred t a)
    (hbody : HoareTime body
      (fun w => w = FiniteReturnStackAt.pushed pcStack (address hN pc) (saved stack src xs v))
      (fun w => w = saved stack dst xs u) bodyCost)
    (hc : HoareTime (family pc) (fun w => w = setTape (restored dst xs u) pcStack f p) post continuationCost) :
    HoareTime (withBodyProgram hN stack src dst pcStack pc body states family) (fun w => w = v) post
      (cost src xs+cost dst xs+2*k+bodyCost+continuationCost+6) := by
  have h := ((call_hoare stack src pcStack (address hN pc) xs v hs).seq hbody).seq
    (return_hoare hN stack dst hu pcStack hslots states family pc xs u f p hd hfree hpct hpch hpcfree continuationCost post hc)
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.RecursiveFrameControl
