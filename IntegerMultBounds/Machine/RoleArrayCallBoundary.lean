import IntegerMultBounds.Machine.RoleArrayCall

/-! Separate physical entry and return blocks for a cyclic recursive controller.
Entry parks inactive arrays and moves the selected array to the common child
source. Return moves its result back and recovers the parked frame. No child
program is embedded in either block; fixed FiniteFlow edges may connect them. -/
namespace IntegerMultBounds.Machine.RoleArrayCallBoundary
open RoleArrayFrames
open RoleArrayCall (entered)
open SharedPlacementAlphabet (setTape)
variable {t a : ℕ}
noncomputable section

def entryProgram (L : Layout t) (ops : List (Role L)) (src dst : Role L) (hne : src ≠ dst) :=
  seq (pushProgram (a := a) L ops) (RoleArrayMove.placedProgram (RoleArrayCall.slots L src dst) (RoleArrayCall.slots_injective L src dst hne))

def returnProgram (L : Layout t) (ops : List (Role L)) (src dst : Role L) (hne : src ≠ dst) :=
  seq (RoleArrayMove.placedProgram (a := a) (RoleArrayCall.slots L dst src) (RoleArrayCall.slots_injective L dst src hne.symm)) (popProgram L ops)

private theorem role_frame (L : Layout t) (ops : List (Role L)) (n : ℕ) (v : Tapes t a)
    (i : Role L) (hi : i ∉ ops) :
    (saved L ops n v).head i.val = v.head i.val ∧
    (saved L ops n v).tape i.val = v.tape i.val :=
  saved_frame L ops n v i.val i.property.1 (by
    intro j hj he
    exact hi ((Subtype.ext he) ▸ hj))

/-- All inactive roles are blank at origin in the exact entered bank; the
payload stack contains their arrays, and all remaining slots are framed. -/
theorem entry_hoare (L : Layout t) (ops : List (Role L)) (hu : ops.Nodup)
    (src dst : Role L) (hne : src ≠ dst) (hsrc : src ∉ ops) (hdst : dst ∉ ops)
    (v : Tapes t a) (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n)
    (hcanon : GrowingCounterData.Canonical bs) (hp : 0 < n) (hc : Controls L bs v)
    (hr : ∀ i ∈ ops, v.head i = 0 ∧ RoleArrayStack.Supported (v.tape i) n)
    (hs : v.head src.val = 0 ∧ RoleArrayStack.Supported (v.tape src.val) n)
    (hd : v.head dst.val = 0 ∧ v.tape dst.val = fun _ => blank) :
    HoareTime (entryProgram L ops src dst hne) (fun w => w = v)
      (fun w => w = entered L ops src dst n v) ((88*ops.length+88)*n) := by
  have hsrc' := role_frame L ops n v src hsrc
  have hdst' := role_frame L ops n v dst hdst
  have hc' := saved_controls L ops n v bs hc
  have hm := RoleArrayMove.placed_hoare_linear (RoleArrayCall.slots L src dst) (RoleArrayCall.slots_injective L src dst hne)
    (saved L ops n v) bs n hn hcanon hp hc' (hsrc'.1.trans hs.1)
    ⟨hdst'.1.trans hd.1,hdst'.2.trans hd.2⟩
    (by simpa only [RoleArrayCall.slots,Matrix.cons_val_zero,hsrc'.2] using hs.2)
  exact ((push_hoare_linear L ops hu v bs n hn hcanon hp hc hr).seq hm).consequence
    (fun _ h => h) (fun _ h => h) (by nlinarith)

private theorem entered_controls (L : Layout t) (ops : List (Role L)) (src dst : Role L)
    (n : ℕ) (v : Tapes t a) (bs : List Bool) (hc : Controls L bs v) :
    RoleArrayStackAt.Controls (RoleArrayCall.slots L dst src) bs (entered L ops src dst n v) := by
  have h := saved_controls L ops n v bs hc
  simpa [RoleArrayStackAt.Controls,Controls,entered,RoleArrayMove.moved,RoleArrayCall.slots,setTape,
    src.property.2.1.symm,src.property.2.2.symm,dst.property.2.1.symm,dst.property.2.2.symm] using h

private theorem move_inverse (L : Layout t) (src dst : Role L) (hne : src ≠ dst)
    (v : Tapes t a) (hs : v.head src.val = 0)
    (hd : v.head dst.val = 0 ∧ v.tape dst.val = fun _ => blank) :
    RoleArrayMove.moved (RoleArrayCall.slots L dst src) (RoleArrayMove.moved (RoleArrayCall.slots L src dst) v) = v := by
  have hv : src.val ≠ dst.val := fun h => hne (Subtype.ext h)
  apply congrArg₂ Tapes.mk <;> funext i <;>
    by_cases hi : i = src.val <;> by_cases hj : i = dst.val <;>
      simp_all [RoleArrayMove.moved,RoleArrayCall.slots,setTape]

/-- This block accepts the exact saved frame with the child's result in the
common source. It restores the full result bank, including older stack cells. -/
theorem return_hoare (L : Layout t) (ops : List (Role L)) (hu : ops.Nodup)
    (src dst : Role L) (hne : src ≠ dst) (hsrc : src ∉ ops) (hdst : dst ∉ ops)
    (v : Tapes t a) (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n)
    (hcanon : GrowingCounterData.Canonical bs) (hp : 0 < n) (hc : Controls L bs v)
    (hr : ∀ i ∈ ops, v.head i = 0 ∧ RoleArrayStack.Supported (v.tape i) n)
    (hf : Free L ops n v)
    (hs : v.head src.val = 0 ∧ RoleArrayStack.Supported (v.tape src.val) n)
    (hd : v.head dst.val = 0 ∧ v.tape dst.val = fun _ => blank) :
    HoareTime (returnProgram L ops src dst hne) (fun w => w = entered L ops src dst n v)
      (fun w => w = v) ((92*ops.length+88)*n) := by
  have hsrc' := role_frame L ops n v src hsrc
  have hdst' := role_frame L ops n v dst hdst
  have hv : src.val ≠ dst.val := fun h => hne (Subtype.ext h)
  have hm := RoleArrayMove.placed_hoare_linear (RoleArrayCall.slots L dst src) (RoleArrayCall.slots_injective L dst src hne.symm)
    (entered L ops src dst n v) bs n hn hcanon hp (entered_controls L ops src dst n v bs hc)
    (by simp [entered,RoleArrayMove.moved,RoleArrayCall.slots,setTape])
    (by simp [entered,RoleArrayMove.moved,RoleArrayCall.slots,setTape,hv])
    (by simpa [entered,RoleArrayMove.moved,RoleArrayCall.slots,setTape,hsrc'.2] using hs.2)
  have he := move_inverse L src dst hne (saved L ops n v) (hsrc'.1.trans hs.1)
    ⟨hdst'.1.trans hd.1,hdst'.2.trans hd.2⟩
  change RoleArrayMove.moved (RoleArrayCall.slots L dst src) (entered L ops src dst n v) = _ at he
  rw [he] at hm
  exact (hm.seq (pop_hoare_linear L ops hu v bs n hn hcanon hp hc hr hf)).consequence
    (fun _ h => h) (fun _ h => h) (by nlinarith)

/-- The common child source contains exactly the selected input array, and the
old selected slot is physically vacated. -/
theorem entered_payload (L : Layout t) (ops : List (Role L)) (src dst : Role L)
    (hne : src ≠ dst) (hsrc : src ∉ ops) (n : ℕ) (v : Tapes t a) :
    (entered L ops src dst n v).head src.val = 0 ∧
    (entered L ops src dst n v).tape src.val = (fun _ => blank) ∧
    (entered L ops src dst n v).head dst.val = 0 ∧
    (entered L ops src dst n v).tape dst.val = v.tape src.val := by
  have hv : src.val ≠ dst.val := fun h => hne (Subtype.ext h)
  have hf := role_frame L ops n v src hsrc
  simp [entered,RoleArrayMove.moved,RoleArrayCall.slots,setTape,hv,hf.2]

end
end IntegerMultBounds.Machine.RoleArrayCallBoundary
