import IntegerMultBounds.Machine.RoleArrayFrames
import IntegerMultBounds.Machine.RoleArrayMove

/-! Physical payload part of a recursive call: park inactive roles, move the
active role to a common child source, execute a framed child, and reverse the
moves. The child contract explicitly includes the parked stack and controls. -/
namespace IntegerMultBounds.Machine.RoleArrayCall
open RoleArrayFrames
open SharedPlacementAlphabet (setTape)
variable {t a : ℕ}

def slots (L : Layout t) (src dst : Role L) : Fin 4 → Fin t :=
  ![src.val,dst.val,L.clock,L.count]

theorem slots_injective (L : Layout t) (src dst : Role L) (hne : src ≠ dst) :
    Function.Injective (slots L src dst) := by
  have hv : src.val ≠ dst.val := fun h => hne (Subtype.ext h)
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [slots,src.property.2.1,src.property.2.2,dst.property.2.1,dst.property.2.2,L.clock_count,eq_comm]

def entered (L : Layout t) (ops : List (Role L)) (src dst : Role L) (n : ℕ) (v : Tapes t a) :=
  RoleArrayMove.moved (slots L src dst) (saved L ops n v)

noncomputable def program (L : Layout t) (ops : List (Role L)) (src dst : Role L)
    (hne : src ≠ dst) {q : ℕ} (body : Program t q a) :=
  seq (seq (seq (seq (pushProgram L ops)
    (RoleArrayMove.placedProgram (slots L src dst) (slots_injective L src dst hne))) body)
    (RoleArrayMove.placedProgram (slots L dst src) (slots_injective L dst src hne.symm)))
    (popProgram L ops)

private theorem role_frame (L : Layout t) (ops : List (Role L)) (n : ℕ) (v : Tapes t a)
    (i : Role L) (hi : i ∉ ops) :
    (saved L ops n v).head i.val = v.head i.val ∧
    (saved L ops n v).tape i.val = v.tape i.val :=
  saved_frame L ops n v i.val i.property.1 (by
    intro j hj he
    exact hi ((Subtype.ext he) ▸ hj))

private theorem controls_move (L : Layout t) (src dst : Role L) (v : Tapes t a)
    (bs : List Bool) (hc : Controls L bs v) :
    RoleArrayStackAt.Controls (slots L dst src) bs (RoleArrayMove.moved (slots L src dst) v) := by
  simpa [RoleArrayStackAt.Controls,Controls,RoleArrayMove.moved,slots,setTape,
    src.property.2.1.symm,src.property.2.2.symm,dst.property.2.1.symm,dst.property.2.2.symm] using hc

private theorem move_inverse (L : Layout t) (src dst : Role L) (hne : src ≠ dst)
    (v : Tapes t a) (hs : v.head src.val = 0)
    (hd : v.head dst.val = 0 ∧ v.tape dst.val = fun _ => blank) :
    RoleArrayMove.moved (slots L dst src) (RoleArrayMove.moved (slots L src dst) v) = v := by
  have hv : src.val ≠ dst.val := fun h => hne (Subtype.ext h)
  apply congrArg₂ Tapes.mk <;> funext i <;>
    by_cases hi : i = src.val <;> by_cases hj : i = dst.val <;>
      simp_all [RoleArrayMove.moved,slots,setTape]

/-- The exact child postcondition restores all parked arrays, old stack cells,
private slots, and shared controls. Only its active-role result may differ. -/
theorem call_hoare (L : Layout t) (ops : List (Role L)) (hu : ops.Nodup)
    (src dst : Role L) (hne : src ≠ dst) (hsrc : src ∉ ops) (hdst : dst ∉ ops)
    (v u : Tapes t a) (bs : List Bool) (n : ℕ)
    (hn : Counter.value bs = n) (hcanon : GrowingCounterData.Canonical bs) (hp : 0 < n)
    (hc : Controls L bs v) (hcu : Controls L bs u)
    (hr : ∀ i ∈ ops, v.head i = 0 ∧ RoleArrayStack.Supported (v.tape i) n)
    (hru : ∀ i ∈ ops, u.head i = 0 ∧ RoleArrayStack.Supported (u.tape i) n)
    (hf : Free L ops n u)
    (hs : v.head src.val = 0 ∧ RoleArrayStack.Supported (v.tape src.val) n)
    (hsu : u.head src.val = 0 ∧ RoleArrayStack.Supported (u.tape src.val) n)
    (hd : v.head dst.val = 0 ∧ v.tape dst.val = fun _ => blank)
    (hdu : u.head dst.val = 0 ∧ u.tape dst.val = fun _ => blank)
    {q B : ℕ} (body : Program t q a)
    (hb : HoareTime body (fun w => w = entered L ops src dst n v)
      (fun w => w = entered L ops src dst n u) B) :
    HoareTime (program L ops src dst hne body) (fun w => w = v) (fun w => w = u)
      ((180*ops.length+178)*n+B) := by
  have hsv := role_frame L ops n v src hsrc
  have hdv := role_frame L ops n v dst hdst
  have hsu' := role_frame L ops n u src hsrc
  have hdu' := role_frame L ops n u dst hdst
  have hc' := saved_controls L ops n v bs hc
  have hcu' := saved_controls L ops n u bs hcu
  have hforward := RoleArrayMove.placed_hoare_linear (slots L src dst) (slots_injective L src dst hne)
    (saved L ops n v) bs n hn hcanon hp hc' (hsv.1.trans hs.1)
    ⟨hdv.1.trans hd.1,hdv.2.trans hd.2⟩ (by simpa only [slots,Matrix.cons_val_zero,hsv.2] using hs.2)
  have hv : src.val ≠ dst.val := fun h => hne (Subtype.ext h)
  have hback := RoleArrayMove.placed_hoare_linear (slots L dst src) (slots_injective L dst src hne.symm)
    (entered L ops src dst n u) bs n hn hcanon hp (controls_move L src dst _ bs hcu')
    (by simp [entered,RoleArrayMove.moved,slots,setTape])
    (by simp [entered,RoleArrayMove.moved,slots,setTape,hv])
    (by simpa [entered,RoleArrayMove.moved,slots,setTape,hsu'.2] using hsu.2)
  have he := move_inverse L src dst hne (saved L ops n u) (hsu'.1.trans hsu.1)
    ⟨hdu'.1.trans hdu.1,hdu'.2.trans hdu.2⟩
  change RoleArrayMove.moved (slots L dst src) (entered L ops src dst n u) = _ at he
  rw [he] at hback
  have hall := (((push_hoare_linear L ops hu v bs n hn hcanon hp hc hr).seq hforward).seq hb).seq hback
  have hall' := hall.seq (pop_hoare_linear L ops hu u bs n hn hcanon hp hcu hru hf)
  exact hall'.consequence (fun _ h => h) (fun _ h => h) (by nlinarith)

/-- Specialization with the sole visible result being the transformed active
array; every other tape and head is exactly restored. -/
theorem active_result_hoare (L : Layout t) (ops : List (Role L)) (hu : ops.Nodup)
    (src dst : Role L) (hne : src ≠ dst) (hsrc : src ∉ ops) (hdst : dst ∉ ops)
    (v : Tapes t a) (out : ℤ → Fin (a+4)) (bs : List Bool) (n : ℕ)
    (hn : Counter.value bs = n) (hcanon : GrowingCounterData.Canonical bs) (hp : 0 < n)
    (hc : Controls L bs v)
    (hr : ∀ i ∈ ops, v.head i = 0 ∧ RoleArrayStack.Supported (v.tape i) n)
    (hf : Free L ops n v)
    (hs : v.head src.val = 0 ∧ RoleArrayStack.Supported (v.tape src.val) n)
    (hout : RoleArrayStack.Supported out n)
    (hd : v.head dst.val = 0 ∧ v.tape dst.val = fun _ => blank)
    {q B : ℕ} (body : Program t q a)
    (hb : HoareTime body (fun w => w = entered L ops src dst n v)
      (fun w => w = entered L ops src dst n (setTape v src.val out 0)) B) :
    HoareTime (program L ops src dst hne body) (fun w => w = v)
      (fun w => w = setTape v src.val out 0) ((180*ops.length+178)*n+B) := by
  apply call_hoare L ops hu src dst hne hsrc hdst v _ bs n hn hcanon hp hc _ hr _ _ hs _ hd _ body hb
  · simpa [Controls,setTape,src.property.2.1.symm,src.property.2.2.symm] using hc
  · intro i hi
    have hne' : i.val ≠ src.val := by
      intro he
      exact hsrc ((Subtype.ext he) ▸ hi)
    simpa [setTape,hne'] using hr i hi
  · simpa [Free,setTape,src.property.1.symm] using hf
  · simpa [setTape] using hout
  · have hne' : dst.val ≠ src.val := fun h => hne (Subtype.ext h.symm)
    simpa [setTape,hne'] using hd

end IntegerMultBounds.Machine.RoleArrayCall
