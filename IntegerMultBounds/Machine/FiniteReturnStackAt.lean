import IntegerMultBounds.Machine.FiniteReturnDispatch
import IntegerMultBounds.Machine.InjectivePlacement
import IntegerMultBounds.Machine.SharedPlacementAlphabet

/-! Put a fixed-width binary return-PC stack in any physical tape slot.
The PC encoded by push is a fixed call-site constant; pop decodes actual bits. -/
namespace IntegerMultBounds.Machine.FiniteReturnStackAt
open SharedPlacementAlphabet (setTape)
open FiniteReturnStack (Code Control address)
variable {t a k N : ℕ}
noncomputable section

def placement (slot : Fin t) : Fin (1+(t-1)) ≃ Fin t :=
  InjectivePlacement.placement (fun _ : Fin 1 => slot) (fun _ _ _ => Subsingleton.elim _ _)
    (by have := slot.isLt; omega)

@[simp] theorem placement_active (slot : Fin t) (i : Fin 1) :
    placement slot (Fin.castAdd (t-1) i) = slot := InjectivePlacement.active_slot _ _ _ _

theorem active_bank (slot : Fin t) (v : Tapes t a) :
    Placement.active (placement slot) v = FiniteReturnStack.bank (v.tape slot) (v.head slot) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp

private theorem extra_ne (slot : Fin t) (i : Fin (t-1)) :
    placement slot (Fin.natAdd 1 i) ≠ slot := by
  intro he
  have hh := placement_active slot (0 : Fin 1)
  have hv := congrArg Fin.val ((placement slot).injective (he.trans hh.symm))
  simp only [Fin.val_natAdd,Fin.val_castAdd,Fin.val_zero] at hv
  omega

theorem replace_bank (slot : Fin t) (v : Tapes t a) (f : ℤ → Fin (a+4)) (p : ℤ) :
    Placement.replace (placement slot) v (FiniteReturnStack.bank f p) = setTape v slot f p := by
  apply congrArg₂ Tapes.mk
  · funext i
    obtain ⟨i,rfl⟩ := (placement slot).surjective i
    induction i using Fin.addCases with
    | left i =>
      change (Placement.combine _ _ _).head _ = _
      rw [Placement.combine_head_active,placement_active]
      simp [FiniteReturnStack.bank]
    | right i =>
      change (Placement.combine _ _ _).head _ = _
      rw [Placement.combine_head_extra]
      simp [Placement.extra,extra_ne]
  · funext i
    obtain ⟨i,rfl⟩ := (placement slot).surjective i
    induction i using Fin.addCases with
    | left i =>
      change (Placement.combine _ _ _).tape _ = _
      rw [Placement.combine_tape_active,placement_active]
      simp [FiniteReturnStack.bank]
    | right i =>
      change (Placement.combine _ _ _).tape _ = _
      rw [Placement.combine_tape_extra]
      simp [Placement.extra,extra_ne]

def pushed (slot : Fin t) (code : Code k) (v : Tapes t a) : Tapes t a :=
  setTape v slot (FiniteReturnStack.wordPart (v.tape slot) (v.head slot) code k le_rfl) (v.head slot+k)

def pushProgram (slot : Fin t) (code : Code k) : Program t (Fintype.card (Control k)) a :=
  Placement.placed (FiniteReturnStack.push a code) (placement slot)

theorem push_hoare (slot : Fin t) (code : Code k) (v : Tapes t a) :
    HoareTime (pushProgram slot code) (fun w => w = v) (fun w => w = pushed slot code v) k := by
  have h := Placement.hoare_at (FiniteReturnStack.push_hoare code (v.tape slot) (v.head slot))
    (placement slot) v (active_bank slot v)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  exact replace_bank _ _ _ _

theorem pushed_frame (slot i : Fin t) (hi : i ≠ slot) (code : Code k) (v : Tapes t a) :
    (pushed slot code v).head i = v.head i ∧ (pushed slot code v).tape i = v.tape i := by
  simp [pushed,setTape,hi]

def dispatchProgram (hN : N ≤ 2^k) (slot : Fin t) (states : Fin N → ℕ)
    (family : ∀ pc, Program t (states pc) a) :=
  FiniteReturnDispatch.program hN (placement slot) states family

/-- The chosen continuation is selected from the terminal state of the real
binary pop machine, and the restored entire bank is passed to it. -/
theorem dispatch_hoare (hN : N ≤ 2^k) (slot : Fin t) (states : Fin N → ℕ)
    (family : ∀ pc, Program t (states pc) a) (pc : Fin N) (v : Tapes t a)
    (f : ℤ → Fin (a+4)) (p : ℤ) (B : ℕ) (post : TapePred t a)
    (hs : v.tape slot = FiniteReturnStack.wordPart f p (address hN pc) k le_rfl)
    (hh : v.head slot = p+k) (hf : ∀ j < k, f (p+j) = blank)
    (hc : HoareTime (family pc) (fun w => w = setTape v slot f p) post B) :
    HoareTime (dispatchProgram hN slot states family) (fun w => w = v) post (k+2+B) := by
  apply FiniteReturnDispatch.dispatch_hoare hN (placement slot) states family pc v f p B post
    (by rw [active_bank,hs,hh]) hf
  simpa only [replace_bank] using hc

/-- Preserve the exact final continuation state for later finite-flow edges. -/
theorem dispatch_exact (hN : N ≤ 2^k) (slot : Fin t) (states : Fin N → ℕ)
    (family : ∀ pc, Program t (states pc) a) (pc : Fin N) (v : Tapes t a)
    (f : ℤ → Fin (a+4)) (p : ℤ)
    (hs : v.tape slot = FiniteReturnStack.wordPart f p (address hN pc) k le_rfl)
    (hh : v.head slot = p+k) (hf : ∀ j < k, f (p+j) = blank)
    (steps : ℕ) (d : Config t (states pc) a)
    (hr : run (family pc) steps ((setTape v slot f p).start (family pc)) = some d)
    (halt : step (family pc) d = none) :
    run (dispatchProgram hN slot states family) (k+2+steps)
      (v.start (dispatchProgram hN slot states family)) =
      some (d.mapState (FiniteDispatch.right states pc)) ∧
    step (dispatchProgram hN slot states family) (d.mapState (FiniteDispatch.right states pc)) = none := by
  apply FiniteReturnDispatch.dispatch_exact hN (placement slot) states family pc v f p
    (by rw [active_bank,hs,hh]) hf steps d _ halt
  simpa only [replace_bank] using hr

end
end IntegerMultBounds.Machine.FiniteReturnStackAt
