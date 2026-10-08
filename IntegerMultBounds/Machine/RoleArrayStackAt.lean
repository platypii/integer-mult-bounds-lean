import IntegerMultBounds.Machine.RoleArrayStack
import IntegerMultBounds.Machine.InjectivePlacement

/-! Place a physical role-array stack transfer in any four distinct bank slots:
role, shared payload stack, reusable work clock, immutable volume descriptor. -/
namespace IntegerMultBounds.Machine.RoleArrayStackAt
open SharedPlacementAlphabet (setTape)
open RoleArrayStackMoves (idle)
variable {t a : ℕ}
noncomputable section

private theorem size (slot : Fin 4 → Fin t) (hi : Function.Injective slot) : 4+(t-4) = t := by
  have h := Fintype.card_le_of_injective slot hi
  simp only [Fintype.card_fin] at h
  omega

def placement (slot : Fin 4 → Fin t) (hi : Function.Injective slot) : Fin (4+(t-4)) ≃ Fin t :=
  InjectivePlacement.placement slot hi (size slot hi)

@[simp] theorem active_slot (slot : Fin 4 → Fin t) (hi : Function.Injective slot) (i : Fin 4) :
    placement slot hi (Fin.castAdd (t-4) i) = slot i := InjectivePlacement.active_slot _ _ _ _

private theorem extra_ne (slot : Fin 4 → Fin t) (hi : Function.Injective slot) (i : Fin (t-4)) (j : Fin 4) :
    placement slot hi (Fin.natAdd 4 i) ≠ slot j := by
  intro he
  have hv := congrArg Fin.val ((placement slot hi).injective (he.trans (active_slot slot hi j).symm))
  simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
  have hj := j.isLt
  omega

def Controls (slot : Fin 4 → Fin t) (bs : List Bool) (v : Tapes t a) : Prop :=
  v.head (slot 2) = 0 ∧ v.tape (slot 2) = (fun _ => blank) ∧
  v.head (slot 3) = 1 ∧ v.tape (slot 3) = CountedLoopReuseAlphabet.binary bs

private theorem active_input (slot : Fin 4 → Fin t) (hi : Function.Injective slot)
    (bs : List Bool) (v : Tapes t a) (hc : Controls slot bs v) :
    Placement.active (placement slot hi) v =
      idle (StackPop.bank (v.tape (slot 0)) (v.tape (slot 1)) (v.head (slot 0)) (v.head (slot 1))) bs := by
  obtain ⟨h0,ht0,h1,ht1⟩ := hc
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [CountedLoopReuseAlphabet.controls,StackPop.bank,h0,ht0,h1,ht1] <;> rfl

private theorem replace_idle (slot : Fin 4 → Fin t) (hi : Function.Injective slot)
    (bs : List Bool) (v : Tapes t a) (hc : Controls slot bs v)
    (f g : ℤ → Fin (a+4)) (p q : ℤ) :
    Placement.replace (placement slot hi) v (idle (StackPop.bank f g p q) bs) =
      setTape (setTape v (slot 0) f p) (slot 1) g q := by
  obtain ⟨h0,ht0,h1,ht1⟩ := hc
  apply congrArg₂ Tapes.mk
  · funext i
    obtain ⟨i,rfl⟩ := (placement slot hi).surjective i
    induction i using Fin.addCases with
    | left i =>
      change (Placement.combine _ _ _).head _ = _
      rw [Placement.combine_head_active,active_slot]
      fin_cases i <;> simp [setTape,hi.eq_iff,idle,CountedLoopReuseAlphabet.bank,CountedLoopReuseAlphabet.controls,Tapes.append,StackPop.bank,h0,h1] <;> rfl
    | right i =>
      change (Placement.combine _ _ _).head _ = _
      rw [Placement.combine_head_extra]
      simp [Placement.extra,setTape,extra_ne]
  · funext i
    obtain ⟨i,rfl⟩ := (placement slot hi).surjective i
    induction i using Fin.addCases with
    | left i =>
      change (Placement.combine _ _ _).tape _ = _
      rw [Placement.combine_tape_active,active_slot]
      fin_cases i <;> simp [setTape,hi.eq_iff,idle,CountedLoopReuseAlphabet.bank,CountedLoopReuseAlphabet.controls,Tapes.append,StackPop.bank,ht0,ht1] <;> rfl
    | right i =>
      change (Placement.combine _ _ _).tape _ = _
      rw [Placement.combine_tape_extra]
      simp [Placement.extra,setTape,extra_ne]

def pushProgram (slot : Fin 4 → Fin t) (hi : Function.Injective slot) :=
  Placement.placed (RoleArrayStack.pushProgram a) (placement slot hi)

def popProgram (slot : Fin 4 → Fin t) (hi : Function.Injective slot) :=
  Placement.placed (RoleArrayStack.popProgram a) (placement slot hi)

def pushed (slot : Fin 4 → Fin t) (v : Tapes t a) (n : ℕ) : Tapes t a :=
  setTape (setTape v (slot 0) (fun _ => blank) 0) (slot 1)
    (RoleArrayStack.parked (v.tape (slot 1)) (v.tape (slot 0)) (v.head (slot 1)) n) (v.head (slot 1)+n)

theorem push_hoare (slot : Fin 4 → Fin t) (hi : Function.Injective slot) (v : Tapes t a)
    (bs : List Bool) (n : ℕ) (hcount : Counter.value bs = n) (hc : Controls slot bs v)
    (hh : v.head (slot 0) = 0) (hr : RoleArrayStack.Supported (v.tape (slot 0)) n) :
    HoareTime (pushProgram slot hi) (fun w => w = v) (fun w => w = pushed slot v n)
      (14*n+14*bs.length+45) := by
  have hp := Placement.hoare_at (RoleArrayStack.push_hoare (v.tape (slot 0)) (v.tape (slot 1)) (v.head (slot 1)) n bs hcount hr)
    (placement slot hi) v (by rw [active_input slot hi bs v hc,hh])
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  exact replace_idle slot hi bs v hc _ _ _ _

theorem pop_hoare (slot : Fin 4 → Fin t) (hi : Function.Injective slot) (v : Tapes t a)
    (role f : ℤ → Fin (a+4)) (p : ℤ) (bs : List Bool) (n : ℕ)
    (hcount : Counter.value bs = n) (hc : Controls slot bs v)
    (hr0 : v.head (slot 0) = 0) (ht0 : v.tape (slot 0) = fun _ => blank)
    (hr1 : v.head (slot 1) = p+n) (ht1 : v.tape (slot 1) = RoleArrayStack.parked f role p n)
    (hr : RoleArrayStack.Supported role n) (hf : ∀ z, p ≤ z → z < p+n → f z = blank) :
    HoareTime (popProgram slot hi) (fun w => w = v)
      (fun w => w = setTape (setTape v (slot 0) role 0) (slot 1) f p) (14*n+14*bs.length+49) := by
  have hp := Placement.hoare_at (RoleArrayStack.pop_hoare role f p n bs hcount hr hf)
    (placement slot hi) v (by rw [active_input slot hi bs v hc,hr0,ht0,hr1,ht1])
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  exact replace_idle slot hi bs v hc _ _ _ _

end
end IntegerMultBounds.Machine.RoleArrayStackAt
