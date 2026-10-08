import IntegerMultBounds.Machine.RoleArrayStackAt

/-! Destructive arbitrary-symbol array transfer between two origin slots.
Both payload heads and the reusable clock are physically reset to zero. -/
namespace IntegerMultBounds.Machine.RoleArrayMove
open RoleArrayStackMoves
open SharedPlacementAlphabet (setTape)
variable {t a : ℕ}
noncomputable section

def program (a : ℕ) :=
  seq (seq (seq (initializeProgram a) StackPush.program) (moveProgram RoleArrayStack.bothLeft)) (cleanupProgram a)

private theorem pushed (role : ℤ → Fin (a+4)) (n : ℕ) (hr : RoleArrayStack.Supported role n) :
    StackPush.result (StackPop.bank role (fun _ => blank) 0 0) n = StackPop.bank (fun _ => blank) role n n := by
  apply congrArg₂ Tapes.mk
  · funext i
    change (StackPush.result (StackPop.bank role (fun _ => blank) 0 0) n).head i = _
    rw [StackPush.heads]; fin_cases i <;> simp [StackPop.bank]
  · funext i z; fin_cases i
    · change (StackPush.result (StackPop.bank role (fun _ => blank) 0 0) n).tape 0 z = blank
      rw [StackPush.source]
      simp only [StackPop.bank,ite_true,zero_add]
      split_ifs with hz
      · rfl
      · exact hr z (by omega)
    · change (StackPush.result (StackPop.bank role (fun _ => blank) 0 0) n).tape 1 z = role z
      rw [StackPush.destination]
      simp only [StackPop.bank,show (1 : Fin 2) ≠ 0 by decide,ite_false,ite_true,zero_add,sub_zero]
      split_ifs with hz
      · rfl
      · exact (hr z (by omega)).symm

theorem move_hoare (role : ℤ → Fin (a+4)) (bs : List Bool) (n : ℕ)
    (hc : Counter.value bs = n) (hr : RoleArrayStack.Supported role n) :
    HoareTime (program a) (fun v => v = idle (StackPop.bank role (fun _ => blank) 0 0) bs)
      (fun v => v = idle (StackPop.bank (fun _ => blank) role 0 0) bs) (14*n+14*bs.length+45) := by
  have hp := StackPush.push_hoare (StackPop.bank role (fun _ => blank) 0 0) bs n hc
  rw [pushed role n hr] at hp
  have hm := RoleArrayStackMoves.move_hoare (StackPop.bank (fun _ => blank) role n n) RoleArrayStack.bothLeft bs n hc
  have he : shifted (StackPop.bank (fun _ => blank) role n n) RoleArrayStack.bothLeft n = StackPop.bank (fun _ => blank) role 0 0 := by
    apply congrArg₂ Tapes.mk
    · funext i; fin_cases i <;> simp [StackPop.bank,RoleArrayStack.bothLeft,Move.offset]
    · rfl
  rw [he] at hm
  exact ((((initialize_hoare _ bs).seq hp).seq hm).seq (cleanup_hoare _ bs)).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

def placedProgram (slot : Fin 4 → Fin t) (hi : Function.Injective slot) :=
  Placement.placed (program a) (RoleArrayStackAt.placement slot hi)

def moved (slot : Fin 4 → Fin t) (v : Tapes t a) : Tapes t a :=
  setTape (setTape v (slot 0) (fun _ => blank) 0) (slot 1) (v.tape (slot 0)) 0

private theorem extra_ne (slot : Fin 4 → Fin t) (hi : Function.Injective slot) (i : Fin (t-4)) (j : Fin 4) :
    RoleArrayStackAt.placement slot hi (Fin.natAdd 4 i) ≠ slot j := by
  intro he
  have hv := congrArg Fin.val ((RoleArrayStackAt.placement slot hi).injective
    (he.trans (RoleArrayStackAt.active_slot slot hi j).symm))
  simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
  have hj := j.isLt
  omega

theorem placed_hoare (slot : Fin 4 → Fin t) (hi : Function.Injective slot) (v : Tapes t a)
    (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n) (hc : RoleArrayStackAt.Controls slot bs v)
    (hs : v.head (slot 0) = 0) (hd : v.head (slot 1) = 0 ∧ v.tape (slot 1) = fun _ => blank)
    (hr : RoleArrayStack.Supported (v.tape (slot 0)) n) :
    HoareTime (placedProgram slot hi) (fun w => w = v) (fun w => w = moved slot v) (14*n+14*bs.length+45) := by
  obtain ⟨h0,ht0,h1,ht1⟩ := hc
  have ha : Placement.active (RoleArrayStackAt.placement slot hi) v = idle (StackPop.bank (v.tape (slot 0)) (fun _ => blank) 0 0) bs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [CountedLoopReuseAlphabet.controls,StackPop.bank,hs,hd.1,hd.2,h0,ht0,h1,ht1] <;> rfl
  have hp := Placement.hoare_at (move_hoare (v.tape (slot 0)) bs n hn hr) (RoleArrayStackAt.placement slot hi) v ha
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  apply congrArg₂ Tapes.mk
  · funext i
    obtain ⟨i,rfl⟩ := (RoleArrayStackAt.placement slot hi).surjective i
    induction i using Fin.addCases with
    | left i =>
      change (Placement.combine _ _ _).head _ = _
      rw [Placement.combine_head_active,RoleArrayStackAt.active_slot]
      fin_cases i <;> simp [setTape,hi.eq_iff,idle,CountedLoopReuseAlphabet.bank,CountedLoopReuseAlphabet.controls,Tapes.append,StackPop.bank,h0,h1] <;> rfl
    | right i =>
      change (Placement.combine _ _ _).head _ = _
      rw [Placement.combine_head_extra]
      simp [Placement.extra,setTape,extra_ne]
  · funext i
    obtain ⟨i,rfl⟩ := (RoleArrayStackAt.placement slot hi).surjective i
    induction i using Fin.addCases with
    | left i =>
      change (Placement.combine _ _ _).tape _ = _
      rw [Placement.combine_tape_active,RoleArrayStackAt.active_slot]
      fin_cases i <;> simp [setTape,hi.eq_iff,idle,CountedLoopReuseAlphabet.bank,CountedLoopReuseAlphabet.controls,Tapes.append,StackPop.bank,ht0,ht1] <;> rfl
    | right i =>
      change (Placement.combine _ _ _).tape _ = _
      rw [Placement.combine_tape_extra]
      simp [Placement.extra,setTape,extra_ne]

theorem placed_hoare_linear (slot : Fin 4 → Fin t) (hi : Function.Injective slot) (v : Tapes t a)
    (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n) (hcanon : GrowingCounterData.Canonical bs) (hp : 0 < n)
    (hc : RoleArrayStackAt.Controls slot bs v) (hs : v.head (slot 0) = 0)
    (hd : v.head (slot 1) = 0 ∧ v.tape (slot 1) = fun _ => blank)
    (hr : RoleArrayStack.Supported (v.tape (slot 0)) n) :
    HoareTime (placedProgram slot hi) (fun w => w = v) (fun w => w = moved slot v) (87*n) := by
  apply (placed_hoare slot hi v bs n hn hc hs hd hr).consequence (fun _ h => h) (fun _ h => h)
  have hl := GrowingCounterData.canonical_width bs hcanon
  rw [hn] at hl
  have hlog := Nat.log2_le_self n
  omega

end
end IntegerMultBounds.Machine.RoleArrayMove
