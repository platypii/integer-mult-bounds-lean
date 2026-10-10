import IntegerMultBounds.Machine.TwoTapeAt

/-! Exact one-tape subroutines at fixed caller slots, framing every other tape. -/
namespace IntegerMultBounds.Machine.NativeReturnOneTape
noncomputable section
variable {t a q cost : ℕ}
def slot (i : Fin t) : Fin 1 → Fin t := fun _ => i
private theorem injective (i : Fin t) : Function.Injective (slot i) := by intro x y _; exact Subsingleton.elim _ _
def placement (i : Fin t) : Fin (1+(t-1)) ≃ Fin t :=
  InjectivePlacement.placement (slot i) (injective i) (by have := i.isLt; omega)
def program (M : Program 1 q a) (i : Fin t) := Placement.placed M (placement i)

theorem runs (M : Program 1 q a) (i : Fin t) (v : Tapes t a)
    (f g : ℤ → Fin (a+4)) (p r : ℤ) (hi : v.tape i=f ∧ v.head i=p)
    (h : HoareTime M (fun w => w=⟨fun _ => p,fun _ => f⟩)
      (fun w => w=⟨fun _ => r,fun _ => g⟩) cost) :
    HoareTime (program M i) (fun w => w=v)
      (fun w => w=SharedPlacementAlphabet.setTape v i g r) cost := by
  have ha : Placement.active (placement i) v=⟨fun _ => p,fun _ => f⟩ := by
    rw [placement,InjectivePlacement.active_bank]
    apply congrArg₂ Tapes.mk <;> funext x <;> simp [slot,hi]
  apply (Placement.hoare_at h (placement i) v ha).consequence (fun _ h => h) ?_ le_rfl
  rintro w ⟨small,rfl,rfl⟩
  simp only [placement]
  apply Placement.Tapes.ext'
  · intro x
    by_cases hx:x=i
    · subst x
      have hh := InjectivePlacement.replace_head_slot (slot i) (injective i)
        (show 1+(t-1)=t by have := i.isLt; omega) v (⟨fun _ => r,fun _ => g⟩ : Tapes 1 a) 0
      simpa [placement,slot,SharedPlacementAlphabet.setTape] using hh
    · rw [InjectivePlacement.replace_head_other (slot i) (injective i)
        (show 1+(t-1)=t by have := i.isLt; omega) v _ x (by intro j; simpa [slot] using Ne.symm hx)]
      simp [SharedPlacementAlphabet.setTape,hx]
  · intro x
    by_cases hx:x=i
    · subst x
      have hh := InjectivePlacement.replace_tape_slot (slot i) (injective i)
        (show 1+(t-1)=t by have := i.isLt; omega) v (⟨fun _ => r,fun _ => g⟩ : Tapes 1 a) 0
      simpa [placement,slot,SharedPlacementAlphabet.setTape] using hh
    · rw [InjectivePlacement.replace_tape_other (slot i) (injective i)
        (show 1+(t-1)=t by have := i.isLt; omega) v _ x (by intro j; simpa [slot] using Ne.symm hx)]
      simp [SharedPlacementAlphabet.setTape,hx]
end
end IntegerMultBounds.Machine.NativeReturnOneTape
