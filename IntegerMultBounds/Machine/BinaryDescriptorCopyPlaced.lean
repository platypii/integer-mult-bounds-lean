import IntegerMultBounds.Machine.BinaryDescriptorCopy
import IntegerMultBounds.Machine.PlacedDescriptorConstruction

/-! Physical marked descriptor duplication on two actual caller tapes.
The source word and head survive, the blank destination becomes the same
canonical word at head one, and all other caller tapes and heads are framed. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorCopyPlaced
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {t a : ℕ}

theorem room (focus : Fin 2 → Fin t) (hf : Function.Injective focus) : 2+(t-2)=t := by
  have h := Fintype.card_le_of_injective focus hf
  simp only [Fintype.card_fin] at h
  omega
def placement (focus : Fin 2 → Fin t) (hf : Function.Injective focus) :=
  InjectivePlacement.placement focus hf (room focus hf)
def program (focus : Fin 2 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (BinaryDescriptorCopy.encodedProgram a) (placement focus hf)

theorem active (caller : Tapes t a) (focus : Fin 2 → Fin t) (hf : Function.Injective focus) :
    Placement.active (placement focus hf) caller=SharedBank.payload caller focus := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [placement,InjectivePlacement.active_slot]

theorem output_set (xs : List Bool) : BinaryDescriptorCopy.encodedOutput a xs=
    setTape (BinaryDescriptorCopy.encodedInput a xs) 1 (RadixZeroFill.encodedBinary xs) 1 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem copies (caller : Tapes t a) (focus : Fin 2 → Fin t) (hf : Function.Injective focus)
    (xs : List Bool) (hi : SharedBank.payload caller focus=BinaryDescriptorCopy.encodedInput a xs) :
    HoareTime (program focus hf) (fun v => v=caller)
      (fun v => v=setTape caller (focus 1) (RadixZeroFill.encodedBinary xs) 1)
      (2*xs.length+5) := by
  have ha := (active caller focus hf).trans hi
  have hr := Placement.hoare_at (BinaryDescriptorCopy.encoded_copy_hoare a xs)
    (placement focus hf) caller ha
  apply hr.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [output_set,←ha,PlacedDescriptorConstruction.replace_setTape]
  simp only [placement,InjectivePlacement.active_slot]

end
end IntegerMultBounds.Machine.BinaryDescriptorCopyPlaced
