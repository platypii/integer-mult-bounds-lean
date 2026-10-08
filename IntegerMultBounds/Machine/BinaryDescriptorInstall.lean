import IntegerMultBounds.Machine.BinaryDescriptorCopy
import IntegerMultBounds.Machine.InjectivePlacement
import IntegerMultBounds.Machine.SharedPlacementAlphabet

/-! Install a descriptor in arbitrary distinct physical tape slots while
preserving every other complete tape and head. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorInstall
open SharedPlacementAlphabet (setTape)
variable {t q : ℕ}
noncomputable section

def slot (src dst : Fin t) : Fin 2 → Fin t := fun i => if i = 0 then src else dst

theorem slot_injective (src dst : Fin t) (hne : src ≠ dst) : Function.Injective (slot src dst) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [slot]

theorem size (src dst : Fin t) (hne : src ≠ dst) : 2+(t-2) = t := by
  have hv : src.val ≠ dst.val := fun h => hne (Fin.ext h)
  have hs := src.isLt
  have hd := dst.isLt
  omega

def placement (src dst : Fin t) (hne : src ≠ dst) : Fin (2+(t-2)) ≃ Fin t :=
  InjectivePlacement.placement (slot src dst) (slot_injective src dst hne) (size src dst hne)

def program (q : ℕ) (src dst : Fin t) (hne : src ≠ dst) : Program t 5 q :=
  Placement.placed (BinaryDescriptorCopy.encodedProgram q) (placement src dst hne)

@[simp] theorem placement_active (src dst : Fin t) (hne : src ≠ dst) (i : Fin 2) :
    placement src dst hne (Fin.castAdd (t-2) i) = slot src dst i :=
  InjectivePlacement.active_slot _ _ _ _

theorem active_input (src dst : Fin t) (hne : src ≠ dst) (v : Tapes t q) (xs : List Bool)
    (hs : v.tape src = RadixZeroFill.encodedBinary xs) (hsh : v.head src = 1)
    (hd : v.tape dst = fun _ => blank) (hdh : v.head dst = 0) :
    Placement.active (placement src dst hne) v = BinaryDescriptorCopy.encodedInput q xs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [placement_active,slot,Copy.cfg,hs,hsh,hd,hdh]

private theorem extra_ne_dst (src dst : Fin t) (hne : src ≠ dst) (i : Fin (t-2)) :
    placement src dst hne (Fin.natAdd 2 i) ≠ dst := by
  have he : placement src dst hne (Fin.castAdd (t-2) (1 : Fin 2)) = dst := by
    simp [slot]
  intro hh
  have hz := (placement src dst hne).injective (hh.trans he.symm)
  have hv := congrArg Fin.val hz
  simp only [Fin.val_natAdd,Fin.val_castAdd,Fin.val_one] at hv
  omega

theorem replace_output (src dst : Fin t) (hne : src ≠ dst) (v : Tapes t q) (xs : List Bool)
    (hs : v.tape src = RadixZeroFill.encodedBinary xs) (hsh : v.head src = 1) :
    Placement.replace (placement src dst hne) v (BinaryDescriptorCopy.encodedOutput q xs) =
      setTape v dst (RadixZeroFill.encodedBinary xs) 1 := by
  apply congrArg₂ Tapes.mk
  · funext i
    obtain ⟨i,rfl⟩ := (placement src dst hne).surjective i
    induction i using Fin.addCases with
    | left i =>
      change (Placement.combine _ _ _).head _ = _
      rw [Placement.combine_head_active,placement_active]
      fin_cases i <;> simp [slot,BinaryDescriptorCopy.encodedOutput,Copy.tapes,
        Copy.cfg,Config.tapes,hne,hsh]
    | right i =>
      change (Placement.combine _ _ _).head _ = _
      rw [Placement.combine_head_extra]
      simp [Placement.extra,extra_ne_dst src dst hne i]
  · funext i
    obtain ⟨i,rfl⟩ := (placement src dst hne).surjective i
    induction i using Fin.addCases with
    | left i =>
      change (Placement.combine _ _ _).tape _ = _
      rw [Placement.combine_tape_active,placement_active]
      fin_cases i <;> simp [slot,BinaryDescriptorCopy.encodedOutput,Copy.tapes,
        Copy.cfg,Config.tapes,hne,hs]
    | right i =>
      change (Placement.combine _ _ _).tape _ = _
      rw [Placement.combine_tape_extra]
      simp [Placement.extra,extra_ne_dst src dst hne i]

theorem install_hoare (src dst : Fin t) (hne : src ≠ dst) (v : Tapes t q) (xs : List Bool)
    (hs : v.tape src = RadixZeroFill.encodedBinary xs) (hsh : v.head src = 1)
    (hd : v.tape dst = fun _ => blank) (hdh : v.head dst = 0) :
    HoareTime (program q src dst hne) (fun w => w = v)
      (fun w => w = setTape v dst (RadixZeroFill.encodedBinary xs) 1) (2*xs.length+5) := by
  have hh := Placement.hoare_at (BinaryDescriptorCopy.encoded_copy_hoare q xs)
    (placement src dst hne) v (active_input src dst hne v xs hs hsh hd hdh)
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  exact replace_output src dst hne v xs hs hsh

/-- The exact postcondition preserves all other physical tapes and heads,
including the descriptor source. -/
theorem output_frame (v : Tapes t q) (dst i : Fin t) (hi : i ≠ dst) (xs : List Bool) :
    (setTape v dst (RadixZeroFill.encodedBinary xs) 1).head i = v.head i ∧
    (setTape v dst (RadixZeroFill.encodedBinary xs) 1).tape i = v.tape i := by
  simp [setTape,hi]

end
end IntegerMultBounds.Machine.BinaryDescriptorInstall
