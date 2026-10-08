import IntegerMultBounds.Machine.BinaryDescriptorStackRoundtrip
import IntegerMultBounds.Machine.BinaryDescriptorInstall

/-! Place variable-length descriptor push and pop on arbitrary distinct slots;
all other complete tapes and heads are preserved literally. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorStackAt
open SharedPlacementAlphabet (setTape)
open BinaryDescriptorInstall (placement slot placement_active)
open BinaryDescriptorStack
variable {t a : ℕ}
noncomputable section

private theorem active_pair (src dst : Fin t) (hne : src ≠ dst) (v : Tapes t a) :
    Placement.active (placement src dst hne) v = Copy.tapes (v.tape src) (v.tape dst) (v.head src) (v.head dst) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [placement_active,slot,Copy.cfg]

private theorem extra_ne (src dst : Fin t) (hne : src ≠ dst) (i : Fin (t-2)) :
    placement src dst hne (Fin.natAdd 2 i) ≠ src ∧ placement src dst hne (Fin.natAdd 2 i) ≠ dst := by
  constructor
  · intro he
    have hh : placement src dst hne (Fin.castAdd (t-2) (0 : Fin 2)) = src := by simp [slot]
    have hv := congrArg Fin.val ((placement src dst hne).injective (he.trans hh.symm))
    simp only [Fin.val_natAdd,Fin.val_castAdd,Fin.val_zero] at hv
    omega
  · intro he
    have hh : placement src dst hne (Fin.castAdd (t-2) (1 : Fin 2)) = dst := by simp [slot]
    have hv := congrArg Fin.val ((placement src dst hne).injective (he.trans hh.symm))
    simp only [Fin.val_natAdd,Fin.val_castAdd,Fin.val_one] at hv
    omega

private theorem replace_pair (src dst : Fin t) (hne : src ≠ dst) (v : Tapes t a)
    (f g : ℤ → Fin (a+4)) (p q : ℤ) :
    Placement.replace (placement src dst hne) v (Copy.tapes f g p q) =
      setTape (setTape v src f p) dst g q := by
  apply congrArg₂ Tapes.mk
  · funext i
    obtain ⟨i,rfl⟩ := (placement src dst hne).surjective i
    induction i using Fin.addCases with
    | left i =>
      change (Placement.combine _ _ _).head _ = _
      rw [Placement.combine_head_active,placement_active]
      fin_cases i <;> simp [slot,Copy.tapes,Copy.cfg,Config.tapes,setTape,hne]
    | right i =>
      change (Placement.combine _ _ _).head _ = _
      rw [Placement.combine_head_extra]
      simp [Placement.extra,setTape,extra_ne src dst hne i]
  · funext i
    obtain ⟨i,rfl⟩ := (placement src dst hne).surjective i
    induction i using Fin.addCases with
    | left i =>
      change (Placement.combine _ _ _).tape _ = _
      rw [Placement.combine_tape_active,placement_active]
      fin_cases i <;> simp [slot,Copy.tapes,Copy.cfg,Config.tapes,setTape,hne]
    | right i =>
      change (Placement.combine _ _ _).tape _ = _
      rw [Placement.combine_tape_extra]
      simp [Placement.extra,setTape,extra_ne src dst hne i]

def pushProgram (src stack : Fin t) (hne : src ≠ stack) : Program t 8 a :=
  Placement.placed push (placement src stack hne)

def popProgram (stack dst : Fin t) (hne : stack ≠ dst) : Program t 8 a :=
  Placement.placed pop (placement stack dst hne)

theorem push_hoare (src stack : Fin t) (hne : src ≠ stack) (v : Tapes t a) (xs : List Bool)
    (hs : v.tape src = descriptor xs) (hh : v.head src = 1) :
    HoareTime (pushProgram src stack hne) (fun w => w = v)
      (fun w => w = setTape v stack (frame (v.tape stack) (v.head stack) xs) (v.head stack+1+xs.length))
      (2*xs.length+7) := by
  have hp := Placement.hoare_at (BinaryDescriptorStack.push_hoare xs (v.tape stack) (v.head stack))
    (placement src stack hne) v (by rw [active_pair,hs,hh])
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  rw [replace_pair]
  have he : setTape v src (descriptor xs) 1 = v := by
    rw [← hs,← hh]
    cases v
    simp [setTape]
  rw [he]

theorem pop_hoare (stack dst : Fin t) (hne : stack ≠ dst) (v : Tapes t a)
    (f : ℤ → Fin (a+4)) (p : ℤ) (xs : List Bool)
    (hs : v.tape stack = frame f p xs) (hh : v.head stack = p+1+xs.length)
    (hd : v.tape dst = fun _ => blank) (hdh : v.head dst = 0)
    (hf : ∀ z, p ≤ z → z < p+1+xs.length → f z = blank) :
    HoareTime (popProgram stack dst hne) (fun w => w = v)
      (fun w => w = setTape (setTape v stack f p) dst (descriptor xs) 1) (2*xs.length+7) := by
  have hp := Placement.hoare_at (BinaryDescriptorStack.pop_hoare xs f p hf)
    (placement stack dst hne) v (by rw [active_pair,hs,hh,hd,hdh])
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  exact replace_pair _ _ _ _ _ _ _ _

end
end IntegerMultBounds.Machine.BinaryDescriptorStackAt
