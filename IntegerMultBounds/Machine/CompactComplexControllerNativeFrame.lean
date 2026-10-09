import IntegerMultBounds.Machine.CompactComplexRootPieceEntry
import IntegerMultBounds.Machine.CompactChildHeadersStack

/-! Place the complete original native66 bank between the forty-four root
controller tapes and arbitrary persistent recursion storage. Native routines
frame every controller cell/head and every appended stack cell/head exactly. -/
namespace IntegerMultBounds.Machine.CompactComplexControllerNativeFrame
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {a s q : ℕ}

abbrev tapes (s : ℕ) := 43+(1+(66+s))
def nativeSlot (i : Fin 66) : Fin (tapes s) := Fin.natAdd 43 (Fin.natAdd 1 (Fin.castAdd s i))
def controllerSlot (i : Fin 43) : Fin (tapes s) := Fin.castAdd (1+(66+s)) i
def queueSlot : Fin (tapes s) := Fin.natAdd 43 (Fin.castAdd (66+s) (0 : Fin 1))
def storageSlot (i : Fin s) : Fin (tapes s) := Fin.natAdd 43 (Fin.natAdd 1 (Fin.natAdd 66 i))

theorem native_injective : Function.Injective (nativeSlot (s := s)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [nativeSlot,Fin.val_natAdd,Fin.val_castAdd] at hv
  omega

def placement := InjectivePlacement.placement (nativeSlot (s := s)) native_injective
  (by unfold tapes; omega : 66+(tapes s-66)=tapes s)

def bank (control : Tapes 43 a) (queue : Tapes 1 a) (native : Tapes 66 a) (storage : Tapes s a) :=
  control.append (queue.append (native.append storage))

theorem active_bank (control : Tapes 43 a) (queue : Tapes 1 a)
    (native : Tapes 66 a) (storage : Tapes s a) :
    Placement.active placement (bank control queue native storage)=native := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [placement,InjectivePlacement.active_slot,nativeSlot,bank,Tapes.append,
    Fin.addCases_right,Fin.addCases_left]

private theorem outside {l u t : ℕ} (e : Fin (l+u) ≃ Fin t)
    (v : Tapes t a) (small : Tapes l a) (slot : Fin t)
    (hn : ∀ i : Fin l, e (Fin.castAdd u i)≠slot) :
    (Placement.replace e v small).head slot=v.head slot ∧
      (Placement.replace e v small).tape slot=v.tape slot := by
  obtain ⟨j,rfl⟩ := e.surjective slot
  induction j using Fin.addCases with
  | left i => exact False.elim (hn i rfl)
  | right i =>
    constructor
    · exact Placement.combine_head_extra _ _ _ _
    · exact Placement.combine_tape_extra _ _ _ _

private theorem controller_outside (j : Fin 43) :
    ∀ i : Fin 66, placement (s := s) (Fin.castAdd (tapes s-66) i)≠controllerSlot j := by
  intro i h
  simp only [placement,InjectivePlacement.active_slot] at h
  have hv := congrArg Fin.val h
  simp only [nativeSlot,controllerSlot,Fin.val_natAdd,Fin.val_castAdd] at hv
  omega

private theorem queue_outside :
    ∀ i : Fin 66, placement (s := s) (Fin.castAdd (tapes s-66) i)≠queueSlot := by
  intro i h
  simp only [placement,InjectivePlacement.active_slot] at h
  have hv := congrArg Fin.val h
  simp only [nativeSlot,queueSlot,Fin.val_natAdd,Fin.val_castAdd,Fin.val_zero] at hv
  omega

private theorem storage_outside (j : Fin s) :
    ∀ i : Fin 66, placement (s := s) (Fin.castAdd (tapes s-66) i)≠storageSlot j := by
  intro i h
  simp only [placement,InjectivePlacement.active_slot] at h
  have hv := congrArg Fin.val h
  simp only [nativeSlot,storageSlot,Fin.val_natAdd,Fin.val_castAdd] at hv
  omega

theorem replace_bank (control : Tapes 43 a) (queue : Tapes 1 a)
    (old new : Tapes 66 a) (storage : Tapes s a) :
    Placement.replace placement (bank control queue old storage) new=bank control queue new storage := by
  have ha : ∀ i : Fin 66,
      (Placement.replace placement (bank control queue old storage) new).head (nativeSlot i)=new.head i ∧
      (Placement.replace placement (bank control queue old storage) new).tape (nativeSlot i)=new.tape i := by
    intro i
    constructor
    · simpa only [Placement.replace,placement,InjectivePlacement.active_slot] using
        Placement.combine_head_active placement new (Placement.extra placement (bank control queue old storage)) i
    · simpa only [Placement.replace,placement,InjectivePlacement.active_slot] using
        Placement.combine_tape_active placement new (Placement.extra placement (bank control queue old storage)) i
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases (m := 43) (n := 1+(66+s)) with
    | left i =>
      exact (outside placement (bank control queue old storage) new (controllerSlot i) (controller_outside i)).1.trans
        (by simp only [controllerSlot,bank,Tapes.append,Fin.addCases_left])
    | right i =>
      induction i using Fin.addCases (m := 1) (n := 66+s) with
      | left i =>
        fin_cases i
        exact (outside placement (bank control queue old storage) new queueSlot queue_outside).1.trans
          (by simp only [queueSlot,bank,Tapes.append,Fin.addCases_right,Fin.addCases_left]; rfl)
      | right i =>
        induction i using Fin.addCases (m := 66) (n := s) with
        | left i => exact (ha i).1.trans (by simp only [Tapes.append,Fin.addCases_right,Fin.addCases_left])
        | right i =>
          exact (outside placement (bank control queue old storage) new (storageSlot i) (storage_outside i)).1.trans
            (by simp only [storageSlot,bank,Tapes.append,Fin.addCases_right])
  · funext i
    induction i using Fin.addCases (m := 43) (n := 1+(66+s)) with
    | left i =>
      exact (outside placement (bank control queue old storage) new (controllerSlot i) (controller_outside i)).2.trans
        (by simp only [controllerSlot,bank,Tapes.append,Fin.addCases_left])
    | right i =>
      induction i using Fin.addCases (m := 1) (n := 66+s) with
      | left i =>
        fin_cases i
        exact (outside placement (bank control queue old storage) new queueSlot queue_outside).2.trans
          (by simp only [queueSlot,bank,Tapes.append,Fin.addCases_right,Fin.addCases_left]; rfl)
      | right i =>
        induction i using Fin.addCases (m := 66) (n := s) with
        | left i => exact (ha i).2.trans (by simp only [Tapes.append,Fin.addCases_right,Fin.addCases_left])
        | right i =>
          exact (outside placement (bank control queue old storage) new (storageSlot i) (storage_outside i)).2.trans
            (by simp only [storageSlot,bank,Tapes.append,Fin.addCases_right])

def program (M : Program 66 q a) := Placement.placed M (placement (s := s))

/-- No native scratch tape is borrowed for persistent controller storage. -/
theorem runs {M : Program 66 q a} {old new : Tapes 66 a} {B : ℕ}
    (h : HoareTime M (fun v => v=old) (fun v => v=new) B)
    (control : Tapes 43 a) (queue : Tapes 1 a) (storage : Tapes s a) :
    HoareTime (program M) (fun v => v=bank control queue old storage)
      (fun v => v=bank control queue new storage) B := by
  have hp := Placement.hoare_at h placement _ (active_bank control queue old storage)
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,hw,rfl⟩
  rw [hw]
  exact replace_bank control queue old new storage

end
end IntegerMultBounds.Machine.CompactComplexControllerNativeFrame
