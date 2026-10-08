import IntegerMultBounds.Machine.TrackedCleanupOne
import IntegerMultBounds.Machine.BinaryDescriptorInstall

/-! Place literal visited-interval cleanup in fixed tape slots. Pair cleanup
erases data and its tracker; tracker-only cleanup preserves every data tape. -/
namespace IntegerMultBounds.Machine.TrackedCleanupAt
open SharedPlacementAlphabet (setTape)
variable {t a : ℕ}
noncomputable section

private theorem extra_ne {s u : ℕ} (e : Fin (s+u) ≃ Fin t)
    (i : Fin u) (j : Fin s) : e (Fin.natAdd s i) ≠ e (Fin.castAdd u j) := by
  intro h
  have hv := congrArg Fin.val (e.injective h)
  simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
  have hj := j.isLt
  omega

def pairProgram (src dst : Fin t) (hne : src ≠ dst) : Program t 4 a :=
  Placement.placed (TrackedCleanup.program a) (BinaryDescriptorInstall.placement src dst hne)

theorem pair_hoare (src dst : Fin t) (hne : src ≠ dst) (v : Tapes t a)
    (lo hi : ℤ) (B : ℕ) (hl : lo ≤ 0) (hh : 0 ≤ hi)
    (hp : lo ≤ v.head src ∧ v.head src ≤ hi) (hlo : -(B : ℤ) ≤ lo) (hhi : hi ≤ B)
    (hd : v.tape dst = TrackedCleanup.tracker lo hi) (hhds : v.head dst = v.head src)
    (hf : ∀ z, z < lo ∨ hi < z → v.tape src z = blank) :
    HoareTime (pairProgram src dst hne) (fun w => w = v)
      (fun w => w = setTape (setTape v src (fun _ => blank) 0) dst (fun _ => blank) 0) (5*B+5) := by
  let e := BinaryDescriptorInstall.placement src dst hne
  have ha : Placement.active e v = TrackedCleanup.bank (v.tape src)
      (TrackedCleanup.tracker lo hi) (v.head src) := by
    unfold Placement.active
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [e,BinaryDescriptorInstall.placement_active,BinaryDescriptorInstall.slot,
        TrackedCleanup.cfg,hd,hhds]
  have hc := Placement.hoare_at (TrackedCleanup.cleanup_hoare_linear
    (v.tape src) lo hi (v.head src) B hl hh hp hlo hhi hf) e v ha
  apply hc.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨small,rfl,rfl⟩
  let out := setTape (setTape v src (fun _ => blank) 0) dst (fun _ => blank) 0
  have hao : Placement.active e out = TrackedCleanup.bank (fun _ => blank) (fun _ => blank) 0 := by
    unfold Placement.active
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [e,out,BinaryDescriptorInstall.placement_active,BinaryDescriptorInstall.slot,
        TrackedCleanup.cfg,setTape,hne]
  have hex : Placement.extra e out = Placement.extra e v := by
    apply congrArg₂ Tapes.mk <;> funext i
    all_goals
      have hs : e (Fin.natAdd 2 i) ≠ src := by
        have h := extra_ne e i (0 : Fin 2)
        simpa [e,BinaryDescriptorInstall.slot] using h
      have hd' : e (Fin.natAdd 2 i) ≠ dst := by
        have h := extra_ne e i (1 : Fin 2)
        simpa [e,BinaryDescriptorInstall.slot] using h
      simp [out,setTape,hs,hd']
  rw [Placement.replace,← hao,← hex]
  exact Placement.view e out

def singleSlot (dst : Fin t) (_ : Fin 1) : Fin t := dst

def singlePlacement (dst : Fin t) : Fin (1+(t-1)) ≃ Fin t :=
  InjectivePlacement.placement (singleSlot dst) (by intro i j _; exact Subsingleton.elim i j)
    (by have hh := dst.isLt; omega)

@[simp] theorem singlePlacement_active (dst : Fin t) (i : Fin 1) :
    singlePlacement dst (Fin.castAdd (t-1) i) = dst :=
  InjectivePlacement.active_slot _ _ _ _

def singleProgram (dst : Fin t) : Program t 4 a :=
  Placement.placed (TrackedCleanupOne.program a) (singlePlacement dst)

theorem single_hoare (dst : Fin t) (v : Tapes t a) (lo hi : ℤ) (B : ℕ)
    (hl : lo ≤ 0) (hh : 0 ≤ hi) (hp : lo ≤ v.head dst ∧ v.head dst ≤ hi)
    (hlo : -(B : ℤ) ≤ lo) (hhi : hi ≤ B)
    (hd : v.tape dst = TrackedCleanup.tracker lo hi) :
    HoareTime (singleProgram dst) (fun w => w = v)
      (fun w => w = setTape v dst (fun _ => blank) 0) (5*B+5) := by
  have ha : Placement.active (singlePlacement dst) v =
      TrackedCleanupOne.one (TrackedCleanup.tracker lo hi) (v.head dst) := by
    simp [Placement.active,TrackedCleanupOne.one,hd]
  have hc := Placement.hoare_at (TrackedCleanupOne.cleanup_hoare lo hi (v.head dst) B hl hh hp hlo hhi)
    (singlePlacement dst) v ha
  apply hc.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨small,rfl,rfl⟩
  have hao : Placement.active (singlePlacement dst) (setTape v dst (fun _ => blank) 0) =
      TrackedCleanupOne.one (fun _ => blank) 0 := by
    simp [Placement.active,TrackedCleanupOne.one,setTape]
  have hex : Placement.extra (singlePlacement dst) (setTape v dst (fun _ => blank) 0) =
      Placement.extra (singlePlacement dst) v := by
    apply congrArg₂ Tapes.mk <;> funext i
    all_goals
      have hd' : singlePlacement dst (Fin.natAdd 1 i) ≠ dst := by
        have h := extra_ne (singlePlacement dst) i (0 : Fin 1)
        simpa only [singlePlacement_active] using h
      simp [setTape,hd']
  rw [Placement.replace,← hao,← hex]
  exact Placement.view _ _

end
end IntegerMultBounds.Machine.TrackedCleanupAt
