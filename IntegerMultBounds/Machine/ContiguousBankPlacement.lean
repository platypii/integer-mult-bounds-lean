import IntegerMultBounds.Machine.InjectivePlacement

/-! Exact execution on a contiguous middle tape bank, preserving both
arbitrary banks around it literally, including all tape heads. -/
namespace IntegerMultBounds.Machine.ContiguousBankPlacement
noncomputable section
variable {a l n r q : ℕ}

def focus (i : Fin n) : Fin (l+(n+r)) := Fin.natAdd l (Fin.castAdd r i)
theorem focus_injective : Function.Injective (focus (l := l) (n := n) (r := r)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [focus,Fin.val_natAdd,Fin.val_castAdd] at hv
  omega

def placement := InjectivePlacement.placement (focus (l := l) (n := n) (r := r)) focus_injective
  (by omega : n+(l+(n+r)-n)=l+(n+r))
def bank (pre : Tapes l a) (small : Tapes n a) (post : Tapes r a) := pre.append (small.append post)

theorem active (pre : Tapes l a) (small : Tapes n a) (post : Tapes r a) :
    Placement.active placement (bank pre small post)=small := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [placement,InjectivePlacement.active_slot,focus,bank,Tapes.append,
    Fin.addCases_right,Fin.addCases_left]

private theorem outside {k u t : ℕ} (e : Fin (k+u) ≃ Fin t)
    (v : Tapes t a) (small : Tapes k a) (slot : Fin t)
    (hn : ∀ i : Fin k, e (Fin.castAdd u i)≠slot) :
    (Placement.replace e v small).head slot=v.head slot ∧
      (Placement.replace e v small).tape slot=v.tape slot := by
  obtain ⟨j,rfl⟩ := e.surjective slot
  induction j using Fin.addCases with
  | left i => exact False.elim (hn i rfl)
  | right i =>
    constructor
    · exact Placement.combine_head_extra _ _ _ _
    · exact Placement.combine_tape_extra _ _ _ _

private theorem left_outside (i : Fin l) :
    ∀ j : Fin n, placement (l := l) (n := n) (r := r) (Fin.castAdd (l+(n+r)-n) j)≠Fin.castAdd (n+r) i := by
  intro j h
  simp only [placement,InjectivePlacement.active_slot] at h
  have hv := congrArg Fin.val h
  simp only [focus,Fin.val_natAdd,Fin.val_castAdd] at hv
  omega

private theorem right_outside (i : Fin r) :
    ∀ j : Fin n, placement (l := l) (n := n) (r := r) (Fin.castAdd (l+(n+r)-n) j)≠Fin.natAdd l (Fin.natAdd n i) := by
  intro j h
  simp only [placement,InjectivePlacement.active_slot] at h
  have hv := congrArg Fin.val h
  simp only [focus,Fin.val_natAdd,Fin.val_castAdd] at hv
  omega

theorem replace (pre : Tapes l a) (old new : Tapes n a) (post : Tapes r a) :
    Placement.replace placement (bank pre old post) new=bank pre new post := by
  have ha : ∀ j : Fin n,
      (Placement.replace placement (bank pre old post) new).head (focus j)=new.head j ∧
      (Placement.replace placement (bank pre old post) new).tape (focus j)=new.tape j := by
    intro j
    constructor
    · simpa only [Placement.replace,placement,InjectivePlacement.active_slot] using
        Placement.combine_head_active placement new (Placement.extra placement (bank pre old post)) j
    · simpa only [Placement.replace,placement,InjectivePlacement.active_slot] using
        Placement.combine_tape_active placement new (Placement.extra placement (bank pre old post)) j
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases (m := l) (n := n+r) with
    | left i =>
      exact (outside placement (bank pre old post) new (Fin.castAdd (n+r) i) (left_outside i)).1.trans
        (by simp only [bank,Tapes.append,Fin.addCases_left])
    | right i =>
      induction i using Fin.addCases (m := n) (n := r) with
      | left i => exact (ha i).1.trans (by simp only [Tapes.append,Fin.addCases_right,Fin.addCases_left])
      | right i =>
        exact (outside placement (bank pre old post) new (Fin.natAdd l (Fin.natAdd n i)) (right_outside i)).1.trans
          (by simp only [bank,Tapes.append,Fin.addCases_right])
  · funext i
    induction i using Fin.addCases (m := l) (n := n+r) with
    | left i =>
      exact (outside placement (bank pre old post) new (Fin.castAdd (n+r) i) (left_outside i)).2.trans
        (by simp only [bank,Tapes.append,Fin.addCases_left])
    | right i =>
      induction i using Fin.addCases (m := n) (n := r) with
      | left i => exact (ha i).2.trans (by simp only [Tapes.append,Fin.addCases_right,Fin.addCases_left])
      | right i =>
        exact (outside placement (bank pre old post) new (Fin.natAdd l (Fin.natAdd n i)) (right_outside i)).2.trans
          (by simp only [bank,Tapes.append,Fin.addCases_right])

def program (M : Program n q a) := Placement.placed M (placement (l := l) (r := r))

theorem runs {M : Program n q a} {old new : Tapes n a} {B : ℕ}
    (h : HoareTime M (fun v => v=old) (fun v => v=new) B) (pre : Tapes l a) (post : Tapes r a) :
    HoareTime (program M) (fun v => v=bank pre old post) (fun v => v=bank pre new post) B := by
  have hp := Placement.hoare_at h placement _ (active pre old post)
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,hw,rfl⟩
  rw [hw]
  exact replace pre old new post

end
end IntegerMultBounds.Machine.ContiguousBankPlacement
