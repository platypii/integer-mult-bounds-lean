import IntegerMultBounds.Machine.InjectivePlacement
import IntegerMultBounds.Machine.FamilyPlacementAlphabet

/-! An arbitrary fixed number of permanent tapes shared by actual stages.
Selected private slots are genuinely blank stationary frames. Fixed injective
placements redirect accesses to the common bank without copying or resetting. -/
namespace IntegerMultBounds.Machine.SharedBank
noncomputable section
variable {k t q a : ℕ}

/-- Lift a local stage slot into the permanent bank or its private remainder. -/
def slot (slots : Fin k → Fin t) (i : Fin t) : Fin (k+t) :=
  if h : ∃ j, slots j = i then Fin.castAdd t h.choose else Fin.natAdd k i

theorem slot_selected (slots : Fin k → Fin t) (hinj : Function.Injective slots) (j : Fin k) :
    slot slots (slots j) = Fin.castAdd t j := by
  unfold slot
  split_ifs with h
  · exact congrArg (Fin.castAdd t) (hinj h.choose_spec)
  · exact (h ⟨j,rfl⟩).elim

theorem slot_injective (slots : Fin k → Fin t) : Function.Injective (slot slots) := by
  have left : Function.LeftInverse (Fin.addCases slots id) (slot slots) := by
    intro i
    unfold slot
    split_ifs with h
    · simpa only [Fin.addCases_left] using h.choose_spec
    · simp
  exact left.injective

def placement (slots : Fin k → Fin t) : Fin (t+k) ≃ Fin (k+t) :=
  InjectivePlacement.placement (slot slots) (slot_injective slots) (Nat.add_comm t k)

theorem placement_active (slots : Fin k → Fin t) (i : Fin t) :
    placement slots (Fin.castAdd k i) = slot slots i :=
  InjectivePlacement.active_slot _ _ _ i

def payload (v : Tapes t a) (slots : Fin k → Fin t) : Tapes k a :=
  ⟨fun i => v.head (slots i),fun i => v.tape (slots i)⟩

def strip (v : Tapes t a) (slots : Fin k → Fin t) : Tapes t a :=
  ⟨fun i => if ∃ j, slots j = i then 0 else v.head i,
    fun i => if ∃ j, slots j = i then (fun _ => blank) else v.tape i⟩

def bank (v : Tapes t a) (slots : Fin k → Fin t) : Tapes (k+t) a :=
  (payload v slots).append (strip v slots)

def empty (k a : ℕ) : Tapes k a := ⟨fun _ => 0,fun _ _ => blank⟩

theorem strip_payload (v : Tapes t a) (slots : Fin k → Fin t) :
    payload (strip v slots) slots = empty k a := by
  unfold payload strip empty
  congr 1 <;> funext i <;> simp

theorem active_bank (v : Tapes t a) (slots : Fin k → Fin t) :
    Placement.active (placement slots) (bank v slots) = v := by
  unfold placement
  rw [InjectivePlacement.active_bank]
  unfold bank payload strip slot
  congr 1 <;> funext i <;> split_ifs with h
  · simp only [Tapes.append,Fin.addCases_left,h.choose_spec]
  · simp only [Tapes.append,Fin.addCases_right,h,ite_false]
  · simp only [Tapes.append,Fin.addCases_left,h.choose_spec]
  · simp only [Tapes.append,Fin.addCases_right,h,ite_false]

private theorem unselected (slots : Fin k → Fin t) (hinj : Function.Injective slots) (x : Fin (k+t))
    (hx : ∀ i, x ≠ slot slots i) : ∃ j, x = Fin.natAdd k (slots j) := by
  induction x using Fin.addCases with
  | left j => exact (hx (slots j) (slot_selected slots hinj j).symm).elim
  | right i =>
    by_cases h : ∃ j, slots j = i
    · obtain ⟨j,rfl⟩ := h
      exact ⟨j,rfl⟩
    · exact (hx i (by simp [slot,h])).elim

/-- Every unused private selected slot is an exact blank stationary frame. -/
theorem extra_bank (v : Tapes t a) (slots : Fin k → Fin t) (hinj : Function.Injective slots) :
    Placement.extra (placement slots) (bank v slots) = empty k a := by
  have hx (j : Fin k) : ∀ i, placement slots (Fin.natAdd t j) ≠ slot slots i := by
    intro i he
    rw [← placement_active slots i] at he
    have hv := congrArg Fin.val ((placement slots).injective he)
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  unfold Placement.extra
  congr 1 <;> funext j <;>
    obtain ⟨i,hi⟩ := unselected slots hinj _ (hx j) <;>
    rw [hi] <;> simp [bank,strip,Tapes.append]

/-- Actual execution against the common bank, retaining all private metadata. -/
theorem stage_hoare {M : Program t q a} {v w : Tapes t a} {cost : ℕ}
    (hh : HoareTime M (fun x => x = v) (fun x => x = w) cost)
    (slots : Fin k → Fin t) (hinj : Function.Injective slots) :
    HoareTime (Placement.placed M (placement slots))
      (fun x => x = bank v slots) (fun x => x = bank w slots) cost := by
  have hs := Placement.hoare_at hh (placement slots) (bank v slots) (active_bank v slots)
  apply hs.consequence (fun _ h => h) ?_ le_rfl
  rintro x ⟨small,hsmall,rfl⟩
  subst small
  rw [Placement.replace,extra_bank v slots hinj,← extra_bank w slots hinj]
  have hw := Placement.view (placement slots) (bank w slots)
  simpa only [active_bank] using hw

end
end IntegerMultBounds.Machine.SharedBank
