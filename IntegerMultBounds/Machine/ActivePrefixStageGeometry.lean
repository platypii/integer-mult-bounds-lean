import IntegerMultBounds.Machine.ActivePrefixStageParameters

/-! Physical offsets of the two distinct original slots. Early sources lie
strictly above the target's retained highest bit; later sources lie wholly
inside activeAfter. Selected positions are exactly rho+i*K within each
original f*K-bit slot, including the final position omitted by the low map. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageGeometry
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
variable {s : Shape}

def slotStart (v : Stage s) (i : Fin v.slots) := highAxes v i*s.chunk
def slotWidth (v : Stage s) := v.f*s.chunk
def slotLow (v : Stage s) (i : Fin v.slots) := lowAxes v i*s.chunk

def earlyOffset (v : Stage s) := (v.target.val-v.source.val-1)*v.f*s.chunk+(s.chunk-v.rho)
def lateOffset (v : Stage s) := slotLow v v.source

theorem source_order (v : Stage s) : v.source.val<v.target.val ∨ v.target.val<v.source.val := by
  have hn : v.source.val≠v.target.val := fun h => v.distinct (Fin.ext h)
  omega

theorem original_slot_split (v : Stage s) (i : Fin v.slots) :
    slotStart v i+slotWidth v+slotLow v i=s.active*s.chunk := by
  have h := congrArg (fun a => a*s.chunk) (axes_split v i)
  simpa only [Nat.add_mul,slotStart,slotWidth,slotLow] using h

/-- High and low retained target intervals are the original slot remnants. -/
theorem target_slot_split (v : Stage s) :
    before v=slotStart v v.target+(s.chunk-v.rho) ∧
    after v=slotLow v v.target+v.rho ∧
    (s.chunk-v.rho)+(v.f-1)*s.chunk+v.rho=slotWidth v :=
  ⟨rfl,rfl,width_split v⟩

theorem early_axes (v : Stage s) (horder : v.source.val<v.target.val) :
    highAxes v v.source+v.f+(v.target.val-v.source.val-1)*v.f=highAxes v v.target := by
  have hi : v.source.val+1+(v.target.val-v.source.val-1)=v.target.val := by omega
  have hm := congrArg (fun a => a*v.f) hi
  simp only [Nat.add_mul,Nat.one_mul] at hm
  unfold highAxes
  omega

theorem late_axes (v : Stage s) (horder : v.target.val<v.source.val) :
    (v.source.val-v.target.val-1)*v.f+v.f+lowAxes v v.source=lowAxes v v.target := by
  have hs := v.source.isLt
  have hi : v.source.val-v.target.val-1+1+(v.slots-v.source.val-1)=v.slots-v.target.val-1 := by omega
  have hm := congrArg (fun a => a*v.f) hi
  simp only [Nat.add_mul,Nat.one_mul] at hm
  unfold lowAxes
  omega

/-- The earlier source ends before the retained target-high interval. -/
theorem early_slot_gap (v : Stage s) (horder : v.source.val<v.target.val) :
    slotStart v v.source+slotWidth v+earlyOffset v=before v := by
  have h := congrArg (fun a => a*s.chunk) (early_axes v horder)
  simp only [Nat.add_mul] at h
  unfold slotStart slotWidth earlyOffset before
  omega

theorem early_fits (v : Stage s) (horder : v.source.val<v.target.val) :
    earlyOffset v+v.f*s.chunk≤before v := by
  have := early_slot_gap v horder
  unfold slotWidth at this
  omega

theorem early_disjoint (v : Stage s) : 1≤earlyOffset v := by
  have := v.selectedFits
  unfold earlyOffset
  omega

theorem late_fits (v : Stage s) (horder : v.target.val<v.source.val) :
    lateOffset v+v.f*s.chunk≤after v := by
  have h := congrArg (fun a => a*s.chunk) (late_axes v horder)
  simp only [Nat.add_mul] at h
  unfold lateOffset slotLow after
  omega

theorem original_disjoint (v : Stage s) :
    slotStart v v.source+slotWidth v≤slotStart v v.target ∨
      slotStart v v.target+slotWidth v≤slotStart v v.source := by
  rcases source_order v with he | hl
  · left
    have h := congrArg (fun a => a*s.chunk) (early_axes v he)
    simp only [Nat.add_mul] at h
    unfold slotStart slotWidth
    omega
  · right
    have hs := original_slot_split v v.source
    have ht := original_slot_split v v.target
    have h := congrArg (fun a => a*s.chunk) (late_axes v hl)
    simp only [Nat.add_mul] at h
    unfold slotLow slotWidth at hs ht
    unfold slotWidth
    omega

/-- The containing target slot's selected positions become the low gadget's
stride positions; the last one is activeBefore bit zero. -/
theorem target_selected_position (v : Stage s) (i : ℕ) :
    after v+i*s.chunk=slotLow v v.target+(v.rho+i*s.chunk) := by
  unfold after slotLow
  omega

theorem early_source_selected_position (v : Stage s) (horder : v.source.val<v.target.val) (i : ℕ) :
    after v+(v.f-1)*s.chunk+(earlyOffset v+v.rho+i*s.chunk)=
      slotLow v v.source+(v.rho+i*s.chunk) := by
  have hf := early_slot_gap v horder
  have ha := original_slot_split v v.source
  have hb := active_size v
  unfold slotWidth at ha hf
  omega

theorem late_source_selected_position (v : Stage s) (i : ℕ) :
    lateOffset v+v.rho+i*s.chunk=slotLow v v.source+(v.rho+i*s.chunk) := by
  unfold lateOffset
  omega

theorem early_high_distance (v : Stage s) (horder : v.source.val<v.target.val) :
    earlyOffset v+v.rho+(v.f-1)*s.chunk=(v.target.val-v.source.val)*v.f*s.chunk := by
  have hw := width_split v
  have hd : v.target.val-v.source.val-1+1=v.target.val-v.source.val := by omega
  have hm := congrArg (fun a => a*v.f*s.chunk) hd
  simp only [Nat.add_mul,Nat.one_mul] at hm
  unfold earlyOffset
  omega

theorem early_high_positive (v : Stage s) (horder : v.source.val<v.target.val) :
    0<earlyOffset v+v.rho+(v.f-1)*s.chunk := by
  rw [early_high_distance v horder]
  have hf := v.positiveWidth
  have hK : 0<s.chunk := by have := v.selectedFits; omega
  exact Nat.mul_pos (Nat.mul_pos (by omega) hf) hK

theorem early_parameters_fit (v : Stage s) (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk)
    (horder : v.source.val<v.target.val) :
    earlyOffset v+(parameters v hG hGK).f*(parameters v hG hGK).q≤(parameters v hG hGK).before :=
  early_fits v horder

theorem late_parameters_fit (v : Stage s) (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk)
    (horder : v.target.val<v.source.val) :
    lateOffset v+(parameters v hG hGK).f*(parameters v hG hGK).q≤(parameters v hG hGK).after :=
  late_fits v horder

theorem early_parameters_high (v : Stage s) (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk)
    (horder : v.source.val<v.target.val) :
    0<ActiveTargetHighestPairLayoutGeometry.sourceHigh s (parameters v hG hGK) (earlyOffset v) :=
  early_high_positive v horder

/-- Every selected position is inside its original complete f*K-bit slot. -/
theorem selected_inside_slot (v : Stage s) (j : Fin v.slots) (i : Fin v.f) :
    slotLow v j≤slotLow v j+(v.rho+i.val*s.chunk) ∧
      slotLow v j+(v.rho+i.val*s.chunk)<slotLow v j+slotWidth v := by
  have hi := i.isLt
  have hr := v.selectedFits
  have hm := Nat.mul_le_mul_right s.chunk (show i.val+1≤v.f by omega)
  simp only [Nat.add_mul,Nat.one_mul] at hm
  unfold slotWidth
  constructor <;> omega

/-- The target highest operation is exactly the original final selected bit,
not a newly added address coordinate. -/
theorem target_highest_position (v : Stage s) :
    after v+(v.f-1)*s.chunk=slotLow v v.target+(v.rho+(v.f-1)*s.chunk) :=
  target_selected_position v (v.f-1)

end IntegerMultBounds.Machine.ActivePrefixStageGeometry
