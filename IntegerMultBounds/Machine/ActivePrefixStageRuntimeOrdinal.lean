import IntegerMultBounds.Machine.ActivePrefixStageRuntimeCoordinates

/-! The complete active word is recoverable from the original serialized
ordinal, independently of the source/target dependent address decomposition. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageRuntimeOrdinal
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageFullSelected (geometry Address)
open ActivePrefixStageRuntimeWord (word word_length)
open BinaryAddressTableData (row row_length row_rank)
open ActivePrefixDirtyControlGlobalSwap (index)
variable {s : Shape}

def activeOrdinal (s : Shape) {rows : ℕ} (k : Fin (rows*s.recordWidth)) : ℕ :=
  k.val/s.payload/2^(s.H+s.B)%2^(s.active*s.chunk)

def front (d : Inputs s) (i : Address d) : ℕ :=
  (((((i.row.val*2^((geometry d).n*(geometry d).b)+i.u.val)*
    2^(s.H-(geometry d).n*(geometry d).b)+i.uTail.val)*2^((geometry d).n*(geometry d).b)+i.t.val)*
    2^(s.H-(geometry d).n*(geometry d).b)+i.tTail.val)*2^s.F+i.frontSlack.val)

theorem word_value (d : Inputs s) (i : Address d) : Counter.value (word d i)=
    (i.activeBefore.val*2^((geometry d).n*(geometry d).q)+i.target.val)*2^(geometry d).after+i.activeAfter.val := by
  simp only [word,ColumnTransducer.value_append,List.length_append,row_length,
    row_rank _ _ i.activeBefore.isLt,row_rank _ _ i.target.isLt,row_rank _ _ i.activeAfter.isLt,pow_add]
  ring

theorem index_factored (d : Inputs s) (i : Address d) :
    (index s (geometry d) i).val=
      ((front d i*2^(s.active*s.chunk)+Counter.value (word d i))*2^(s.H+s.B)+i.back.val)*s.payload+i.payload.val := by
  rw [ActivePrefixDirtyControlGlobalSwap.index,CompactActiveTargetLayout.index_val,word_value]
  have hs := (geometry d).activeSize
  rw [←hs]
  simp only [front,pow_add]
  ring

theorem quotient (a b c : ℕ) (hc : 0<c) (hb : b<c) : (a*c+b)/c=a := by
  rw [Nat.mul_comm a c,Nat.mul_add_div hc,Nat.div_eq_of_lt hb,Nat.add_zero]

theorem active_at_index (d : Inputs s) (i : Address d) :
    activeOrdinal s (index s (geometry d) i)=Counter.value (word d i) := by
  have hp : 0<s.payload := by have := d.hrecord; omega
  have hw : Counter.value (word d i)<2^(s.active*s.chunk) := by
    simpa only [word_length] using Counter.value_lt (word d i)
  rw [activeOrdinal,index_factored,quotient _ _ _ hp i.payload.isLt,
    quotient _ _ _ (by positivity) i.back.isLt,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hw]

def rawCoordinates (v : ActivePrefixStageParameters.Stage s) {rows : ℕ}
    (k : Fin (rows*s.recordWidth)) : Fin v.f → Fin v.slots → Bool :=
  fun axis slot => Nat.testBit (activeOrdinal s k)
    (ActivePrefixStageGeometry.slotLow v slot+(v.rho+axis.val*s.chunk))

theorem coordinates_at_index (d : Inputs s) (i : Address d) :
    rawCoordinates d.stage (index s (geometry d) i)=ActivePrefixStageRuntimeCoordinates.coordinates d i := by
  funext axis slot
  rw [rawCoordinates,active_at_index,Compact.PowerTwo.testBit_value]
  rfl

/-- Axis ordinals in the original node run high to low; row words run low
bit first. Reversal is explicit rather than hidden in the basis columns. -/
def reverseAxis {f : ℕ} (axis : Fin f) : Fin f := ⟨f-axis.val-1,by have := axis.isLt; omega⟩

def originalAxis (v : ActivePrefixStageParameters.Stage s) (slot : Fin v.slots) (axis : Fin v.f) : ℕ :=
  v.left+slot.val*v.f+axis.val

def originalPosition (v : ActivePrefixStageParameters.Stage s) (slot : Fin v.slots) (axis : Fin v.f) : ℕ :=
  (s.active-originalAxis v slot axis-1)*s.chunk+v.rho

theorem original_position (v : ActivePrefixStageParameters.Stage s) (slot : Fin v.slots) (axis : Fin v.f) :
    originalPosition v slot axis=ActivePrefixStageGeometry.slotLow v slot+(v.rho+(reverseAxis axis).val*s.chunk) := by
  have hs := ActivePrefixStageParameters.axes_split v slot
  unfold ActivePrefixStageParameters.highAxes at hs
  have he : s.active-(v.left+slot.val*v.f+axis.val)-1=
      ActivePrefixStageParameters.lowAxes v slot+(v.f-axis.val-1) := by have := axis.isLt; omega
  simp only [originalPosition,originalAxis,he,reverseAxis,ActivePrefixStageGeometry.slotLow]
  ring

def highCoordinates (v : ActivePrefixStageParameters.Stage s) {rows : ℕ}
    (k : Fin (rows*s.recordWidth)) : Fin v.f → Fin v.slots → Bool :=
  fun axis slot => Nat.testBit (activeOrdinal s k) (originalPosition v slot axis)

theorem high_coordinates (v : ActivePrefixStageParameters.Stage s) {rows : ℕ}
    (k : Fin (rows*s.recordWidth)) (axis : Fin v.f) (slot : Fin v.slots) :
    highCoordinates v k axis slot=rawCoordinates v k (reverseAxis axis) slot := by
  rw [highCoordinates,original_position]
  rfl

theorem high_at_index (d : Inputs s) (i : Address d) (axis : Fin d.stage.f) (slot : Fin d.stage.slots) :
    highCoordinates d.stage (index s (geometry d) i) axis slot=
      (word d i).getD (originalPosition d.stage slot axis) false := by
  rw [highCoordinates,active_at_index,Compact.PowerTwo.testBit_value]

end
end IntegerMultBounds.Machine.ActivePrefixStageRuntimeOrdinal
