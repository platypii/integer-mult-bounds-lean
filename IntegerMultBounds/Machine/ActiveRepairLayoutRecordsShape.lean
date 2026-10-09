import IntegerMultBounds.Machine.ActiveRepairLayoutPermutation

/-! Separate the actual physical record width from the payload-one address
space used by repair keys. No physical shape or reservation is changed. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsShape
noncomputable section
open CompactGadgetReservationShape CompactActiveTargetLayout

abbrev addressShape (s : Shape) : Shape := {s with payload:=1}
@[simp] theorem address_payload (s : Shape) : (addressShape s).payload=1 := rfl
@[simp] theorem address_bits (s : Shape) : (addressShape s).bits=s.bits := rfl
@[simp] theorem address_width (s : Shape) : (addressShape s).recordWidth=2^s.bits := by
  simp only [Shape.recordWidth,address_bits,Nat.mul_one]

variable (s : Shape) (w m before after rows : ℕ)
abbrev RecordAddress := Address (addressShape s) w m before after rows

def cell (x : RecordAddress s w m before after rows) (r : Fin s.payload) :
    Address s w m before after rows :=
  ⟨x.row,x.u,x.uTail,x.t,x.tTail,x.frontSlack,x.activeBefore,x.target,x.activeAfter,x.back,r⟩
def record (x : Address s w m before after rows) : RecordAddress s w m before after rows :=
  ⟨x.row,x.u,x.uTail,x.t,x.tTail,x.frontSlack,x.activeBefore,x.target,x.activeAfter,x.back,0⟩

def cellEquiv : Address s w m before after rows ≃
    RecordAddress s w m before after rows × Fin s.payload where
  toFun x := (record s w m before after rows x,x.payload)
  invFun x := cell s w m before after rows x.1 x.2
  left_inv _ := rfl
  right_inv x := by
    obtain ⟨x,r⟩ := x
    have hp : x.payload=0 := Subsingleton.elim _ _
    cases x
    simp only [cell,record] at hp ⊢
    cases hp
    rfl

variable (hw : w≤s.H) (ha : before+m+after=s.active*s.chunk)

theorem cell_index (x : RecordAddress s w m before after rows) (r : Fin s.payload) :
    (index s w m before after rows hw ha (cell s w m before after rows x r)).val=
      (index (addressShape s) w m before after rows hw ha x).val*s.payload+r.val := by
  have hp : x.payload.val=0 := by have := x.payload.isLt; change x.payload.val<1 at this; omega
  have hx := index_val (addressShape s) w m before after rows hw ha x
  rw [index_val s w m before after rows hw ha]
  simpa only [cell,addressShape,Shape.H,Shape.F,Shape.B,Nat.mul_one,hp,Nat.add_zero]
    using congrArg (fun z => z*s.payload+r.val) hx.symm

 theorem record_count : rows*(addressShape s).recordWidth*s.payload=rows*s.recordWidth := by
  change rows*(2^s.bits*1)*s.payload=rows*(2^s.bits*s.payload)
  ring

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsShape
