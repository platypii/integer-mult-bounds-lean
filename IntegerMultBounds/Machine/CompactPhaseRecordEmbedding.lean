import IntegerMultBounds.Machine.CompactLiteralUnitPhase
import IntegerMultBounds.Machine.ActivePrefixStageTripleTransport

/-! Explicit physical record-start embedding, its actual stage destination,
and the corresponding coefficient ordinal. Payload offset zero is preserved
by every actual stage instruction and therefore by the complete literal word. -/
namespace IntegerMultBounds.Machine.CompactPhaseRecordEmbedding
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageFullSelected (geometry)
open ActivePrefixStagePairData (changePair)
open ActivePrefixDirtyControlGlobalSwap (index)
open Networks Networks.ComplexPhaseRowSchedule
variable {s : Shape}

def start (d : Inputs s) (i : Fin (d.rows*2^s.bits)) : Fin (d.rows*s.recordWidth) :=
  ⟨i.val*s.payload,by
    have hp : 0<s.payload := by have := d.hrecord; omega
    have h := Nat.mul_lt_mul_of_pos_right i.isLt hp
    simpa only [Shape.recordWidth,Nat.mul_assoc] using h⟩

theorem start_val (d : Inputs s) (i : Fin (d.rows*2^s.bits)) : (start d i).val=i.val*s.payload := rfl

theorem index_mod (d : Inputs s) (i : ActivePrefixStageFullSelected.Address d) :
    (index s (geometry d) i).val%s.payload=i.payload.val := by
  rw [ActivePrefixStageRuntimeOrdinal.index_factored,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt i.payload.isLt]

theorem destination_mod (d : Inputs s) (op : BinaryRowProgram.Op (Fin d.stage.slots))
    (k : Fin (d.rows*s.recordWidth)) :
    (ActivePrefixStagePairCoordinates.destination d op k).val%s.payload=k.val%s.payload := by
  let a := (ActivePrefixStagePairCoordinates.addressEquiv (changePair d op)).symm k
  have hp := congrArg (fun x => x.payload)
    (ActivePrefixStageTripleTransport.destination_payload (changePair d op) a a.payload)
  change (ActivePrefixStageRuntimeSelected.destination (changePair d op) a).payload=a.payload at hp
  have hleft := index_mod (changePair d op) (ActivePrefixStageRuntimeSelected.destination (changePair d op) a)
  have hright := index_mod (changePair d op) a
  have hdecode := ActivePrefixStagePairCoordinates.index_decode (changePair d op) k
  change index s (geometry (changePair d op)) a=k at hdecode
  rw [hdecode] at hright
  exact hleft.trans ((congrArg Fin.val hp).trans hright.symm)

theorem run_mod (d : Inputs s) (ops : List (BinaryRowProgram.Op (Fin d.stage.slots)))
    (k : Fin (d.rows*s.recordWidth)) : (ActivePrefixStagePairCoordinates.run d ops k).val%s.payload=k.val%s.payload := by
  induction ops generalizing k with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (destination_mod d op k)

theorem destination_start_mod (d : Inputs s) (hslots : d.stage.slots=25^3) (edge : Edge)
    (i : Fin (d.rows*2^s.bits)) : (CompactComplexPhasePhysical.destination d hslots edge (start d i)).val%s.payload=0 := by
  rw [CompactComplexPhasePhysical.destination,run_mod,start_val,Nat.mul_mod_left]

def ordinal (d : Inputs s) (hslots : d.stage.slots=25^3) (edge : Edge) (i : Fin (d.rows*2^s.bits)) :
    Fin (d.rows*2^s.bits) :=
  ⟨CompactComplexPhaseRecordAddress.rank d hslots edge (start d i),by
    have hp : 0<s.payload := by have := d.hrecord; omega
    apply (Nat.div_lt_iff_lt_mul hp).2
    simpa only [Shape.recordWidth,Nat.mul_assoc] using
      (CompactComplexPhasePhysical.destination d hslots edge (start d i)).isLt⟩

theorem destination_start (d : Inputs s) (hslots : d.stage.slots=25^3) (edge : Edge) (i : Fin (d.rows*2^s.bits)) :
    CompactComplexPhasePhysical.destination d hslots edge (start d i)=start d (ordinal d hslots edge i) := by
  apply Fin.ext
  have h := Nat.mod_add_div (CompactComplexPhasePhysical.destination d hslots edge (start d i)).val s.payload
  rw [destination_start_mod d hslots edge i,zero_add] at h
  simpa only [start,ordinal,CompactComplexPhaseRecordAddress.rank,Nat.mul_comm] using h.symm

end
end IntegerMultBounds.Machine.CompactPhaseRecordEmbedding
