import IntegerMultBounds.Machine.UnitPhaseStreamLoop

/-! Every phase record costs linear time in reserved payload and signed
coefficient width, including actual address generation and all cleanup.
The original-header stream loop retains the resulting aggregate bound. -/
namespace IntegerMultBounds.Machine.UnitPhaseStreamBudget
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open UnitPhaseRecordKernel (headerWords)
variable {s : Shape}

theorem count_le_bits (v : Stage s) (m : ℕ) (hslots : m≤v.slots) : m≤s.bits := by
  have hf := v.positiveWidth
  have hsplit := v.activeAxes
  have hm := (Nat.le_mul_of_pos_right v.slots hf).trans (by omega : v.slots*v.f≤s.active)
  have hq : 0<s.chunk := by have := v.selectedFits; omega
  have hactive := Nat.le_mul_of_pos_right s.active hq
  unfold Shape.bits
  omega

theorem values_le_bits (v : Stage s) (axis : Fin v.f) (m : ℕ) (hm : 0<m) (hslots : m≤v.slots)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<s.bits)
    (i : Fin 3) : SparsePhaseHeadersData.values v axis m i≤s.bits := by
  have hf := v.positiveWidth
  have hsplit := v.activeAxes
  have hslotspos : 0<v.slots := by omega
  have hfc := Nat.mul_le_mul_right s.chunk
    ((Nat.le_mul_of_pos_left v.f hslotspos).trans (by omega : v.slots*v.f≤s.active))
  have hm := count_le_bits v m hslots
  fin_cases i
  · change v.f*s.chunk≤s.bits; unfold Shape.bits; omega
  · change m-1≤s.bits; omega
  · change SparsePhaseHeadersData.offset v axis m≤s.bits; omega

theorem cleanup_bound (v : Stage s) (axis : Fin v.f) (m : ℕ) (hm : 0<m) (hslots : m≤v.slots)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<s.bits)
    (hrecord : s.bits+1≤s.payload) :
    BinaryDescriptorCleanupList.cost UnitPhaseLocalReset.headerSlots (headerWords v axis m)≤6*s.payload+15 := by
  have hl (i : Fin 3) : (SparsePhaseUnitCaller.headers v axis m i).length≤s.payload :=
    (ActiveRepairRankHeadersCommands.bits_length _).trans
      ((Nat.add_le_add_right (values_le_bits v axis m hm hslots hspan i) 1).trans hrecord)
  have h0 := hl 0
  have h1 := hl 1
  have h2 := hl 2
  simp only [BinaryDescriptorCleanupList.cost,UnitPhaseLocalReset.headerSlots,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil,headerWords,ite_true,show (23 : Fin 60) ≠ 22 by decide,
    show (24 : Fin 60) ≠ 22 by decide,show (24 : Fin 60) ≠ 23 by decide,ite_false]
  omega

theorem body_bound (v : Stage s) (axis : Fin v.f) (m w i : ℕ) (hm : 0<m) (hslots : m≤v.slots)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<s.bits)
    (hrecord : s.bits+1≤s.payload) :
    UnitPhaseStreamLoop.bodyCost v axis m w i≤10600*s.payload+24*w := by
  have hc := cleanup_bound v axis m hm hslots hspan hrecord
  have hm' := (count_le_bits v m hslots).trans (by omega : s.bits≤s.payload)
  have hl : (UnitPhaseRecordKernel.selected v axis m (BinaryAddressTableData.row s.bits i)).length=m := by
    simp only [UnitPhaseRecordKernel.selected,SparseWeightedUnitPhase.selected,SelectedSourceBitsData.selected_length]
    omega
  unfold UnitPhaseStreamLoop.bodyCost UnitPhaseRecordFull.cost UnitPhaseRecord.cost UnitPhaseRecordKernel.cost
  rw [hl]
  omega

theorem loop_bound (v : Stage s) (axis : Fin v.f) (m w rows : ℕ) (hm : 0<m) (hslots : m≤v.slots)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<s.bits)
    (hrecord : s.bits+1≤s.payload) :
    CountedLoopHeaderClean.cost rows (RecursiveChildQuotientsConstant.bits rows)
      (UnitPhaseStreamLoop.bodyCost v axis m w)≤rows*(10620*s.payload+24*w)+46 := by
  have hsum : (∑ i ∈ Finset.range rows,UnitPhaseStreamLoop.bodyCost v axis m w i)≤
      rows*(10600*s.payload+24*w) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range rows,(10600*s.payload+24*w) :=
        Finset.sum_le_sum (fun i _ => body_bound v axis m w i hm hslots hspan hrecord)
      _ = _ := by simp
  have hl := ActiveRepairRankHeadersCommands.bits_length rows
  have hp : 1≤s.payload := by omega
  have hx := Nat.mul_le_mul_left rows hp
  unfold CountedLoopHeaderClean.cost
  nlinarith

end IntegerMultBounds.Machine.UnitPhaseStreamBudget
