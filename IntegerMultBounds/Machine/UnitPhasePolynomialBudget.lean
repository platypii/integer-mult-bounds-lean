import IntegerMultBounds.Machine.UnitPhasePolynomialStream
import IntegerMultBounds.Machine.UnitPhaseStreamBudget
import IntegerMultBounds.Machine.UnitPhaseFullStreamInitBudget

/-! Polynomial traversal counts phase setup once per address, while charging
coefficient arithmetic once per actual polynomial coefficient. The paid
inner loop descriptor preparation and erasure are included. -/
namespace IntegerMultBounds.Machine.UnitPhasePolynomialBudget
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
variable {s : Shape}

theorem body_bound (v : Stage s) (axis : Fin v.f) (m R w i : ℕ) (hm : 0<m) (hslots : m≤v.slots)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<s.bits)
    (hrecord : s.bits+1≤s.payload) :
    UnitPhasePolynomialStreamLoop.bodyCost v axis m R w i≤10600*s.payload+R*(24*w+100) := by
  have hc := UnitPhaseStreamBudget.cleanup_bound v axis m hm hslots hspan hrecord
  have hsame : BinaryDescriptorCleanupList.cost UnitPhaseControlReset.headerSlots (UnitPhaseRecordKernel.headerWords v axis m)=
      BinaryDescriptorCleanupList.cost UnitPhaseLocalReset.headerSlots (UnitPhaseRecordKernel.headerWords v axis m) := rfl
  have hm' := UnitPhaseStreamBudget.count_le_bits v m hslots
  have hl : (UnitPhaseRecordKernel.selected v axis m (BinaryAddressTableData.row s.bits i)).length=m := by
    simp only [UnitPhaseRecordKernel.selected,SparseWeightedUnitPhase.selected,SelectedSourceBitsData.selected_length]
    omega
  have hR := ActiveRepairRankHeadersCommands.bits_length R
  have hp : 1≤s.payload := by omega
  unfold UnitPhasePolynomialStreamLoop.bodyCost UnitPhaseControlReset.cost
  rw [hl,hsame]
  nlinarith

theorem loop_bound (v : Stage s) (axis : Fin v.f) (m R w N : ℕ) (hm : 0<m) (hslots : m≤v.slots)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<s.bits)
    (hrecord : s.bits+1≤s.payload) :
    CountedLoopHeaderClean.cost N (RecursiveChildQuotientsConstant.bits N)
      (UnitPhasePolynomialStreamLoop.bodyCost v axis m R w)≤
      N*(10620*s.payload+R*(24*w+100))+46 := by
  have hsum : (∑ i ∈ Finset.range N,UnitPhasePolynomialStreamLoop.bodyCost v axis m R w i)≤
      N*(10600*s.payload+R*(24*w+100)) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range N,(10600*s.payload+R*(24*w+100)) :=
        Finset.sum_le_sum (fun i _ => body_bound v axis m R w i hm hslots hspan hrecord)
      _ = _ := by simp
  have hl := ActiveRepairRankHeadersCommands.bits_length N
  have hp : 1≤s.payload := by omega
  have hx := Nat.mul_le_mul_left N hp
  unfold CountedLoopHeaderClean.cost
  nlinarith

end IntegerMultBounds.Machine.UnitPhasePolynomialBudget
