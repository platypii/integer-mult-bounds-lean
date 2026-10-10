import IntegerMultBounds.Machine.AllAxisPolynomialStream
import IntegerMultBounds.Machine.AllAxisFullStreamInitBudget

/-! Aggregate phase extraction is paid once per address; coefficient work is
paid once per polynomial entry. Every generated descriptor is erased. -/
namespace IntegerMultBounds.Machine.AllAxisPolynomialBudget
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
variable {s : Shape}

theorem count_le_bits (v : Stage s) (m : ℕ) (hslots : m≤v.slots) : m*v.f≤s.bits := by
  have hs := v.activeAxes
  have hm := Nat.mul_le_mul_right v.f hslots
  have hq : 0<s.chunk := by have := v.selectedFits; omega
  have ha := Nat.le_mul_of_pos_right s.active hq
  unfold Shape.bits
  omega

theorem cleanup_bound (v : Stage s) (m : ℕ) (hm : 0<m) (hslots : m≤v.slots)
    (hspan : AllAxisPhaseHeadersData.offset v m+(m*v.f-1)*s.chunk<s.bits)
    (hrecord : s.bits+1≤s.payload) :
    BinaryDescriptorCleanupList.cost UnitPhaseControlReset.headerSlots
      (AllAxisPhaseFlagsEndpoint.headerWords v m)≤6*s.payload+15 := by
  have hmf := count_le_bits v m hslots
  have hq : s.chunk≤s.bits := by
    have hf := v.positiveWidth
    have hs := v.activeAxes
    have hslotspos : 0<v.slots := by omega
    have ha : 0<s.active := by nlinarith
    have h := Nat.le_mul_of_pos_left s.chunk ha
    unfold Shape.bits
    omega
  have h0 := ActiveRepairRankHeadersCommands.bits_length s.chunk
  have h1 := ActiveRepairRankHeadersCommands.bits_length (m*v.f-1)
  have h2 := ActiveRepairRankHeadersCommands.bits_length (AllAxisPhaseHeadersData.offset v m)
  simp only [BinaryDescriptorCleanupList.cost,UnitPhaseControlReset.headerSlots,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil,AllAxisPhaseFlagsEndpoint.headerWords,ite_true,
    show (23 : Fin 60)≠22 by decide,show (24 : Fin 60)≠22 by decide,
    show (24 : Fin 60)≠23 by decide,ite_false]
  omega

theorem body_bound (v : Stage s) (m R w i : ℕ) (hmpos : 0<m) (hslots : m≤v.slots)
    (hspan : AllAxisPhaseHeadersData.offset v m+(m*v.f-1)*s.chunk<s.bits)
    (hrecord : s.bits+1≤s.payload) :
    AllAxisPolynomialStreamLoop.bodyCost v m R w i≤10700*s.payload+R*(24*w+100) := by
  have hc := cleanup_bound v m hmpos hslots hspan hrecord
  have hm := count_le_bits v m hslots
  have hf := v.positiveWidth
  have hlf := ActiveRepairRankHeadersCommands.bits_length v.f
  have hR := ActiveRepairRankHeadersCommands.bits_length R
  have hscan : m*(7*v.f+11*(RecursiveChildQuotientsConstant.bits v.f).length+36)≤65*(m*v.f) := by
    have h := Nat.mul_le_mul_left m hlf
    have h' := Nat.mul_le_mul_left m (show 1≤v.f by omega)
    nlinarith
  have hl : (AllAxisPhaseFlagsCaller.controls v m (BinaryAddressTableData.row s.bits i)).length=m*v.f := by
    simp only [AllAxisPhaseFlagsCaller.controls,SelectedSourceBitsData.selected_length]
  have hp : 1≤s.payload := by omega
  unfold AllAxisPolynomialStreamLoop.bodyCost UnitPhaseControlReset.cost
  rw [hl]
  nlinarith

theorem loop_bound (v : Stage s) (m R w N : ℕ) (hmpos : 0<m) (hslots : m≤v.slots)
    (hspan : AllAxisPhaseHeadersData.offset v m+(m*v.f-1)*s.chunk<s.bits)
    (hrecord : s.bits+1≤s.payload) :
    CountedLoopHeaderClean.cost N (RecursiveChildQuotientsConstant.bits N)
      (AllAxisPolynomialStreamLoop.bodyCost v m R w)≤
      N*(10720*s.payload+R*(24*w+100))+46 := by
  have hsum : (∑ i ∈ Finset.range N,AllAxisPolynomialStreamLoop.bodyCost v m R w i)≤
      N*(10700*s.payload+R*(24*w+100)) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range N,(10700*s.payload+R*(24*w+100)) :=
        Finset.sum_le_sum (fun i _ => body_bound v m R w i hmpos hslots hspan hrecord)
      _ = _ := by simp
  have hl := ActiveRepairRankHeadersCommands.bits_length N
  have hp : 1≤s.payload := by omega
  have hx := Nat.mul_le_mul_left N hp
  unfold CountedLoopHeaderClean.cost
  nlinarith

end IntegerMultBounds.Machine.AllAxisPolynomialBudget
