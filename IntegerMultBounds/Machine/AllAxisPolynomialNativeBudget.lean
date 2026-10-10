import IntegerMultBounds.Machine.AllAxisPolynomialNative
import IntegerMultBounds.Machine.AllAxisPolynomialBudget

/-! Linear-volume budget for the fully normalized polynomial phase machine,
including immutable-ell synthesis, both counted loops, every control erase,
stream rewinds, destructive overwrite and source-head return. -/
namespace IntegerMultBounds.Machine.AllAxisPolynomialNativeBudget
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
variable {s : Shape}

theorem cost_bound (order : Order) (v : Stage s) (rows : ℕ) (hr : 0<rows)
    (m ell w : ℕ) (hm : 0<m) (hslots : m≤v.slots)
    (hspan : AllAxisPhaseHeadersData.offset v m+(m*v.f-1)*s.chunk<s.bits)
    (hrecord : s.bits+1≤s.payload) (hR : 2^ell≤s.payload) :
    AllAxisPolynomialNative.cost order v rows m ell w≤
      (rows*2^s.bits)*((2*FixedBasePowerDescriptor.constant 2+15000)*s.payload+34*2^ell*w) := by
  let N := rows*2^s.bits
  let R := 2^ell
  have hn : 1≤N := Nat.mul_pos hr (by positivity)
  have hp : 1≤s.payload := by omega
  have hNp : N≤N*s.payload := Nat.le_mul_of_pos_right _ (by omega)
  have hunit : 1≤N*s.payload := Nat.mul_pos (by omega) (by omega)
  have hPp : s.payload≤N*s.payload := Nat.le_mul_of_pos_left _ (by omega)
  have hRp : R≤N*s.payload := hR.trans hPp
  have hNRp : N*R≤N*s.payload := Nat.mul_le_mul_left N hR
  have hC := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) hRp
  have hinit := AllAxisFullStreamInitBudget.cost_payload order v rows hr hrecord
  change AllAxisFullStreamInit.cost order v rows≤(FixedBasePowerDescriptor.constant 2+2000)*N*s.payload at hinit
  have hloop := AllAxisPolynomialBudget.loop_bound v m R w N hm hslots hspan hrecord
  have hbitsN := ActiveRepairRankHeadersCommands.bits_length N
  have hbitsR := ActiveRepairRankHeadersCommands.bits_length R
  have hclean : BinaryDescriptorCleanupList.cost AllAxisPolynomialStreamClean.slots
      (AllAxisPolynomialStreamClean.words N R)≤2*N+2*R+14 := by
    simp only [BinaryDescriptorCleanupList.cost,AllAxisPolynomialStreamClean.slots,
      AllAxisPolynomialStreamClean.words,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      ite_true,show (60 : Fin 65)≠59 by decide,ite_false]
    omega
  unfold AllAxisPolynomialNative.cost
  change FixedBasePowerDescriptor.constant 2*R+AllAxisFullStreamInit.cost order v rows+1+
    CountedLoopHeaderClean.cost N (RecursiveChildQuotientsConstant.bits N)
      (AllAxisPolynomialStreamLoop.bodyCost v m R w)+1+
    (5*s.bits+11+BinaryDescriptorCleanupList.cost AllAxisPolynomialStreamClean.slots
      (AllAxisPolynomialStreamClean.words N R)+1)+1+5*(N*R)*(2*(w+1))+13≤
    N*((2*FixedBasePowerDescriptor.constant 2+15000)*s.payload+34*R*w)
  nlinarith

end IntegerMultBounds.Machine.AllAxisPolynomialNativeBudget
