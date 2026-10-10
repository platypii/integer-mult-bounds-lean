import IntegerMultBounds.Machine.AllAxisFullStreamInit
import IntegerMultBounds.Machine.AllAxisAddressInitBudget

/-! Full coefficient count and counter preparation is linear in the actual
coefficient count times reserved payload, including generated descriptor
synthesis and physical transfer/erasure. -/
namespace IntegerMultBounds.Machine.AllAxisFullStreamInitBudget
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
variable {s : Shape}

theorem count_bound (order : Order) (v : Stage s) (rows : ℕ) (hr : 0<rows) :
    AllAxisCountHeaders.cost order v rows≤(FixedBasePowerDescriptor.constant 2+300)*(rows*2^s.bits) := by
  have hp : 1≤2^s.bits := Nat.one_le_pow _ _ (by decide)
  have hn : 2^s.bits≤rows*2^s.bits := Nat.le_mul_of_pos_left _ hr
  have hc := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) hn
  simp [AllAxisCountHeaders.cost,AllAxisCountHeaders.schedule,
    CompactChildHeadersArithmetic.scheduleCost,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,
    AllAxisCountHeaders.powerState,AllAxisAddressHeaders.finished,AllAxisAddressHeaders.initial,AllAxisPhaseHeadersData.initial,
    ActivePrefixStageHeadersData.finished,
    ActivePrefixStageHeadersData.originalValues,ActiveRepairRankHeadersCommands.put,Function.update]
  nlinarith

theorem cost_payload (order : Order) (v : Stage s) (rows : ℕ) 
    (hr : 0<rows) (hrecord : s.bits+1≤s.payload) :
    AllAxisFullStreamInit.cost order v rows≤
      (FixedBasePowerDescriptor.constant 2+2000)*(rows*2^s.bits)*s.payload := by
  have hd := AllAxisAddressInitBudget.derive_bound order v rows
  have hc := count_bound order v rows hr
  have hlw := ActiveRepairRankHeadersCommands.bits_length s.bits
  have hln := ActiveRepairRankHeadersCommands.bits_length (rows*2^s.bits)
  have hp : 1≤s.payload := by omega
  have hn : 1≤rows*2^s.bits := Nat.mul_pos hr (by positivity)
  have hnp := Nat.le_mul_of_pos_right (rows*2^s.bits) (by omega : 0<s.payload)
  have hpp := Nat.le_mul_of_pos_left s.payload (by omega : 0<rows*2^s.bits)
  have hscaled := hc.trans (Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2+300) hnp)
  unfold AllAxisFullStreamInit.cost
  nlinarith

end IntegerMultBounds.Machine.AllAxisFullStreamInitBudget
