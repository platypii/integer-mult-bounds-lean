import IntegerMultBounds.Machine.CompactComplexChildHeadersData

/-! A polynomial descriptor cost for the paid physical child-header schedule.
This bound counts quotient, product, constant writing and all erasures. -/
namespace IntegerMultBounds.Machine.CompactComplexChildHeadersBudget
open CompactChildHeadersArithmetic CompactComplexChildHeadersData
open ActiveRepairRankHeadersCommands (State)
open RecursiveChildQuotientsConstant (bits)

/-- Only the six consumed numeric values enter the budget; payload and row
counts are retained without being read by this arithmetic schedule. -/
theorem cost_le (slot : Fin CompactComplexRecursiveGeometry.arity) (st : State)
    (active slots width left right : ℕ)
    (h3 : st 3 = some active) (h6 : st 6 = some slots) (h7 : st 7 = some width)
    (h8 : st 8 = some left) (h9 : st 9 = some right) :
    scheduleCost (schedule slot) st ≤
      100000*(active+slots+width+left+right+slot.val+1)^2 := by
  let B := active+slots+width+left+right+slot.val+1
  have hb : 1 ≤ B := by dsimp [B]; omega
  have hw : width ≤ B := by dsimp [B]; omega
  have hm : slots ≤ B := by dsimp [B]; omega
  have hl : left ≤ B := by dsimp [B]; omega
  have hr : right ≤ B := by dsimp [B]; omega
  have ha : active ≤ B := by dsimp [B]; omega
  have hs : slot.val ≤ B := by dsimp [B]; omega
  have hq : width/slots ≤ B := (Nat.div_le_self _ _).trans hw
  have hsf : slot.val*width ≤ B*B := Nat.mul_le_mul hs hw
  have hmq : width/slots*slots ≤ B*B := Nat.mul_le_mul hq hm
  have hsub : active-(width/slots*slots+(left+slot.val*width)) ≤ active := Nat.sub_le _ _
  have hbitsw := ActiveRepairRankHeadersCommands.bits_length width
  have hbitsm := ActiveRepairRankHeadersCommands.bits_length slots
  have hbitss := ActiveRepairRankHeadersCommands.bits_length slot.val
  have hd := BinaryDescriptorDivision.cost_le (bits width) (bits slots)
  have hdBound : BinaryDescriptorDivision.cost (bits width) (bits slots) ≤ 5000*B^2 := by
    have hw' : (bits width).length ≤ 2*B := by omega
    have hm' : (bits slots).length ≤ 2*B := by omega
    have hinner : 4*(bits width).length+6*(bits slots).length+30 ≤ 50*B := by omega
    have hprod := Nat.mul_le_mul hw' hinner
    nlinarith
  simp [schedule,scheduleCost,cost,eval,ActivePrefixStageHeadersOps.cost,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    RecursiveChildQuotientsConstant.cost,Function.update,h3,h6,h7,h8,h9]
  change _ ≤ 100000*B^2
  nlinarith

end IntegerMultBounds.Machine.CompactComplexChildHeadersBudget
