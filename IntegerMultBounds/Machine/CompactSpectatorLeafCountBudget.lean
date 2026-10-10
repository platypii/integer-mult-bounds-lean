import IntegerMultBounds.Machine.CompactComplexChildHeadersData
import IntegerMultBounds.Machine.CompactComplexLeafHeadersData

/-! A positive-exponent node stores its child-slot width in original header7.
The stopped whole-node leaf must physically expand that width by original
header6, then restore it after execution. Both schedules reclaim scratch22. -/
namespace IntegerMultBounds.Machine.CompactSpectatorLeafCountBudget
noncomputable section
open CompactChildHeadersArithmetic
open ActiveRepairRankHeadersCommands (State put)

def expand : List Op := [.existing (.product ![7,6,22] (by decide)),
  .existing (.command (.erase 7)),.existing (.command (.copy 22 7 (by decide))),
  .existing (.command (.erase 22))]
def restore : List Op := [.quotient ![7,6,22] (by decide),
  .existing (.command (.erase 7)),.existing (.command (.copy 22 7 (by decide))),
  .existing (.command (.erase 22))]
def expanded (st : State) (slots count : ℕ) : State := put st 7 (count*slots)

theorem expand_eval (st : State) (slots count : ℕ)
    (h6 : st 6=some slots) (h7 : st 7=some count) (h22 : st 22=none) :
    execute expand st=expanded st slots count := by
  funext i
  simp [expand,execute,eval,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,
    expanded,put,Function.update,h6,h7]
  split_ifs <;> simp_all [Nat.mul_comm]

theorem expand_valid (st : State) (slots count : ℕ)
    (h6 : st 6=some slots) (h7 : st 7=some count) (h22 : st 22=none)
    (hc : 0<count) : validSchedule expand st := by
  simp [expand,validSchedule,valid,eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,put,Function.update,h6,h7,h22,hc]

theorem restore_eval (st : State) (slots count : ℕ)
    (h6 : st 6=some slots) (h7 : st 7=some count) (h22 : st 22=none) (hs : 0<slots) :
    execute restore (expanded st slots count)=st := by
  have hd : count*slots/slots=count := Nat.mul_div_cancel count hs
  funext i
  simp [restore,execute,eval,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,
    expanded,put,Function.update,h6,hd]
  split_ifs <;> simp_all

theorem restore_valid (st : State) (slots count : ℕ)
    (h6 : st 6=some slots) (_h7 : st 7=some count) (h22 : st 22=none) (hs : 0<slots) :
    validSchedule restore (expanded st slots count) := by
  have hd : count*slots/slots=count := Nat.mul_div_cancel count hs
  simp [restore,validSchedule,valid,eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,expanded,put,Function.update,h6,h22,hd,hs]

variable {a : ℕ}

theorem expand_runs (st : State) (slots count : ℕ)
    (h6 : st 6=some slots) (h7 : st 7=some count) (h22 : st 22=none) (hc : 0<count) :
    HoareTime (compile (a:=a) expand).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank st)
      (fun v => v=ActiveRepairRankHeadersCommands.bank (expanded st slots count))
      (scheduleCost expand st) := by
  have hh := schedule_runs (a:=a) expand st (expand_valid st slots count h6 h7 h22 hc)
  rwa [expand_eval st slots count h6 h7 h22] at hh

theorem restore_runs (st : State) (slots count : ℕ)
    (h6 : st 6=some slots) (h7 : st 7=some count) (h22 : st 22=none) (hs : 0<slots) :
    HoareTime (compile (a:=a) restore).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (expanded st slots count))
      (fun v => v=ActiveRepairRankHeadersCommands.bank st)
      (scheduleCost restore (expanded st slots count)) := by
  have hh := schedule_runs (a:=a) restore (expanded st slots count) (restore_valid st slots count h6 h7 h22 hs)
  rwa [restore_eval st slots count h6 h7 h22 hs] at hh

/-- This is the live original node state, not arbitrary leaf readiness. -/
theorem node_expanded_count {s : CompactGadgetReservationShape.Shape} (rho : Fin s.chunk) {left k : ℕ}
    (visit : CompactComplexRecursiveGeometry.Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin CompactComplexRecursiveGeometry.arity)) (rows : ℕ) :
    execute expand (ActivePrefixStageHeadersData.initial
      (CompactBinaryBasisSchedule.stage (CompactComplexRecursiveGeometry.node rho visit hactive) pair) rows) 7=
      some (CompactComplexRecursiveGeometry.arity^(k+1)) := by
  rw [expand_eval _ CompactComplexRecursiveGeometry.arity (CompactComplexRecursiveGeometry.arity^k) rfl rfl rfl]
  simp [expanded,put,Function.update,pow_succ]

/-- Scalar child preparation already writes the literal exponent-zero Visit
length1. Expanding by the retained arity at exponent0 would be incorrect. -/
theorem scalar_count {s : CompactGadgetReservationShape.Shape} (rho : Fin s.chunk)
    (slot : Fin CompactComplexRecursiveGeometry.arity) (rows : ℕ)
    (pair : Networks.BinaryRowProgram.Op (Fin CompactComplexRecursiveGeometry.arity)) (left : ℕ) :
    CompactComplexLeafHeadersData.leaf rho slot rows pair left 7=
      some (CompactComplexRecursiveGeometry.arity^0) := by
  simp [CompactComplexLeafHeadersData.leaf,CompactComplexLeafHeadersData.values]

theorem expand_cost (st : State) (slots count : ℕ)
    (h6 : st 6=some slots) (h7 : st 7=some count) :
    scheduleCost expand st≤400*(count*slots+count+1) := by
  simp [expand,scheduleCost,cost,eval,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,put,Function.update,h6,h7]
  nlinarith

theorem restore_cost (st : State) (slots count : ℕ)
    (h6 : st 6=some slots) (hs : 0<slots) :
    scheduleCost restore (expanded st slots count)≤10000*(count*slots+slots+count+1)^2 := by
  let B := count*slots+slots+count+1
  have hb : 1≤B := by dsimp [B]; omega
  have hn : count*slots≤B := by dsimp [B]; omega
  have hs' : slots≤B := by dsimp [B]; omega
  have hc : count≤B := by dsimp [B]; omega
  have hy := ActiveRepairRankHeadersCommands.bits_length (count*slots)
  have hd := ActiveRepairRankHeadersCommands.bits_length slots
  have ht := BinaryDescriptorDivision.cost_le
    (RecursiveChildQuotientsConstant.bits (count*slots)) (RecursiveChildQuotientsConstant.bits slots)
  have hyl : (RecursiveChildQuotientsConstant.bits (count*slots)).length≤2*B := by omega
  have hdl : (RecursiveChildQuotientsConstant.bits slots).length≤2*B := by omega
  have hi : 4*(RecursiveChildQuotientsConstant.bits (count*slots)).length+
      6*(RecursiveChildQuotientsConstant.bits slots).length+30≤50*B := by omega
  have hm := Nat.mul_le_mul hyl hi
  have ht' : BinaryDescriptorDivision.cost
      (RecursiveChildQuotientsConstant.bits (count*slots)) (RecursiveChildQuotientsConstant.bits slots)≤5000*B^2 := by
    nlinarith
  have hdiv : count*slots/slots=count := Nat.mul_div_cancel count hs
  simp [restore,scheduleCost,cost,eval,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,expanded,put,Function.update,h6,hdiv]
  change _≤10000*B^2
  nlinarith

end
end IntegerMultBounds.Machine.CompactSpectatorLeafCountBudget
