import IntegerMultBounds.Machine.CompactComplexChildHeadersData

/-! Exponent-zero children are scalar leaves, not internal arity-slot stages.
Their thirteen-header bank records one selected coordinate, retaining the
parent arity and pair labels; no fictitious zero-width Stage is introduced. -/
namespace IntegerMultBounds.Machine.CompactComplexLeafHeadersData
noncomputable section
open CompactChildHeadersArithmetic CompactComplexRecursiveGeometry
open CompactBinaryBasisSchedule ActivePrefixStageParameters
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageHeadersData (initial)
open Networks.BinaryRowProgram (Op)

def schedule (slotValue : ℕ) : List CompactChildHeadersArithmetic.Op :=
  [.constant 22 slotValue,
   .existing (.command (.copy 8 24 (by decide))),
   .existing (.command (.add 24 22 (by decide))),
   .constant 26 1,
   .existing (.command (.add 26 24 (by decide))),
   .existing (.command (.difference 3 26 27 (by decide))),
   .existing (.command (.erase 8)), .existing (.command (.copy 24 8 (by decide))),
   .existing (.command (.erase 9)), .existing (.command (.copy 27 9 (by decide))),
   .existing (.command (.erase 22)), .existing (.command (.erase 24)),
   .existing (.command (.erase 26)), .existing (.command (.erase 27))]

variable {s : Shape} (rho : Fin s.chunk) {left : ℕ}
  (visit : Visit s.active left 1) (hactive : s.active ≤ s.axes)
  (pair : Op (Fin arity)) (slot : Fin arity) (rows : ℕ)

def parent := stage (node rho visit hactive) pair

def values (leafPair : Op (Fin arity)) (leafLeft : ℕ) : Fin 13 → ℕ :=
  ![s.chunk,s.axes,s.guard,s.active,rows,s.payload,arity,1,leafLeft+slot.val,
    s.active-(leafLeft+slot.val+1),rho.val,leafPair.source.val,leafPair.target.val]

def leaf (leafPair : Op (Fin arity)) (leafLeft : ℕ) : ActiveRepairRankHeadersCommands.State := fun i =>
  if h : i.val < 13 then some (values rho slot rows leafPair leafLeft ⟨i.val,h⟩) else none

theorem execute_eq : execute (schedule slot.val) (initial (parent rho visit hactive pair) rows) =
    leaf rho slot rows pair left := by
  funext i
  fin_cases i <;> simp [schedule,execute,eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,initial,
    ActivePrefixStageHeadersData.originalValues,parent,stage,node,leaf,values,Function.update]
  rw [Nat.add_comm 1]

private theorem valid_state (slotValue active start right : ℕ)
    (st : ActiveRepairRankHeadersCommands.State)
    (h3 : st 3 = some active) (h8 : st 8 = some start) (h9 : st 9 = some right)
    (h22 : st 22 = none) (h24 : st 24 = none) (h26 : st 26 = none) (h27 : st 27 = none)
    (hfit : start+slotValue+1 ≤ active) : validSchedule (schedule slotValue) st := by
  simp [schedule,validSchedule,valid,eval,ActivePrefixStageHeadersOps.valid,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,Function.update,
    h3,h8,h9,h22,h24,h26,h27]
  simpa only [Nat.add_comm] using hfit

private theorem initial_active (v : Stage s) (rows : ℕ) : initial v rows 3 = some s.active := rfl
private theorem initial_left (v : Stage s) (rows : ℕ) : initial v rows 8 = some v.left := rfl
private theorem initial_right (v : Stage s) (rows : ℕ) : initial v rows 9 = some v.right := rfl
private theorem initial_empty (v : Stage s) (rows : ℕ) (i : Fin 28) (hi : 13 ≤ i.val) :
    initial v rows i = none := by simp [initial,show ¬i.val < 13 by omega]

private theorem valid_stage (v : Stage s) (rows slotValue : ℕ)
    (hfit : v.left+slotValue+1 ≤ s.active) : validSchedule (schedule slotValue) (initial v rows) :=
  valid_state slotValue s.active v.left v.right (initial v rows)
    (initial_active v rows) (initial_left v rows) (initial_right v rows)
    (initial_empty v rows 22 (by decide)) (initial_empty v rows 24 (by decide))
    (initial_empty v rows 26 (by decide)) (initial_empty v rows 27 (by decide)) hfit

theorem schedule_valid : validSchedule (schedule slot.val) (initial (parent rho visit hactive pair) rows) := by
  apply valid_stage
  simpa only [parent,stage,node,pow_zero,mul_one] using (Visit.child visit slot).fits

variable {a : ℕ}

theorem runs : HoareTime (compile (a := a) (schedule slot.val)).2
    (fun x => x = ActiveRepairRankHeadersCommands.bank (initial (parent rho visit hactive pair) rows))
    (fun x => x = ActiveRepairRankHeadersCommands.bank (leaf rho slot rows pair left))
    (scheduleCost (schedule slot.val) (initial (parent rho visit hactive pair) rows)) := by
  have h := schedule_runs (a := a) (schedule slot.val) (initial (parent rho visit hactive pair) rows)
    (schedule_valid rho visit hactive pair slot rows)
  rw [execute_eq] at h
  exact h

/-- The scalar leaf is literally the selected coordinate in the original chunk. -/
def bitPosition (leafLeft : ℕ) := (leafLeft+slot.val)*s.chunk+rho.val

include visit in
theorem bitPosition_lt : bitPosition rho slot left < s.active*s.chunk := by
  have hfit := (Visit.child visit slot).fits
  simp only [pow_zero,mul_one] at hfit
  have hmul := Nat.mul_le_mul_right s.chunk hfit
  rw [Nat.add_mul,one_mul] at hmul
  have hr := rho.isLt
  unfold bitPosition
  omega


/-- Leaf preparation has linear descriptor cost: no internal-node quotient
or product is executed at exponent zero. -/
theorem cost_le (slotValue active start right : ℕ) (st : ActiveRepairRankHeadersCommands.State)
    (h3 : st 3 = some active) (h8 : st 8 = some start) (h9 : st 9 = some right) :
    scheduleCost (schedule slotValue) st ≤ 10000*(active+start+right+slotValue+1) := by
  have hs := ActiveRepairRankHeadersCommands.bits_length slotValue
  have h1 := ActiveRepairRankHeadersCommands.bits_length 1
  have hsub : active-(1+(start+slotValue)) ≤ active := Nat.sub_le _ _
  simp [schedule,scheduleCost,cost,eval,ActivePrefixStageHeadersOps.cost,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    RecursiveChildQuotientsConstant.cost,Function.update,h3,h8,h9]
  omega

def placedProgram (slotValue : ℕ) := extend (compile (a := a) (schedule slotValue)).2 23

theorem runs_framed (tail : Tapes 23 a) : HoareTime (placedProgram (a := a) slot.val)
    (fun x => x = (ActiveRepairRankHeadersCommands.bank
      (initial (parent rho visit hactive pair) rows)).append tail)
    (fun x => x = (ActiveRepairRankHeadersCommands.bank (leaf rho slot rows pair left)).append tail)
    (scheduleCost (schedule slot.val) (initial (parent rho visit hactive pair) rows)) :=
  hoare_extend_eq (runs rho visit hactive pair slot rows) tail

end
end IntegerMultBounds.Machine.CompactComplexLeafHeadersData
