import IntegerMultBounds.Machine.CompactChildHeadersArithmetic

/-! The root-piece generator obtains each low-to-high base digit from its
actual remaining-prefix word. The fixed arithmetic schedule produces the
quotient and digit, replaces the remaining prefix, and cleans every private
operand. All other permanent controller fields and native tapes are framed. -/
namespace IntegerMultBounds.Machine.CompactComplexRootDigitRound
noncomputable section
open CompactChildHeadersArithmetic
open ActiveRepairRankHeadersCommands (State put bank)

/-- Relative controller slots zero and four hold remaining prefix and digit.
The controller bank is appended outside the native stage bank. -/
def schedule (base : ℕ) : List Op :=
  [.constant 22 base, .quotient ![0,22,23] (by decide),
    .existing (.product ![22,23,24] (by decide)),
    .existing (.command (.difference 0 24 25 (by decide))),
    .existing (.command (.copy 25 4 (by decide))),
    .existing (.command (.erase 0)), .existing (.command (.copy 23 0 (by decide))),
    .existing (.command (.erase 22)), .existing (.command (.erase 23)),
    .existing (.command (.erase 24)), .existing (.command (.erase 25))]

def finished (st : State) (remaining base : ℕ) := put (put st 0 (remaining/base)) 4 (remaining%base)

private theorem remainder_eq (remaining base : ℕ) :
    remaining-(remaining/base*base)=remaining%base := by
  have h : remaining=remaining%base+remaining/base*base := by
    simpa only [Nat.mul_comm] using (Nat.mod_add_div remaining base).symm
  conv_lhs => lhs; rw [h]
  exact Nat.add_sub_cancel _ _

theorem execute_eq (base remaining : ℕ) (st : State) (h0 : st 0 = some remaining)
    (h22 : st 22 = none) (h23 : st 23 = none) (h24 : st 24 = none) (h25 : st 25 = none) :
    execute (schedule base) st=finished st remaining base := by
  funext i
  by_cases hi0 : i=0
  · subst i
    simp [schedule,execute,eval,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,put,finished,Function.update,h0]
  by_cases hi4 : i=4
  · subst i
    simp [schedule,execute,eval,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,put,finished,Function.update,h0,remainder_eq]
  by_cases hi22 : i=22
  · subst i
    simp [schedule,execute,eval,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,put,finished,Function.update,h22]
  by_cases hi23 : i=23
  · subst i
    simp [schedule,execute,eval,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,put,finished,Function.update,h23]
  by_cases hi24 : i=24
  · subst i
    simp [schedule,execute,eval,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,put,finished,Function.update,h24]
  by_cases hi25 : i=25
  · subst i
    simp [schedule,execute,eval,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,put,finished,Function.update,h25]
  simp [schedule,execute,eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,put,finished,Function.update,hi0,hi4,hi22,hi23,hi24,hi25]

theorem valid (base remaining : ℕ) (hb : 0 < base) (st : State) (h0 : st 0 = some remaining)
    (h4 : st 4 = none) (h22 : st 22 = none) (h23 : st 23 = none)
    (h24 : st 24 = none) (h25 : st 25 = none) : validSchedule (schedule base) st := by
  simp [schedule,validSchedule,CompactChildHeadersArithmetic.valid,eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,
    put,Function.update,h0,h4,h22,h23,h24,h25,hb,Nat.div_mul_le_self]

variable {a : ℕ}
theorem runs (base remaining : ℕ) (hb : 0 < base) (st : State) (h0 : st 0 = some remaining)
    (h4 : st 4 = none) (h22 : st 22 = none) (h23 : st 23 = none)
    (h24 : st 24 = none) (h25 : st 25 = none) :
    HoareTime (compile (a := a) (schedule base)).2 (fun x => x=bank st)
      (fun x => x=bank (finished st remaining base)) (scheduleCost (schedule base) st) := by
  have h := schedule_runs (a := a) (schedule base) st
    (valid base remaining hb st h0 h4 h22 h23 h24 h25)
  rw [execute_eq base remaining st h0 h22 h23 h24 h25] at h
  exact h

/-- Every complete native tape and head belongs to the stationary frame. -/
theorem runs_framed {t : ℕ} (base remaining : ℕ) (hb : 0 < base) (st : State)
    (h0 : st 0 = some remaining) (h4 : st 4 = none) (h22 : st 22 = none)
    (h23 : st 23 = none) (h24 : st 24 = none) (h25 : st 25 = none) (native : Tapes t a) :
    HoareTime (extend (compile (a := a) (schedule base)).2 t)
      (fun x => x=(bank st).append native)
      (fun x => x=(bank (finished st remaining base)).append native)
      (scheduleCost (schedule base) st) :=
  hoare_extend_eq (runs base remaining hb st h0 h4 h22 h23 h24 h25) native


/-- The digit round uses descriptor-polynomial time in the remaining original
prefix and fixed base, including all quotient/product/cleanup transitions. -/
theorem cost_le (base remaining : ℕ) (st : State) (h0 : st 0 = some remaining) :
    scheduleCost (schedule base) st ≤ 100000*(remaining+base+1)^2 := by
  let B := remaining+base+1
  have hb : 1 ≤ B := by dsimp [B]; omega
  have hr : remaining ≤ B := by dsimp [B]; omega
  have hm : base ≤ B := by dsimp [B]; omega
  have hq : remaining/base ≤ B := (Nat.div_le_self _ _).trans hr
  have hprod : remaining/base*base ≤ remaining := Nat.div_mul_le_self _ _
  have hsub : remaining-(remaining/base*base) ≤ remaining := Nat.sub_le _ _
  have hlr := ActiveRepairRankHeadersCommands.bits_length remaining
  have hlm := ActiveRepairRankHeadersCommands.bits_length base
  have hd := BinaryDescriptorDivision.cost_le (RecursiveChildQuotientsConstant.bits remaining)
    (RecursiveChildQuotientsConstant.bits base)
  have hdBound : BinaryDescriptorDivision.cost (RecursiveChildQuotientsConstant.bits remaining)
      (RecursiveChildQuotientsConstant.bits base) ≤ 5000*B^2 := by
    have hrl : (RecursiveChildQuotientsConstant.bits remaining).length ≤ 2*B := by omega
    have hml : (RecursiveChildQuotientsConstant.bits base).length ≤ 2*B := by omega
    have hi : 4*(RecursiveChildQuotientsConstant.bits remaining).length+
        6*(RecursiveChildQuotientsConstant.bits base).length+30 ≤ 50*B := by omega
    have hp := Nat.mul_le_mul hrl hi
    nlinarith
  simp [schedule,scheduleCost,cost,eval,ActivePrefixStageHeadersOps.cost,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,put,Function.update,h0,RecursiveChildQuotientsConstant.cost]
  change _ ≤ 100000*B^2
  nlinarith

end
end IntegerMultBounds.Machine.CompactComplexRootDigitRound
