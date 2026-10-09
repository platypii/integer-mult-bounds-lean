import IntegerMultBounds.Machine.CompactGlobalRowHeaders

/-! Exact physical header cost, decomposed at fixed schedule boundaries to
keep kernel checking within the project's default resource limits. -/
namespace IntegerMultBounds.Machine.CompactGlobalRowHeaderCost
open CompactGlobalRowHeaders
open CompactGlobalRowPadding
open CompactGlobalRowHeaderOps
open ActiveRepairRankHeadersCommands (State put)

def stageA (c m d D K P : ℕ) : State := fun i =>
  if h : i.val<4 then some (originalValues K d D P ⟨i.val,h⟩) else
  match i.val with
  | 4 => some (Nat.clog 2 c) | 5 => some (2*d) | 6 => some (Nat.clog m (2*d))
  | 7 => some (rowAxes c m d) | 8 => some (depth m d) | 9 => some (c^depth m d)
  | _ => none

def stageB (c m d D K P : ℕ) : State := fun i =>
  if h : i.val<4 then some (originalValues K d D P ⟨i.val,h⟩) else
  match i.val with
  | 4 => some (Nat.clog 2 c) | 5 => some (2*d) | 6 => some (Nat.clog m (2*d))
  | 7 => some (rowAxes c m d) | 8 => some (depth m d) | 9 => some (c^depth m d)
  | 10 => some (rowAxes c m d*K) | 11 => some (originalRows c m d K)
  | 12 => some (D-rowAxes c m d) | 13 => some ((D-rowAxes c m d)*K)
  | 14 => some (2^((D-rowAxes c m d)*K)) | 15 => some (recordWidth c m d D K P)
  | 16 => some (initialRows c m d K) | 17 => some 1 | _ => none

theorem execute_first (c m d D K P : ℕ) :
    execute (first c m) (initial K d D P)=stageA c m d D K P := by
  funext i
  fin_cases i <;> simp [first,execute,eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,put,initial,originalValues,stageA,Function.update,
    rowAxes,depth,two_mul,Nat.mul_comm]

theorem execute_second (c m d D K P : ℕ) (hc : 0<c) :
    execute second (stageA c m d D K P)=stageB c m d D K P := by
  have he := CompactRowPaddingRound.rounded_eq (originalRows c m d K) (c^depth m d)
    (pow_pos (by decide) _) (pow_pos hc _)
  funext i
  fin_cases i
  all_goals simp [second,execute,eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,put,originalValues,stageA,stageB,Function.update,
    originalRows,initialRows,recordWidth,Nat.mul_comm] at he ⊢
  exact he

theorem first_cost (c m d D K P : ℕ) :
    scheduleCost (first c m) (initial K d D P)=
      RecursiveChildQuotientsConstant.cost (Nat.clog 2 c)+300*d+
      CompactGlobalRowHeaderPrimitives.logConstant m*(3*d)+53*rowAxes c m d+
      FixedBasePowerDescriptor.constant c*c^depth m d+235 := by
  simp [first,scheduleCost,CompactGlobalRowHeaderOps.cost,eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,
    put,initial,originalValues,Function.update,rowAxes,depth]
  rw [show d+d=2*d by omega]
  ring

theorem second_cost (c m d D K P : ℕ) (hc : 0<c) :
    scheduleCost second (stageA c m d D K P)=
      53*(rowAxes c m d*K+(D-rowAxes c m d)*K+recordWidth c m d D K P)+
      FixedBasePowerDescriptor.constant 2*(originalRows c m d K+2^((D-rowAxes c m d)*K))+
      100*(D+rowAxes c m d)+4096*initialRows c m d K+201 := by
  have he := CompactRowPaddingRound.rounded_eq (originalRows c m d K) (c^depth m d)
    (pow_pos (by decide) _) (pow_pos hc _)
  simp [second,scheduleCost,CompactGlobalRowHeaderOps.cost,eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,
    put,stageA,originalValues,Function.update,originalRows,initialRows,recordWidth,Nat.mul_comm] at he ⊢
  rw [he]
  unfold RecursiveChildQuotientsConstant.cost
  rw [show (RecursiveChildQuotientsConstant.bits 1).length=1 by decide]
  ring

theorem scratch_cost (c m d D K P : ℕ) :
    scheduleCost cleanup (stageB c m d D K P)=
      100*(Nat.clog 2 c+2*d+Nat.clog m (2*d)+rowAxes c m d*K+
        (D-rowAxes c m d)+(D-rowAxes c m d)*K+2^((D-rowAxes c m d)*K))+707 := by
  simp [cleanup,scratch,scheduleCost,CompactGlobalRowHeaderOps.cost,eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,
    stageB,Function.update]
  ring

theorem cost_eq (c m d D K P : ℕ) (hc : 0<c) :
    CompactGlobalRowHeaders.cost c m d D K P =
      RecursiveChildQuotientsConstant.cost (Nat.clog 2 c)+
      CompactGlobalRowHeaderPrimitives.logConstant m*(3*d)+
      FixedBasePowerDescriptor.constant c*c^depth m d+
      FixedBasePowerDescriptor.constant 2*(originalRows c m d K+2^((D-rowAxes c m d)*K))+
      4096*initialRows c m d K+
      100*(Nat.clog 2 c+5*d+D+rowAxes c m d+Nat.clog m (2*d)+
        (D-rowAxes c m d)+2^((D-rowAxes c m d)*K))+
      153*(rowAxes c m d*K+(D-rowAxes c m d)*K)+
      53*(rowAxes c m d+recordWidth c m d D K P)+1143 := by
  unfold CompactGlobalRowHeaders.cost schedule construction
  rw [scheduleCost_append,scheduleCost_append,execute_append,execute_first,
    execute_second c m d D K P hc,first_cost,second_cost c m d D K P hc,scratch_cost]
  ring

end IntegerMultBounds.Machine.CompactGlobalRowHeaderCost
