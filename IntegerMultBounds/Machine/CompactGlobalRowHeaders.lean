import IntegerMultBounds.Machine.CompactGlobalRowHeaderOps
import IntegerMultBounds.Machine.CompactGlobalRowPadding

/-! The original public words K,d,D,payload determine every global row-padding
header. The network constants c,m are fixed program parameters, never supplied
as generated numeric descriptors. Private arithmetic scratch is erased. -/
namespace IntegerMultBounds.Machine.CompactGlobalRowHeaders
noncomputable section
open CompactGlobalRowHeaderOps
open ActiveRepairRankHeadersCommands (State put)
open CompactGlobalRowPadding
variable {a : ℕ}

def originalValues (K d D payload : ℕ) : Fin 4 → ℕ := ![K,d,D,payload]
def initial (K d D payload : ℕ) : State := fun i =>
  if h : i.val<4 then some (originalValues K d D payload ⟨i.val,h⟩) else none

def recordWidth (c m d D K payload : ℕ) := 2^((D-rowAxes c m d)*K)*payload

def first (c m : ℕ) : List Op := [
  .constant (Nat.clog 2 c) 4,
  .ordinary (.command (.copy 1 5 (by decide))),
  .ordinary (.command (.add 5 1 (by decide))),
  .logarithm m ![5,6] (by decide),
  .ordinary (.product ![4,6,7] (by decide)),
  .logarithm m ![1,8] (by decide),
  .power c ![8,9] (by decide)]

def second : List Op := [
  .ordinary (.product ![0,7,10] (by decide)),
  .power 2 ![10,11] (by decide),
  .ordinary (.command (.difference 2 7 12 (by decide))),
  .ordinary (.product ![0,12,13] (by decide)),
  .power 2 ![13,14] (by decide),
  .ordinary (.product ![3,14,15] (by decide)),
  .ordinary (.round ![11,9,16] (by decide)),
  .constant 1 17]

def construction (c m : ℕ) := first c m++second

def scratch : List (Fin 28) := [4,5,6,10,12,13,14]
def cleanup := scratch.map (fun i => Op.ordinary (.command (.erase i)))
def schedule (c m : ℕ) := construction c m++cleanup

def finished (c m d D K payload : ℕ) : State := fun i =>
  if h : i.val<4 then some (originalValues K d D payload ⟨i.val,h⟩) else
  match i.val with
  | 7 => some (rowAxes c m d)
  | 8 => some (depth m d)
  | 9 => some (c^depth m d)
  | 11 => some (originalRows c m d K)
  | 15 => some (recordWidth c m d D K payload)
  | 16 => some (initialRows c m d K)
  | 17 => some 1
  | _ => none

theorem logc_positive (c : ℕ) (hc : 2≤c) : 0 < Nat.clog 2 c := by
  have h := Nat.le_pow_clog (by decide : 1<2) c
  by_contra hh
  have he : Nat.clog 2 c=0 := by omega
  simp only [he,pow_zero] at h
  omega

theorem valid_schedule (c m d D K payload : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hK : 0<K) (hp : 0<payload) (hD : rowAxes c m d≤D) :
    validSchedule (schedule c m) (initial K d D payload) := by
  have hlog := logc_positive c hc
  have htwo : d+d=2*d := by omega
  have hpow : 0<c^Nat.clog m d := pow_pos (by omega) _
  have hpow2 : ∀ n : ℕ, 0<(2:ℕ)^n := fun n => pow_pos (by decide) n
  simp [schedule,construction,first,second,cleanup,scratch,validSchedule,valid,eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,
    put,initial,originalValues,Function.update,htwo,rowAxes,Nat.mul_comm] at hD ⊢
  omega

theorem executes (c m d D K payload : ℕ) (hc : 2≤c) :
    execute (schedule c m) (initial K d D payload) = finished c m d D K payload := by
  have htwo : d+d=2*d := by omega
  have hround := CompactRowPaddingRound.rounded_eq (originalRows c m d K) (c^depth m d)
    (pow_pos (by decide) _) (pow_pos (by omega) _)
  funext i
  fin_cases i
  all_goals simp [schedule,construction,first,second,cleanup,scratch,execute,eval,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,
    put,initial,originalValues,Function.update,finished,htwo,recordWidth,
    rowAxes,depth,originalRows,initialRows,Nat.mul_comm] at *
  exact hround

 def program (c m : ℕ) := (compile (a := a) (schedule c m)).2
 def cost (c m d D K payload : ℕ) := scheduleCost (schedule c m) (initial K d D payload)

theorem runs (c m d D K payload : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hK : 0<K) (hp : 0<payload) (hD : rowAxes c m d≤D) :
    HoareTime (program (a := a) c m)
      (fun v => v=ActiveRepairRankHeadersCommands.bank (initial K d D payload))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (finished c m d D K payload))
      (cost c m d D K payload) := by
  have h := schedule_runs (a := a) (schedule c m) (initial K d D payload)
    (valid_schedule c m d D K payload hc hm hd hK hp hD)
  simpa only [executes c m d D K payload hc,program,cost] using h

end
end IntegerMultBounds.Machine.CompactGlobalRowHeaders
