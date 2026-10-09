import IntegerMultBounds.Machine.CompactGlobalRowInitialData

/-! All seven generated global headers are physically erased after padding.
The four original public words and arbitrary payload tapes are retained. -/
namespace IntegerMultBounds.Machine.CompactGlobalRowInitialCleanup
noncomputable section
open CompactGlobalRowHeaderOps
open CompactGlobalRowHeaders
open CompactGlobalRowPadding
open CompactGlobalRowInitialData (bank)
open ActiveRepairRankHeadersCommands (put)
variable {a : ℕ}

def slots : List (Fin 28) := [7,8,9,11,15,16,17]
def schedule := slots.map (fun i => Op.ordinary (.command (.erase i)))
def program := extend (compile (a := a) schedule).2 2

def cost (c m d D K P : ℕ) := scheduleCost schedule (finished c m d D K P)

theorem valid_schedule (c m d D K P : ℕ) : validSchedule schedule (finished c m d D K P) := by
  simp [schedule,slots,validSchedule,valid,eval,ActivePrefixStageHeadersOps.valid,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,finished,Function.update]

theorem executes (c m d D K P : ℕ) :
    execute schedule (finished c m d D K P)=initial K d D P := by
  funext i
  fin_cases i <;> simp [schedule,slots,execute,eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,finished,initial,Function.update]

theorem cost_eq (c m d D K P : ℕ) : cost c m d D K P =
    100*(rowAxes c m d+depth m d+c^depth m d+originalRows c m d K+
      recordWidth c m d D K P+initialRows c m d K+8)+7 := by
  simp [cost,schedule,slots,scheduleCost,CompactGlobalRowHeaderOps.cost,eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,
    finished,Function.update]
  ring

theorem runs (c m d D K P : ℕ) (source dest : ℤ → Fin (a+4)) (p q : ℤ) :
    HoareTime (program (a := a))
      (fun v => v=bank (finished c m d D K P) source dest p q)
      (fun v => v=bank (initial K d D P) source dest p q) (cost c m d D K P) := by
  have h := schedule_runs (a := a) schedule (finished c m d D K P) (valid_schedule c m d D K P)
  rw [executes] at h
  exact hoare_extend_eq h (CompactGlobalRowInitialData.payload source dest p q)

end
end IntegerMultBounds.Machine.CompactGlobalRowInitialCleanup
