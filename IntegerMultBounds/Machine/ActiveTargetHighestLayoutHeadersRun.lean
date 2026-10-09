import IntegerMultBounds.Machine.ActiveTargetHighestLayoutHeadersData
import IntegerMultBounds.Machine.ActiveTargetHighestPairHeadersAtomic

/-! Charged physical construction and erasure of the highest-bit pair's
five original words from the existing fourteen layout headers. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestLayoutHeadersRun
noncomputable section
open ActiveRepairRankHeadersCommands
open ActivePrefixLayoutHeadersData (Inputs initial seeded)
open ActiveTargetHighestLayoutHeadersData
variable {a : ℕ}

def program (mode : Mode) := seq (ActiveTargetHighestPairHeadersAtomic.seedProgram (a := a) 24)
  (compile (schedule mode)).2
def cleanupProgram := (compile (a := a) cleanup).2

def cost (mode : Mode) (d : Inputs) := 9+1+scheduleCost (schedule mode) (seeded d)
def cleanupCost (mode : Mode) (d : Inputs) := scheduleCost cleanup (finished mode d)

theorem runs (mode : Mode) (d : Inputs) (hv : Valid mode d) :
    HoareTime (program (a := a) mode) (fun v => v=bank (initial d))
      (fun v => v=bank (finished mode d)) (cost mode d) := by
  have hs := ActiveTargetHighestPairHeadersAtomic.seed (a := a) (initial d) 24 (by rfl)
  have hm := schedule_runs (a := a) (schedule mode) (seeded d) (schedule_valid mode d hv)
  rw [schedule_eq] at hm
  exact hs.seq hm

theorem cleans (mode : Mode) (d : Inputs) :
    HoareTime (cleanupProgram (a := a)) (fun v => v=bank (finished mode d))
      (fun v => v=bank (initial d)) (cleanupCost mode d) := by
  have h := schedule_runs (a := a) cleanup (finished mode d) (cleanup_valid mode d)
  rw [cleanup_eq] at h
  exact h

end
end IntegerMultBounds.Machine.ActiveTargetHighestLayoutHeadersRun
