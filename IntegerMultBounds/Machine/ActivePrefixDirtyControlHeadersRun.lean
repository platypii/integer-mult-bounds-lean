import IntegerMultBounds.Machine.ActivePrefixDirtyControlHeadersData

/-! Actual full-header producer and cleanup for the dirty-control consumers.
The complete 43-tape bank preserves originals and erases all scratch words. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlHeadersRun
noncomputable section
open ActiveRepairRankHeadersCommands ActivePrefixLayoutHeadersData
open ActivePrefixDirtyControlHeadersData
variable {a : ℕ}

def program (k : Kind) := seq (ActivePrefixLayoutHeadersRun.program (a := a) (mode k))
  (compile (a := a) (patch k)).snd
def cost (k : Kind) (d : Inputs) := ActivePrefixLayoutHeadersRun.cost (mode k) d+1+
  scheduleCost (patch k) (ActivePrefixLayoutHeadersData.finished (mode k) d)
def cleanupProgram := (compile (a := a) outputCleanup).snd
def cleanupCost (k : Kind) (d : Inputs) := scheduleCost outputCleanup (finished k d)

theorem runs (k : Kind) (d : Inputs) (hw : d.w≤d.H) :
    HoareTime (program (a := a) k) (fun v => v=bank (initial d))
      (fun v => v=bank (finished k d)) (cost k d) := by
  have hp := schedule_runs (a := a) (patch k) (ActivePrefixLayoutHeadersData.finished (mode k) d)
    (patch_valid k d hw)
  rw [patch_eq] at hp
  exact (ActivePrefixLayoutHeadersRun.runs (mode k) d hw).seq hp

theorem produces (k : Kind) (d : Inputs) (hw : d.w≤d.H) (hs : Fin 14 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=originalValues d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a) k) (fun v => v=ActivePrefixLayoutHeadersEndpoint.input hs)
      (fun v => v=bank (finished k d)) (cost k d) := by
  rw [ActivePrefixLayoutHeadersEndpoint.input_eq d hs hv hc]
  exact runs k d hw

theorem cleans (k : Kind) (d : Inputs) :
    HoareTime (cleanupProgram (a := a)) (fun v => v=bank (finished k d))
      (fun v => v=bank (initial d)) (cleanupCost k d) := by
  have h := schedule_runs (a := a) outputCleanup (finished k d) (cleanup_valid k d)
  rwa [ActivePrefixDirtyControlHeadersData.cleanup_eq] at h

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlHeadersRun
