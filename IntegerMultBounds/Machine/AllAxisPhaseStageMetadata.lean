import IntegerMultBounds.Machine.ActivePrefixStageHeadersBudget

/-! Original thirteen numeric headers physically produce the complete stage
metadata for an all-axis phase caller. The remaining phase tapes, including
source56, immutable ell65 and edge token66, are stationary frame. Computed
stage headers are physically erased after the phase caller releases its own
workspace; there is no axis25 ordinal setup or per-axis metadata pass. -/
namespace IntegerMultBounds.Machine.AllAxisPhaseStageMetadata
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order initial finished)
open ActivePrefixStageHeadersSchedule (Ordered)
open ActiveRepairRankHeadersCommands (bank)
variable {s : Shape} {a extra : ℕ}

def setup (order : Order) := extend (ActivePrefixStageHeadersRun.program (a := a) order) extra

theorem setup_runs (order : Order) (v : Stage s) (rows : ℕ) (tail : Tapes extra a)
    (hG : 1≤s.guard) (ho : Ordered order v) :
    HoareTime (setup (a := a) order)
      (fun z => z=(bank (initial v rows)).append tail)
      (fun z => z=(bank (finished order v rows)).append tail)
      (ActivePrefixStageHeadersRun.cost order v rows) :=
  hoare_extend_eq (ActivePrefixStageHeadersRun.runs (a := a) order v rows hG ho) tail

def eraseSchedule : List ActivePrefixStageHeadersOps.Op :=
  [.command (.erase 13),.command (.erase 14),.command (.erase 15),
   .command (.erase 16),.command (.erase 17),.command (.erase 18),
   .command (.erase 19),.command (.erase 20),.command (.erase 21)]
def cleanup := extend (ActivePrefixStageHeadersOps.compile (a := a) eraseSchedule).2 extra

def cleanupCost (order : Order) (v : Stage s) (rows : ℕ) :=
  ActivePrefixStageHeadersOps.scheduleCost eraseSchedule (finished order v rows)

theorem cleanup_runs (order : Order) (v : Stage s) (rows : ℕ) (tail : Tapes extra a) :
    HoareTime (cleanup (a := a))
      (fun z => z=(bank (finished order v rows)).append tail)
      (fun z => z=(bank (initial v rows)).append tail) (cleanupCost order v rows) := by
  have hv : ActivePrefixStageHeadersOps.validSchedule eraseSchedule (finished order v rows) := by
    simp [eraseSchedule,ActivePrefixStageHeadersOps.validSchedule,ActivePrefixStageHeadersOps.valid,
      ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
      ActiveRepairRankHeadersCommands.eval,finished,Function.update]
  have he : ActivePrefixStageHeadersOps.execute eraseSchedule (finished order v rows)=initial v rows := by
    funext i; fin_cases i
    all_goals simp [eraseSchedule,ActivePrefixStageHeadersOps.execute,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,initial,finished,Function.update]
  have h := ActivePrefixStageHeadersOps.schedule_runs (a := a) eraseSchedule (finished order v rows) hv
  rw [he] at h
  exact hoare_extend_eq h tail

private theorem cleanup_bound (order : Order) (v : Stage s) (rows A : ℕ)
    (hv : ∀ i,ActivePrefixStageHeadersData.outputs order v i≤A) :
    cleanupCost order v rows≤2000*(A+1) := by
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  have h4 := hv 4
  have h5 := hv 5
  have h6 := hv 6
  have h7 := hv 7
  have h8 := hv 8
  simp [cleanupCost,eraseSchedule,ActivePrefixStageHeadersOps.scheduleCost,ActivePrefixStageHeadersOps.cost,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,finished,Function.update]
  omega

/-- Both metadata lifecycles fit a fixed constant times original record volume,
framing all coefficient, precision and dispatch tapes throughout. -/
theorem lifecycle_bound (order : Order) (v : Stage s) (rows : ℕ)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (ho : Ordered order v)
    (hr : 0<rows) (hrecord : s.bits+1≤s.payload) :
    ActivePrefixStageHeadersRun.cost order v rows+cleanupCost order v rows≤
      804000*(rows*s.recordWidth) := by
  obtain ⟨hvalues,houtputs⟩ := ActivePrefixStageHeadersBudget.original_bounds order v rows hG hGK ho hr hrecord
  have hs := ActivePrefixStageHeadersBudget.arithmetic_bound order v rows (rows*s.recordWidth) hG hvalues houtputs
  have hc := cleanup_bound order v rows (rows*s.recordWidth) houtputs
  have hp : 0<s.payload := by omega
  have hV : 0<rows*s.recordWidth := by unfold Shape.recordWidth; positivity
  omega

end
end IntegerMultBounds.Machine.AllAxisPhaseStageMetadata
