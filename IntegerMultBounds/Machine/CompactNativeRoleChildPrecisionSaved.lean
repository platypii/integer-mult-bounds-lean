import IntegerMultBounds.Machine.CompactNativeRoleChildPrecision

/-! Payload reinterpretation may retain original header5 at numeric26. All
baseline conversion commands frame this saved descriptor literally, including
its marked binary word; its value does not affect the actual runtime. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleChildPrecisionSaved
noncomputable section
open ButterflyAxisHeadersArithmetic
open ActiveRepairRankHeadersCommands (State put)
open CompactNativeRoleChildPrecision (prepare restore baseline)
open CompactSpectatorLeafSetup (raw)
open CompactGadgetReservationShape (Shape)

theorem prepare_saved (st : State) (n : ℕ) :
    execute prepare (put st 26 n)=put (execute prepare st) 26 n := by
  funext i
  fin_cases i <;> simp [prepare,CompactSpectatorLeafSetup.geometry,ActivePrefixStageHeadersData.back,
    ActivePrefixStageHeadersData.front,ButterflyAxisHeadersData.product,
    ButterflyAxisHeadersData.cmd,CompactNativeRoleChildPrecision.cmd,execute,eval,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,put,Function.update]

theorem prepare_valid_saved (st : State) (n : ℕ) :
    validSchedule prepare (put st 26 n)↔validSchedule prepare st := by
  simp [prepare,CompactSpectatorLeafSetup.geometry,ActivePrefixStageHeadersData.back,
    ActivePrefixStageHeadersData.front,ButterflyAxisHeadersData.product,ButterflyAxisHeadersData.cmd,
    CompactNativeRoleChildPrecision.cmd,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,put,Function.update]

theorem restore_saved (st : State) (n : ℕ) :
    execute restore (put st 26 n)=put (execute restore st) 26 n := by
  funext i
  fin_cases i <;> simp [restore,CompactNativeRoleChildPrecision.cmd,execute,eval,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,put,Function.update]

theorem restore_valid_saved (st : State) (n : ℕ) :
    validSchedule restore (put st 26 n)↔validSchedule restore st := by
  simp [restore,CompactNativeRoleChildPrecision.cmd,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,put,Function.update]

theorem prepare_runs (s : Shape) (rows ell p rho left count slots right src dst saved : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk) (hp : 2*s.bits≤p) :
    HoareTime (compile (a:=2) prepare).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (put (raw s rows ell p rho left count slots right src dst) 26 saved))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (put (baseline s rows ell p rho left count slots right src dst) 26 saved))
      (scheduleCost prepare (put (raw s rows ell p rho left count slots right src dst) 26 saved)) := by
  have hv := (prepare_valid_saved _ saved).mpr
    (CompactNativeRoleChildPrecision.prepare_valid s rows ell p rho left count slots right src dst hG hA hK hp)
  have h := schedule_runs (a:=2) prepare _ hv
  rwa [prepare_saved,CompactNativeRoleChildPrecision.prepare_eval s rows ell p rho left count slots right src dst hG hA hK] at h

theorem restore_runs (s : Shape) (rows ell p rho left count slots right src dst saved : ℕ) :
    HoareTime (compile (a:=2) restore).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (put (baseline s rows ell p rho left count slots right src dst) 26 saved))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (put (raw s rows ell p rho left count slots right src dst) 26 saved))
      (scheduleCost restore (put (baseline s rows ell p rho left count slots right src dst) 26 saved)) := by
  have hv : validSchedule restore (put (baseline s rows ell p rho left count slots right src dst) 26 saved) := by
    rw [restore_valid_saved]
    simp [restore,baseline,raw,CompactNativeRoleChildPrecision.cmd,validSchedule,valid,eval,
      CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.valid,
      ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,put,Function.update]
  have he : execute restore (baseline s rows ell p rho left count slots right src dst)=
      raw s rows ell p rho left count slots right src dst := by
    funext i
    fin_cases i <;> simp [restore,baseline,raw,CompactNativeRoleChildPrecision.cmd,execute,eval,
      CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,put,Function.update]
  have h := schedule_runs (a:=2) restore _ hv
  rwa [restore_saved,he] at h

theorem cost_saved (ops : List Op) (hops : ops=prepare ∨ ops=restore) (st : State) (n : ℕ) :
    scheduleCost ops (put st 26 n)=scheduleCost ops st := by
  rcases hops with rfl | rfl
  · simp [prepare,CompactSpectatorLeafSetup.geometry,ActivePrefixStageHeadersData.back,
      ActivePrefixStageHeadersData.front,ButterflyAxisHeadersData.product,ButterflyAxisHeadersData.cmd,
      CompactNativeRoleChildPrecision.cmd,scheduleCost,cost,eval,CompactChildHeadersArithmetic.cost,
      CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,put,Function.update]
  · simp [restore,CompactNativeRoleChildPrecision.cmd,scheduleCost,cost,eval,CompactChildHeadersArithmetic.cost,
      CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,put,Function.update]

private theorem framed {t c : ℕ} (ops : List Op) (old : Tapes t 2) (ht : 43<t)
    (st su : State) (payload : Tapes (1+c) 2) (cost : ℕ)
    (h : HoareTime (compile (a:=2) ops).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank st)
      (fun v => v=ActiveRepairRankHeadersCommands.bank su) cost) :
    HoareTime (CompactNativeRoleChildPrecision.program ops t c)
      (fun v => v=CompactNativeRoleSourcePorts.external old ht st payload)
      (fun v => v=CompactNativeRoleSourcePorts.external old ht su payload) cost := by
  have hh := Placement.hoare_at h (CompactNativeRoleChildHeadersPorts.placement t c)
    (CompactNativeRoleSourcePorts.external old ht st payload) (CompactNativeRoleChildHeadersPorts.active old ht st payload)
  apply hh.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [Placement.replace,CompactNativeRoleChildHeadersPorts.extra old ht st su payload,
    ←CompactNativeRoleChildHeadersPorts.active old ht su payload,Placement.view]

theorem exterior_prepare {t c : ℕ} (old : Tapes t 2) (ht : 43<t) (s : Shape)
    (rows ell p rho left count slots right src dst saved : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk) (hp : 2*s.bits≤p) (payload : Tapes (1+c) 2) :
    HoareTime (CompactNativeRoleChildPrecision.program prepare t c)
      (fun v => v=CompactNativeRoleSourcePorts.external old ht (put (raw s rows ell p rho left count slots right src dst) 26 saved) payload)
      (fun v => v=CompactNativeRoleSourcePorts.external old ht (put (baseline s rows ell p rho left count slots right src dst) 26 saved) payload)
      (scheduleCost prepare (raw s rows ell p rho left count slots right src dst)) := by
  have h := framed prepare old ht _ _ payload _
    (prepare_runs s rows ell p rho left count slots right src dst saved hG hA hK hp)
  rwa [cost_saved prepare (Or.inl rfl)] at h

theorem exterior_restore {t c : ℕ} (old : Tapes t 2) (ht : 43<t) (s : Shape)
    (rows ell p rho left count slots right src dst saved : ℕ) (payload : Tapes (1+c) 2) :
    HoareTime (CompactNativeRoleChildPrecision.program restore t c)
      (fun v => v=CompactNativeRoleSourcePorts.external old ht (put (baseline s rows ell p rho left count slots right src dst) 26 saved) payload)
      (fun v => v=CompactNativeRoleSourcePorts.external old ht (put (raw s rows ell p rho left count slots right src dst) 26 saved) payload)
      (scheduleCost restore (baseline s rows ell p rho left count slots right src dst)) := by
  have h := framed restore old ht _ _ payload _ (restore_runs s rows ell p rho left count slots right src dst saved)
  rwa [cost_saved restore (Or.inr rfl)] at h

end
end IntegerMultBounds.Machine.CompactNativeRoleChildPrecisionSaved
