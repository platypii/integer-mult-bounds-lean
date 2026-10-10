import IntegerMultBounds.Machine.CompactNativeRoleSourceRuns

/-! Final paid removal of the physically copied original13 plus ell/p bank.
These are copies; the global original scalar bank and native result are framed. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleMetadataCleanup
noncomputable section
open CompactChildHeadersArithmetic
open ActiveRepairRankHeadersCommands (State)

abbrev cmd (op : ActiveRepairRankHeadersCommands.Command) : Op := .existing (.command op)
def schedule : List Op := ([0,1,2,3,4,5,6,7,8,9,10,11,12,17,18] : List (Fin 28)).map (fun i => cmd (.erase i))

theorem execute_eq (vs : Fin 15 → ℕ) : execute schedule (CompactNativeRoleStageCopy.metadata vs)=fun _ => none := by
  funext i
  fin_cases i <;> simp [schedule,cmd,execute,eval,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,
    CompactNativeRoleStageCopy.metadata,Function.update]

theorem runs (vs : Fin 15 → ℕ) :
    HoareTime (compile (a:=2) schedule).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (CompactNativeRoleStageCopy.metadata vs))
      (fun v => v=SharedBank.empty 43 2)
      (scheduleCost schedule (CompactNativeRoleStageCopy.metadata vs)) := by
  have hv : validSchedule schedule (CompactNativeRoleStageCopy.metadata vs) := by
    simp [schedule,cmd,validSchedule,valid,eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,
      CompactNativeRoleStageCopy.metadata,Function.update]
  have hh := schedule_runs (a:=2) schedule _ hv
  rw [execute_eq] at hh
  have he : ActiveRepairRankHeadersCommands.bank (a:=2) (fun _ => none)=SharedBank.empty 43 2 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases (m:=28) (n:=15) <;>
      simp [ActiveRepairRankHeadersCommands.caller,SharedBank.empty]
  rwa [he] at hh

def values (s : CompactGadgetReservationShape.Shape) (rows ell p rho left count slots right src dst : ℕ) : Fin 15 → ℕ :=
  ![s.chunk,s.axes,s.guard,s.active,rows,s.payload,slots,count,left,right,rho,src,dst,ell,p]

theorem metadata_raw (s : CompactGadgetReservationShape.Shape) (rows ell p rho left count slots right src dst : ℕ) :
    CompactNativeRoleStageCopy.metadata (values s rows ell p rho left count slots right src dst)=
      CompactSpectatorLeafSetup.raw s rows ell p rho left count slots right src dst := by
  funext i
  fin_cases i <;> rfl

theorem raw_runs (s : CompactGadgetReservationShape.Shape) (rows ell p rho left count slots right src dst : ℕ) :
    HoareTime (compile (a:=2) schedule).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (CompactSpectatorLeafSetup.raw s rows ell p rho left count slots right src dst))
      (fun v => v=SharedBank.empty 43 2)
      (scheduleCost schedule (CompactSpectatorLeafSetup.raw s rows ell p rho left count slots right src dst)) := by
  simpa only [metadata_raw] using runs (values s rows ell p rho left count slots right src dst)

end
end IntegerMultBounds.Machine.CompactNativeRoleMetadataCleanup
