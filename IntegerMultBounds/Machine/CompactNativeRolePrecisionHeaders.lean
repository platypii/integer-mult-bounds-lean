import IntegerMultBounds.Machine.CompactNativeRoleReservedBridge
import IntegerMultBounds.Machine.CompactReservationPaddingHeaderBudget

/-! The corrected role precision is physically computed from original scalar
q,D,K and the paid original row-axis reservation. Its value is not preloaded
or inferred from a width equality; all generated fields are erased afterwards. -/
namespace IntegerMultBounds.Machine.CompactNativeRolePrecisionHeaders
noncomputable section
open CompactGlobalRowHeaderOps
open ActiveRepairRankHeadersCommands (State put)
open CompactReservedHeaders (initial)
open CompactReservationPaddingHeaders (cmd)
open CompactNativeRoleReservedBridge (precision)

private theorem validSchedule_append (xs ys : List Op) (st : State) :
    validSchedule (xs++ys) st ↔ validSchedule xs st ∧ validSchedule ys (execute xs st) := by
  induction xs generalizing st with
  | nil => simp [validSchedule,execute]
  | cons x xs ih => simp only [List.cons_append,validSchedule,execute,ih,and_assoc]

def extra : List Op := [cmd (.copy 4 19 (by decide)),cmd (.add 19 16 (by decide)),
  cmd (.add 19 16 (by decide)),cmd (.add 19 11 (by decide)),cmd (.add 19 11 (by decide))]
def schedule (c m : ℕ) := CompactReservationPaddingHeaders.schedule c m++extra

def prepared (c m D K rho ell q d G : ℕ) : State :=
  put (CompactReservationPaddingHeaders.prepared c m D K rho ell q d G) 19 (precision c m d D K q)
def cleanup := CompactReservationPaddingHeaders.cleanup++[cmd (.erase 19)]

theorem extra_eval (c m D K rho ell q d G : ℕ) :
    execute extra (CompactReservationPaddingHeaders.prepared c m D K rho ell q d G)=prepared c m D K rho ell q d G := by
  funext i
  fin_cases i <;> simp [extra,execute,eval,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,
    CompactReservationPaddingHeaders.prepared,prepared,put,Function.update,precision,initial]
  all_goals ring

theorem extra_valid (c m D K rho ell q d G : ℕ) :
    validSchedule extra (CompactReservationPaddingHeaders.prepared c m D K rho ell q d G) := by
  simp [extra,validSchedule,valid,eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,put,Function.update,
    CompactReservationPaddingHeaders.prepared,CompactReservedHeaders.initial]

theorem runs (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hK : 0<K) (hrow : CompactGlobalRowPadding.rowAxes c m d≤D) (hDp : 0<D) :
    HoareTime (compile (a:=2) (schedule c m)).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (initial D K rho ell q d G))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (prepared c m D K rho ell q d G))
      (scheduleCost (schedule c m) (initial D K rho ell q d G)) := by
  have hv : validSchedule (schedule c m) (initial D K rho ell q d G) := by
    rw [schedule,validSchedule_append,CompactReservationPaddingHeaders.execute_eq c m D K rho ell q d G hc]
    exact ⟨CompactReservationPaddingHeaders.valid c m D K rho ell q d G hc hm hd hK hrow hDp,extra_valid _ _ _ _ _ _ _ _ _⟩
  have hh := schedule_runs (a:=2) (schedule c m) _ hv
  rw [schedule,execute_append,CompactReservationPaddingHeaders.execute_eq c m D K rho ell q d G hc,extra_eval] at hh
  exact hh

theorem cleanup_eval (c m D K rho ell q d G : ℕ) : execute cleanup (prepared c m D K rho ell q d G)=initial D K rho ell q d G := by
  funext i
  fin_cases i <;> simp [cleanup,CompactReservationPaddingHeaders.cleanup,cmd,execute,eval,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,prepared,put,
    CompactReservationPaddingHeaders.prepared,CompactReservedHeaders.initial,Function.update]

theorem cleanup_runs (c m D K rho ell q d G : ℕ) :
    HoareTime (compile (a:=2) cleanup).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (prepared c m D K rho ell q d G))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (initial D K rho ell q d G))
      (scheduleCost cleanup (prepared c m D K rho ell q d G)) := by
  have hv : validSchedule cleanup (prepared c m D K rho ell q d G) := by
    simp [cleanup,CompactReservationPaddingHeaders.cleanup,cmd,validSchedule,valid,eval,ActivePrefixStageHeadersOps.valid,
      ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,
      prepared,put,CompactReservationPaddingHeaders.prepared,Function.update]
  have hh := schedule_runs (a:=2) cleanup _ hv
  rwa [cleanup_eval] at hh

theorem precision_cells (c m D K rho ell q d G : ℕ) :
    (ActiveRepairRankHeadersCommands.bank (a:=2) (prepared c m D K rho ell q d G)).head (19 : Fin 43)=1 ∧
      (ActiveRepairRankHeadersCommands.bank (a:=2) (prepared c m D K rho ell q d G)).tape (19 : Fin 43)=
        RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (precision c m d D K q)) := by
  constructor <;> rfl

end
end IntegerMultBounds.Machine.CompactNativeRolePrecisionHeaders
