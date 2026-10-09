import IntegerMultBounds.Machine.CompactSpectatorVisitGeometry

/-! Runtime sparse leaf selectors retain the entire immutable address geometry.
Each body derives its descending selected bit from the actual ordinal, and
reclaims every generated descriptor after the native butterfly. -/
namespace IntegerMultBounds.Machine.CompactSpectatorLeafHeaders
noncomputable section
open CompactGadgetReservationShape (Shape)
open ButterflyAxisHeadersArithmetic
open ButterflyAxisHeadersData (cmd product)
open ActiveRepairRankHeadersCommands (State put)

def initial (s : Shape) (rows ell p rho ordinal count : ℕ) (i : Fin 28) : Option ℕ :=
  match i.val with
  | 0 => some s.bits | 1 => some rows | 2 => some ell | 3 => some p | 4 => some s.chunk
  | 5 => some rho | 6 => some s.H | 7 => some s.B | 8 => some s.active
  | 9 => some ordinal | 10 => some count | _ => none

def selected (s : Shape) (rho ordinal : ℕ) := CompactSpectatorVisitGeometry.selected s rho ordinal 0

def prepared (s : Shape) (rows ell p rho ordinal count shift : ℕ) (i : Fin 28) : Option ℕ :=
  match i.val with
  | 0 => some s.bits | 1 => some rows | 2 => some ell | 3 => some p | 4 => some s.chunk
  | 5 => some rho | 6 => some s.H | 7 => some s.B | 8 => some s.active
  | 9 => some ordinal | 10 => some count | 11 => some 1
  | 12 => some (selected s rho ordinal+shift) | 13 => some (s.active-1)
  | 14 => some (s.active-1-ordinal) | 15 => some ((s.active-1-ordinal)*s.chunk)
  | 16 => some (2^ell) | _ => none

def setup : List Op := [.base (.constant 11 1),cmd (.difference 8 11 13 (by decide)),
  cmd (.difference 13 9 14 (by decide)),product ![4,14,15] (by decide),cmd (.copy 15 12 (by decide)),
  cmd (.add 12 6 (by decide)),cmd (.add 12 7 (by decide)),cmd (.add 12 5 (by decide)),.power ![2,16] (by decide)]
def cleanup : List Op := [cmd (.add 9 11 (by decide)),cmd (.erase 11),cmd (.erase 12),
  cmd (.erase 13),cmd (.erase 14),cmd (.erase 15),cmd (.erase 16)]

theorem setup_eval (s : Shape) (rows ell p rho ordinal count : ℕ) :
    execute setup (initial s rows ell p rho ordinal count)=prepared s rows ell p rho ordinal count 0 := by
  funext i
  fin_cases i <;> simp [setup,execute,eval,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,put,initial,prepared,selected,CompactSpectatorVisitGeometry.selected,Function.update]
  all_goals omega

theorem setup_valid (s : Shape) (rows ell p rho ordinal count : ℕ) (ho : ordinal<s.active) (hK : 0<s.chunk) :
    validSchedule setup (initial s rows ell p rho ordinal count) := by
  simp [setup,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,put,initial,Function.update]
  omega

theorem cleanup_eval (s : Shape) (rows ell p rho ordinal count : ℕ) :
    execute cleanup (prepared s rows ell p rho ordinal count 1)=initial s rows ell p rho (ordinal+1) count := by
  funext i
  fin_cases i <;> simp [cleanup,execute,eval,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,put,initial,prepared,Function.update]

theorem cleanup_valid (s : Shape) (rows ell p rho ordinal count : ℕ) :
    validSchedule cleanup (prepared s rows ell p rho ordinal count 1) := by
  simp [cleanup,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,put,prepared,Function.update]

theorem setup_runs (s : Shape) (rows ell p rho ordinal count : ℕ) (ho : ordinal<s.active) (hK : 0<s.chunk) :
    HoareTime (compile (a:=2) setup).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (initial s rows ell p rho ordinal count))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (prepared s rows ell p rho ordinal count 0))
      (scheduleCost setup (initial s rows ell p rho ordinal count)) := by
  have hh := schedule_runs (a:=2) setup _ (setup_valid s rows ell p rho ordinal count ho hK)
  rwa [setup_eval] at hh

theorem cleanup_runs (s : Shape) (rows ell p rho ordinal count : ℕ) :
    HoareTime (compile (a:=2) cleanup).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (prepared s rows ell p rho ordinal count 1))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (initial s rows ell p rho (ordinal+1) count))
      (scheduleCost cleanup (prepared s rows ell p rho ordinal count 1)) := by
  have hh := schedule_runs (a:=2) cleanup _ (cleanup_valid s rows ell p rho ordinal count)
  rwa [cleanup_eval] at hh

end
end IntegerMultBounds.Machine.CompactSpectatorLeafHeaders
