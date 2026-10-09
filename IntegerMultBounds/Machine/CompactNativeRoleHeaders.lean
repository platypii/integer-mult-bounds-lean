import IntegerMultBounds.Machine.CompactSpectatorLeafSetup

/-! Physical complete-native-row lengths and role group counts are synthesized
from the original thirteen words and ell/p. The full Shape.bits dimension is
retained while only the outer row count is divided by the fixed role count. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleHeaders
noncomputable section
open CompactGadgetReservationShape (Shape)
open ButterflyAxisHeadersArithmetic
open ButterflyAxisHeadersData (cmd product)
open ActiveRepairRankHeadersCommands (State)
open CompactSpectatorLeafSetup (raw state geometry)

theorem execute_append (xs ys : List Op) (st : State) : execute (xs++ys) st=execute ys (execute xs st) := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => exact ih (eval x st)

theorem validSchedule_append (xs ys : List Op) (st : State) :
    validSchedule (xs++ys) st ↔ validSchedule xs st ∧ validSchedule ys (execute xs st) := by
  induction xs generalizing st with
  | nil => simp [validSchedule,execute]
  | cons x xs ih => simp only [List.cons_append,validSchedule,execute,ih,and_assoc]

def recordWidth (s : Shape) (p : ℕ) := ButterflyGuard.width p s.bits

def rest (c : ℕ) (merge : Bool) : List Op :=
  [.base (.constant 19 c),.base (.quotient ![4,19,26] (by decide)),
   .base (.constant 20 4),cmd (.copy 16 23 (by decide)),cmd (.add 23 16 (by decide)),
   cmd (.add 23 18 (by decide)),cmd (.add 23 20 (by decide)),.base (.constant 21 1),
   cmd (.add 23 21 (by decide)),cmd (.erase 20),.base (.constant 20 2),product ![20,23,24] (by decide),
   cmd (.erase 20),.power ![16,20] (by decide),cmd (.erase 21),.power ![17,21] (by decide),
   product ![20,21,22] (by decide),product ![22,24,25] (by decide),
   product (if merge then ![26,25,27] else ![4,25,27]) (by cases merge <;> decide)]
def schedule (c : ℕ) (merge : Bool) := geometry++rest c merge

def prepared (c : ℕ) (merge : Bool) (s : Shape) (rows ell p rho left count slots right source target : ℕ) : State := fun i =>
  match i.val with
  | 19 => some c | 20 => some (2^s.bits) | 21 => some (2^ell) | 22 => some (2^s.bits*2^ell)
  | 23 => some (recordWidth s p+1) | 24 => some (2*(recordWidth s p+1))
  | 25 => some (2^s.bits*2^ell*(2*(recordWidth s p+1))) | 26 => some (rows/c)
  | 27 => some ((if merge then rows/c else rows)*(2^s.bits*2^ell*(2*(recordWidth s p+1))))
  | _ => state 0 s rows ell p rho left count slots right source target i

def cleanup : List Op := ([13,14,15,16,19,20,21,22,23,24,25,26,27] : List (Fin 28)).map (fun i => cmd (.erase i))

theorem rest_eval (c : ℕ) (merge : Bool) (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    execute (rest c merge) (state 0 s rows ell p rho left count slots right source target)=
      prepared c merge s rows ell p rho left count slots right source target := by
  cases merge <;> funext i <;> fin_cases i
  all_goals simp [rest,execute,eval,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,state,prepared,Function.update,
    recordWidth,ButterflyGuard.width,ButterflyGuard.halfWidth]
  all_goals ring

theorem rest_valid (c : ℕ) (merge : Bool) (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c) :
    validSchedule (rest c merge) (state 0 s rows ell p rho left count slots right source target) := by
  have hcr : c≤rows := (Nat.div_pos_iff.mp hgroup).2
  have hP : 0<(2:ℕ)^s.bits := pow_pos (by decide) _
  have hR : 0<(2:ℕ)^ell := pow_pos (by decide) _
  have hPR : 0<(2:ℕ)^s.bits*2^ell := Nat.mul_pos hP hR
  cases merge <;> simp [rest,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,state,Function.update]
  all_goals omega

theorem execute_eq (c : ℕ) (merge : Bool) (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk) :
    execute (schedule c merge) (raw s rows ell p rho left count slots right source target)=
      prepared c merge s rows ell p rho left count slots right source target := by
  rw [schedule,execute_append,CompactSpectatorLeafSetup.geometry_eval s rows ell p rho left count slots right source target
    (by unfold Shape.H CompactGadgetReservationCapacity.capacity; positivity) hK,rest_eval]

theorem cleanup_eval (c : ℕ) (merge : Bool) (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    execute cleanup (prepared c merge s rows ell p rho left count slots right source target)=
      raw s rows ell p rho left count slots right source target := by
  funext i
  fin_cases i <;> simp [cleanup,cmd,execute,eval,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,prepared,state,raw,Function.update]

theorem runs (c : ℕ) (merge : Bool) (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c) (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk) :
    HoareTime (compile (a:=2) (schedule c merge)).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (raw s rows ell p rho left count slots right source target))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (prepared c merge s rows ell p rho left count slots right source target))
      (scheduleCost (schedule c merge) (raw s rows ell p rho left count slots right source target)) := by
  have hv : validSchedule (schedule c merge) (raw s rows ell p rho left count slots right source target) := by
    rw [schedule,validSchedule_append]
    refine ⟨CompactSpectatorLeafSetup.geometry_valid s rows ell p rho left count slots right source target hG hA hK,?_⟩
    rw [CompactSpectatorLeafSetup.geometry_eval s rows ell p rho left count slots right source target
      (by unfold Shape.H CompactGadgetReservationCapacity.capacity; positivity) hK]
    exact rest_valid c merge s rows ell p rho left count slots right source target hc hr hgroup
  have hh := schedule_runs (a:=2) (schedule c merge) _ hv
  rwa [execute_eq c merge s rows ell p rho left count slots right source target hG hA hK] at hh

theorem cleanup_runs (c : ℕ) (merge : Bool) (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    HoareTime (compile (a:=2) cleanup).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (prepared c merge s rows ell p rho left count slots right source target))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (raw s rows ell p rho left count slots right source target))
      (scheduleCost cleanup (prepared c merge s rows ell p rho left count slots right source target)) := by
  have hv : validSchedule cleanup (prepared c merge s rows ell p rho left count slots right source target) := by
    simp [cleanup,cmd,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,
      ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
      ActiveRepairRankHeadersCommands.eval,prepared,state,Function.update]
  have hh := schedule_runs (a:=2) cleanup _ hv
  rwa [cleanup_eval] at hh

end
end IntegerMultBounds.Machine.CompactNativeRoleHeaders
