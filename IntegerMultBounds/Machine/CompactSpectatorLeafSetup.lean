import IntegerMultBounds.Machine.CompactSpectatorLeafHeaders
import IntegerMultBounds.Machine.ActivePrefixStageHeadersData

/-! Leaf-private geometry is synthesized from copied original thirteen native
headers plus immutable polynomial exponent and precision words. H, B, F and
the complete global bit dimension are paid arithmetic outputs, not input oracles. -/
namespace IntegerMultBounds.Machine.CompactSpectatorLeafSetup
noncomputable section
open CompactGadgetReservationShape (Shape)
open ButterflyAxisHeadersArithmetic
open ButterflyAxisHeadersData (cmd product)
open ActiveRepairRankHeadersCommands (State put)

def raw (s : Shape) (rows ell p rho left count slots right source target : ℕ) (i : Fin 28) : Option ℕ :=
  match i.val with
  | 0 => some s.chunk | 1 => some s.axes | 2 => some s.guard | 3 => some s.active
  | 4 => some rows | 5 => some s.payload | 6 => some slots | 7 => some count
  | 8 => some left | 9 => some right | 10 => some rho | 11 => some source | 12 => some target
  | 17 => some ell | 18 => some p | _ => none

def geometry : List Op := [product ![2,1,13] (by decide)]++
  (ActivePrefixStageHeadersData.back++ActivePrefixStageHeadersData.front).map (fun op => .base (.existing op))++
  [product ![0,3,24] (by decide),cmd (.copy 13 16 (by decide)),cmd (.add 16 13 (by decide)),
   cmd (.add 16 13 (by decide)),cmd (.add 16 14 (by decide)),cmd (.add 16 15 (by decide)),
   cmd (.add 16 24 (by decide)),cmd (.erase 24)]

def move (src dst : Fin 28) (hne : src≠dst) : List Op :=
  [cmd (.erase dst),cmd (.copy src dst hne)]

def reorderA : List Op := [cmd (.copy 3 22 (by decide))]++
  move 8 9 (by decide)++move 4 1 (by decide)++move 17 2 (by decide)++move 18 3 (by decide)
def reorderB : List Op := move 0 4 (by decide)++move 10 5 (by decide)++move 7 10 (by decide)++move 22 8 (by decide)
def reorderC : List Op := move 13 6 (by decide)++move 14 7 (by decide)++move 16 0 (by decide)++
  ([11,12,13,14,15,16,17,18,22] : List (Fin 28)).map (fun i => cmd (.erase i))
def schedule := geometry++reorderA++reorderB++reorderC

def state (phase : ℕ) (s : Shape) (rows ell p rho left count slots right source target : ℕ) (i : Fin 28) : Option ℕ :=
  match i.val with
  | 0 => some s.chunk | 1 => some (if phase=0 then s.axes else rows)
  | 2 => some (if phase=0 then s.guard else ell) | 3 => some (if phase=0 then s.active else p)
  | 4 => some (if phase=2 then s.chunk else rows) | 5 => some (if phase=2 then rho else s.payload)
  | 6 => some slots | 7 => some count | 8 => some (if phase=2 then s.active else left)
  | 9 => some (if phase=0 then right else left) | 10 => some (if phase=2 then count else rho)
  | 11 => some source | 12 => some target | 13 => some s.H | 14 => some s.B | 15 => some s.F
  | 16 => some s.bits | 17 => some ell | 18 => some p
  | 22 => if phase=0 then none else some s.active | _ => none

private theorem rounded_back (s : Shape) (hH : 0<s.H) (hK : 0<s.chunk) :
    RoundedRowDescriptor.rounded s.H s.chunk-s.H=s.B := by
  rw [RoundedRowDescriptor.rounded_eq_ceiling _ _ hH hK]
  unfold Shape.B CompactGadgetReservationCapacity.backSlack CompactGadgetReservationCapacity.backChunks
    CompactGadgetReservationCapacity.chunks
  rw [Nat.mul_comm s.chunk]
  rfl
private theorem rounded_front (s : Shape) (hH : 0<s.H) (hK : 0<s.chunk) :
    RoundedRowDescriptor.rounded (2*s.H) s.chunk-2*s.H=s.F := by
  rw [RoundedRowDescriptor.rounded_eq_ceiling _ _ (by omega) hK]
  unfold Shape.F CompactGadgetReservationCapacity.frontSlack CompactGadgetReservationCapacity.frontChunks
    CompactGadgetReservationCapacity.chunks
  rw [Nat.mul_comm s.chunk]
  rfl

theorem geometry_eval (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hH : 0<s.H) (hK : 0<s.chunk) :
    execute geometry (raw s rows ell p rho left count slots right source target)=
      state 0 s rows ell p rho left count slots right source target := by
  have hb := rounded_back s hH hK
  have hf := rounded_front s hH hK
  have hb' : RoundedRowDescriptor.rounded (s.axes*s.guard) s.chunk-s.axes*s.guard=s.B := by
    simpa [Shape.H,CompactGadgetReservationCapacity.capacity,Nat.mul_comm] using hb
  have hf' : RoundedRowDescriptor.rounded (s.axes*s.guard+s.axes*s.guard) s.chunk-
      (s.axes*s.guard+s.axes*s.guard)=s.F := by
    simpa [Shape.H,CompactGadgetReservationCapacity.capacity,two_mul,Nat.mul_comm] using hf
  funext i
  fin_cases i <;> simp [geometry,state,execute,eval,ActivePrefixStageHeadersData.back,
    ActivePrefixStageHeadersData.front,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,put,raw,Function.update,hb',hf']
  all_goals first | rfl | (unfold Shape.bits Shape.H CompactGadgetReservationCapacity.capacity; ring)

theorem reorderA_eval (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    execute reorderA (state 0 s rows ell p rho left count slots right source target)=
      state 1 s rows ell p rho left count slots right source target := by
  funext i
  fin_cases i <;> simp [reorderA,move,state,execute,eval,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,put,Function.update]

theorem reorderB_eval (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    execute reorderB (state 1 s rows ell p rho left count slots right source target)=
      state 2 s rows ell p rho left count slots right source target := by
  funext i
  fin_cases i <;> simp [reorderB,move,state,execute,eval,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,put,Function.update]

theorem reorderC_eval (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    execute reorderC (state 2 s rows ell p rho left count slots right source target)=
      CompactSpectatorLeafHeaders.initial s rows ell p rho left count := by
  funext i
  fin_cases i <;> simp [reorderC,move,state,execute,eval,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,put,
    CompactSpectatorLeafHeaders.initial,Function.update]

private theorem execute_append (xs ys : List Op) (st : State) :
    execute (xs++ys) st=execute ys (execute xs st) := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => exact ih (eval x st)

theorem execute_eq (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hH : 0<s.H) (hK : 0<s.chunk) :
    execute schedule (raw s rows ell p rho left count slots right source target)=
      CompactSpectatorLeafHeaders.initial s rows ell p rho left count := by
  rw [schedule,execute_append,execute_append,execute_append,geometry_eval _ _ _ _ _ _ _ _ _ _ _ hH hK,
    reorderA_eval,reorderB_eval,reorderC_eval]


theorem geometry_valid (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk) :
    validSchedule geometry (raw s rows ell p rho left count slots right source target) := by
  have hH : 0<s.axes*s.guard := Nat.mul_pos hA hG
  have hb := RoundedRowDescriptor.rows_le (s.axes*s.guard) s.chunk hH hK
  have hf := RoundedRowDescriptor.rows_le (s.axes*s.guard+s.axes*s.guard) s.chunk (by omega) hK
  simp [geometry,validSchedule,valid,eval,ActivePrefixStageHeadersData.back,
    ActivePrefixStageHeadersData.front,CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,put,raw,Function.update]
  omega

theorem reorderA_valid (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    validSchedule reorderA (state 0 s rows ell p rho left count slots right source target) := by
  simp [reorderA,move,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,put,state,Function.update]

theorem reorderB_valid (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    validSchedule reorderB (state 1 s rows ell p rho left count slots right source target) := by
  simp [reorderB,move,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,put,state,Function.update]

theorem reorderC_valid (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    validSchedule reorderC (state 2 s rows ell p rho left count slots right source target) := by
  simp [reorderC,move,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,put,state,Function.update]

private theorem valid_append (xs ys : List Op) (st : State) :
    validSchedule (xs++ys) st ↔ validSchedule xs st ∧ validSchedule ys (execute xs st) := by
  induction xs generalizing st with
  | nil => simp [validSchedule,execute]
  | cons x xs ih => simp [validSchedule,execute,ih,and_assoc]

theorem schedule_valid (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk) :
    validSchedule schedule (raw s rows ell p rho left count slots right source target) := by
  have hH : 0<s.H := by exact Nat.mul_pos hA hG
  rw [schedule,valid_append,valid_append,valid_append]
  simp only [execute_append,geometry_eval _ _ _ _ _ _ _ _ _ _ _ hH hK,reorderA_eval,reorderB_eval]
  exact ⟨⟨⟨geometry_valid s _ _ _ _ _ _ _ _ _ _ hG hA hK,reorderA_valid s _ _ _ _ _ _ _ _ _ _⟩,
    reorderB_valid s _ _ _ _ _ _ _ _ _ _⟩,reorderC_valid s _ _ _ _ _ _ _ _ _ _⟩

theorem runs (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk) :
    HoareTime (compile (a:=2) schedule).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (raw s rows ell p rho left count slots right source target))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (CompactSpectatorLeafHeaders.initial s rows ell p rho left count))
      (scheduleCost schedule (raw s rows ell p rho left count slots right source target)) := by
  have hh := schedule_runs (a:=2) schedule (raw s rows ell p rho left count slots right source target)
    (schedule_valid s rows ell p rho left count slots right source target hG hA hK)
  rwa [execute_eq _ _ _ _ _ _ _ _ _ _ _ (Nat.mul_pos hA hG) hK] at hh

end
end IntegerMultBounds.Machine.CompactSpectatorLeafSetup
