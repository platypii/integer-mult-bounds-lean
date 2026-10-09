import IntegerMultBounds.Machine.ButterflyAxisHeadersData
import IntegerMultBounds.Machine.NativeZeroPadding

/-! Actual arithmetic for the number of added native coefficient records.
The row deficit multiplies immutable address volume and polynomial count;
coefficient width is retained independently of either multiplicity. -/
namespace IntegerMultBounds.Machine.NativeZeroPaddingHeaders
noncomputable section
open ButterflyAxisHeadersArithmetic
open ButterflyAxisHeadersData (cmd product)
open ActiveRepairRankHeadersCommands (State put)

def count (rows padded bits ell : ℕ) := (padded-rows)*(2^bits*2^ell)
def initial (rows padded bits ell width : ℕ) (i : Fin 28) : Option ℕ :=
  match i.val with
  | 0 => some rows | 1 => some padded | 2 => some bits | 3 => some ell | 4 => some width | _ => none
def output (rows padded bits ell width : ℕ) (i : Fin 28) : Option ℕ :=
  match i.val with
  | 0 => some rows | 1 => some padded | 2 => some bits | 3 => some ell | 4 => some width
  | 9 => some (count rows padded bits ell) | _ => none

def schedule : List Op :=
  [cmd (.difference 1 0 5 (by decide)),.power ![2,6] (by decide),.power ![3,7] (by decide),
    product ![6,7,8] (by decide),product ![8,5,9] (by decide),
    cmd (.erase 5),cmd (.erase 6),cmd (.erase 7),cmd (.erase 8)]
def cleanup : List Op := [cmd (.erase 9)]

theorem execute_eq (rows padded bits ell width : ℕ) : execute schedule (initial rows padded bits ell width)=
    output rows padded bits ell width := by
  funext i
  fin_cases i
  all_goals simp [schedule,execute,eval,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,put,initial,output,count,Function.update]
  all_goals simp [Nat.mul_comm]

theorem valid (rows padded bits ell width : ℕ) (hpad : rows≤padded) : validSchedule schedule (initial rows padded bits ell width) := by
  simp [schedule,validSchedule,ButterflyAxisHeadersArithmetic.valid,eval,CompactChildHeadersArithmetic.valid,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,put,initial,Function.update,hpad]

theorem runs (rows padded bits ell width : ℕ) (hpad : rows≤padded) :
    HoareTime (compile (a:=2) schedule).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (initial rows padded bits ell width))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (output rows padded bits ell width))
      (scheduleCost schedule (initial rows padded bits ell width)) := by
  have hh := schedule_runs (a:=2) schedule _ (valid rows padded bits ell width hpad)
  rwa [execute_eq] at hh

theorem cleanup_eval (rows padded bits ell width : ℕ) : execute cleanup (output rows padded bits ell width)=initial rows padded bits ell width := by
  funext i
  fin_cases i
  all_goals simp [cleanup,execute,eval,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,initial,output,Function.update]

theorem cleanup_runs (rows padded bits ell width : ℕ) :
    HoareTime (compile (a:=2) cleanup).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (output rows padded bits ell width))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (initial rows padded bits ell width))
      (scheduleCost cleanup (output rows padded bits ell width)) := by
  have hh := schedule_runs (a:=2) cleanup (output rows padded bits ell width) (by
    simp [cleanup,validSchedule,ButterflyAxisHeadersArithmetic.valid,CompactChildHeadersArithmetic.valid,
      ActivePrefixStageHeadersOps.valid,ActiveRepairRankHeadersCommands.valid,output])
  rwa [cleanup_eval] at hh

theorem added_volume (rows padded bits ell : ℕ) (hpad : rows≤padded) :
    rows*2^bits*2^ell+count rows padded bits ell=padded*2^bits*2^ell := by
  unfold count
  calc
    _ = (rows+(padded-rows))*2^bits*2^ell := by ring
    _ = _ := by rw [Nat.add_sub_of_le hpad]

theorem added_symbols (rows padded bits ell width : ℕ) (hpad : rows≤padded) :
    rows*2^bits*2^ell*(2*(width+1))+(NativeZeroStream.records width (count rows padded bits ell)).length=
      padded*2^bits*2^ell*(2*(width+1)) := by
  rw [NativeZeroStream.length]
  have hh := congrArg (fun n => n*(2*(width+1))) (added_volume rows padded bits ell hpad)
  simpa only [Nat.add_mul] using hh

end
end IntegerMultBounds.Machine.NativeZeroPaddingHeaders
