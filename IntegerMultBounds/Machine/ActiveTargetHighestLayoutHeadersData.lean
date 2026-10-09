import IntegerMultBounds.Machine.ActivePrefixLayoutHeadersData
import IntegerMultBounds.Machine.ActiveTargetHighestPairLayoutGeometry

/-! The highest-bit geometry is computed from the same fourteen original
layout descriptors as the low selected-bit sequences. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestLayoutHeadersData
noncomputable section
open ActiveRepairRankHeadersCommands
open ActivePrefixLayoutHeadersData (Inputs originalValues initial seeded)

inductive Mode | early | late deriving DecidableEq

def baseWidth (d : Inputs) := 2*d.H+d.F+d.before
def sourceHigh (d : Inputs) := d.sourceOffset+d.rho+d.m
def left (mode : Mode) (d : Inputs) := baseWidth d-(match mode with | .early => sourceHigh d+1 | .late => 1)
def gap (mode : Mode) (d : Inputs) := match mode with
  | .early => sourceHigh d-1
  | .late => d.after-(d.sourceOffset+d.rho+1)
def suffix (mode : Mode) (d : Inputs) :=
  (match mode with | .early => d.m+d.after | .late => sourceHigh d)+d.H+d.B

def Valid (mode : Mode) (d : Inputs) : Prop := match mode with
  | .early => sourceHigh d+1≤baseWidth d ∧ 1≤sourceHigh d
  | .late => 1≤baseWidth d ∧ d.sourceOffset+d.rho+1≤d.after

def values (mode : Mode) (d : Inputs) : Fin 5 → ℕ := ![left mode d,gap mode d,suffix mode d,d.rows,d.payload]
def finished (mode : Mode) (d : Inputs) : State := fun i =>
  if h : i.val<14 then some (originalValues d ⟨i.val,h⟩)
  else if h : i.val<19 then some (values mode d ⟨i.val-14,by omega⟩) else none

def middle : Mode → List Command
  | .early => [.add 20 5 (by decide),.copy 20 21 (by decide),.add 21 24 (by decide),
      .difference 19 21 14 (by decide),.difference 20 24 15 (by decide),
      .copy 5 16 (by decide),.add 16 4 (by decide)]
  | .late => [.difference 19 24 14 (by decide),.copy 20 21 (by decide),.add 21 24 (by decide),
      .difference 4 21 15 (by decide),.copy 20 16 (by decide),.add 16 5 (by decide)]
def schedule (mode : Mode) : List Command :=
  [.copy 0 19 (by decide),.add 19 0 (by decide),.add 19 2 (by decide),.add 19 3 (by decide),
   .copy 11 20 (by decide),.add 20 10 (by decide)]++middle mode++
  [.add 16 0 (by decide),.add 16 1 (by decide),.copy 12 17 (by decide),.copy 13 18 (by decide),
   .erase 19,.erase 20,.erase 21,.erase 24]
def cleanup : List Command := [.erase 14,.erase 15,.erase 16,.erase 17,.erase 18]

theorem schedule_valid (mode : Mode) (d : Inputs) (hv : Valid mode d) :
    validSchedule (schedule mode) (seeded d) := by
  cases mode <;> simp [Valid,baseWidth,sourceHigh] at hv
  all_goals simp [schedule,middle,validSchedule,valid,eval,put,seeded,initial,originalValues,Function.update]
  all_goals omega

theorem schedule_eq (mode : Mode) (d : Inputs) :
    execute (schedule mode) (seeded d)=finished mode d := by
  cases mode <;> funext i <;> fin_cases i
  all_goals simp [schedule,middle,execute,eval,put,seeded,initial,originalValues,Function.update,
    finished,values,left,gap,suffix,baseWidth,sourceHigh]
  all_goals omega

theorem cleanup_valid (mode : Mode) (d : Inputs) : validSchedule cleanup (finished mode d) := by
  simp [cleanup,validSchedule,valid,eval,finished,Function.update]
theorem cleanup_eq (mode : Mode) (d : Inputs) : execute cleanup (finished mode d)=initial d := by
  funext i; fin_cases i
  all_goals simp [cleanup,execute,eval,finished,initial,Function.update]

end
end IntegerMultBounds.Machine.ActiveTargetHighestLayoutHeadersData
