import IntegerMultBounds.Machine.ActiveRepairRankHeadersCommands
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersPowerRound

/-! Physical layout-header preparation starts with fourteen original widths
and stage controls. Reservation widths H/B/F themselves are supplied here;
deriving those from reservation chunk/axis/guard controls remains separate. -/
namespace IntegerMultBounds.Machine.ActivePrefixLayoutHeadersData
noncomputable section
open ActiveRepairRankHeadersCommands

structure Inputs where
  H : ℕ
  B : ℕ
  F : ℕ
  before : ℕ
  after : ℕ
  m : ℕ
  w : ℕ
  q : ℕ
  b : ℕ
  n : ℕ
  rho : ℕ
  sourceOffset : ℕ
  rows : ℕ
  payload : ℕ

inductive Mode | target | compactBefore | compactAfter deriving DecidableEq

def originalValues (d : Inputs) : Fin 14 → ℕ :=
  ![d.H,d.B,d.F,d.before,d.after,d.m,d.w,d.q,d.b,d.n,d.rho,d.sourceOffset,d.rows,d.payload]
def prefixWidth (mode : Mode) (d : Inputs) :=
  2*d.H+d.F+d.before+(match mode with | .target => 0 | _ => d.m+d.after)
def targetStart (mode : Mode) (d : Inputs) :=
  match mode with | .target => d.H-d.w+d.F+d.before | _ => d.after
def sourceStart (mode : Mode) (d : Inputs) :=
  match mode with | .compactBefore => d.sourceOffset+d.m+d.after | _ => d.sourceOffset
def exponent (mode : Mode) (d : Inputs) :=
  match mode with | .target => d.H+d.B+d.after | _ => d.H-d.w+d.B
def suffix (mode : Mode) (d : Inputs) := d.payload*2^exponent mode d

def values (mode : Mode) (d : Inputs) : Fin 10 → ℕ :=
  ![prefixWidth mode d,targetStart mode d,sourceStart mode d,d.q,d.b,d.n,d.rho,d.n+1,d.rows,suffix mode d]
def initial (d : Inputs) : State := fun i =>
  if h : i.val<14 then some (originalValues d ⟨i.val,h⟩) else none
def seeded (d : Inputs) := put (initial d) 24 1

def arithmetic (mode : Mode) (d : Inputs) : State := fun i =>
  if h : i.val<14 then some (originalValues d ⟨i.val,h⟩)
  else if h : i.val<23 then some (values mode d ⟨i.val-14,by omega⟩)
  else if i.val=24 then some (exponent mode d) else none
def powered (mode : Mode) (d : Inputs) := put (arithmetic mode d) 25 (2^exponent mode d)
def multiplied (mode : Mode) (d : Inputs) := put (powered mode d) 23 (suffix mode d)
def finished (mode : Mode) (d : Inputs) : State := fun i =>
  if h : i.val<14 then some (originalValues d ⟨i.val,h⟩)
  else if h : i.val<24 then some (values mode d ⟨i.val-14,by omega⟩) else none

def widthCommands : Mode → List Command
  | .target => []
  | _ => [.add 14 5 (by decide),.add 14 4 (by decide)]
def targetCommands : Mode → List Command
  | .target => [.difference 0 6 15 (by decide),.add 15 2 (by decide),.add 15 3 (by decide)]
  | _ => [.copy 4 15 (by decide)]
def sourceCommands : Mode → List Command
  | .compactBefore => [.add 16 5 (by decide),.add 16 4 (by decide)]
  | _ => []
def exponentCommands : Mode → List Command
  | .target => [.copy 0 24 (by decide),.add 24 1 (by decide),.add 24 4 (by decide)]
  | _ => [.difference 0 6 24 (by decide),.add 24 1 (by decide)]
def schedule (mode : Mode) : List Command :=
  [.copy 0 14 (by decide),.add 14 0 (by decide),.add 14 2 (by decide),.add 14 3 (by decide)]++
  widthCommands mode++targetCommands mode++[.copy 11 16 (by decide)]++sourceCommands mode++
  [.copy 7 17 (by decide),.copy 8 18 (by decide),.copy 9 19 (by decide),.copy 10 20 (by decide),
   .copy 9 21 (by decide),.add 21 24 (by decide),.erase 24,.copy 12 22 (by decide)]++exponentCommands mode

def scratchCleanup : List Command := [.erase 24,.erase 25]
def outputCleanup : List Command := [.erase 14,.erase 15,.erase 16,.erase 17,.erase 18,
  .erase 19,.erase 20,.erase 21,.erase 22,.erase 23]

theorem schedule_valid (mode : Mode) (d : Inputs) (hw : d.w≤d.H) :
    validSchedule (schedule mode) (seeded d) := by
  cases mode <;> simp [schedule,widthCommands,targetCommands,sourceCommands,exponentCommands,
    validSchedule,valid,eval,put,seeded,initial,originalValues,Function.update,hw]

theorem execute_eq (mode : Mode) (d : Inputs) : execute (schedule mode) (seeded d)=arithmetic mode d := by
  cases mode <;> funext i <;> fin_cases i
  all_goals simp [schedule,widthCommands,targetCommands,sourceCommands,exponentCommands,
    execute,eval,put,seeded,initial,originalValues,Function.update,arithmetic,values,prefixWidth,targetStart,sourceStart,exponent]
  all_goals omega

theorem scratch_valid (mode : Mode) (d : Inputs) : validSchedule scratchCleanup (multiplied mode d) := by
  simp [scratchCleanup,validSchedule,valid,eval,put,multiplied,powered,arithmetic,Function.update]
theorem scratch_eq (mode : Mode) (d : Inputs) : execute scratchCleanup (multiplied mode d)=finished mode d := by
  funext i; fin_cases i
  all_goals simp [scratchCleanup,execute,eval,put,multiplied,powered,arithmetic,finished,values,Function.update]

theorem cleanup_valid (mode : Mode) (d : Inputs) : validSchedule outputCleanup (finished mode d) := by
  simp [outputCleanup,validSchedule,valid,eval,finished,Function.update]
theorem cleanup_eq (mode : Mode) (d : Inputs) : execute outputCleanup (finished mode d)=initial d := by
  funext i; fin_cases i
  all_goals simp [outputCleanup,execute,eval,finished,initial,Function.update]

end
end IntegerMultBounds.Machine.ActivePrefixLayoutHeadersData
