import IntegerMultBounds.Machine.ActiveRepairRankHeadersCommands

/-! Fixed arithmetic schedules for rank parser and destination patch headers.
Only original widths are supplied; starts are actual runtime arithmetic outputs. -/
namespace IntegerMultBounds.Machine.ActiveRepairRankHeadersData
noncomputable section
open ActiveRepairRankHeadersCommands

structure Widths where
  H : ℕ
  B : ℕ
  F : ℕ
  before : ℕ
  after : ℕ
  m : ℕ
  w : ℕ
  sourceOffset : ℕ
  sourceWidth : ℕ
  addressBits : ℕ
inductive SourceSide where | before | after

def originalValues (d : Widths) : Fin 10 → ℕ :=
  ![d.H,d.B,d.F,d.before,d.after,d.m,d.w,d.sourceOffset,d.sourceWidth,d.addressBits]
def targetStart (d : Widths) := d.after+d.H+d.B
def prefixStart (d : Widths) := d.m+targetStart d
def tStart (d : Widths) := prefixStart d+(d.H-d.w)+d.F+d.before
def uStart (d : Widths) := tStart d+d.H
def sourceStart (side : SourceSide) (d : Widths) :=
  (match side with | .before => prefixStart d | .after => d.H+d.B)+d.sourceOffset

def parserValues (side : SourceSide) (d : Widths) : Fin 8 → ℕ :=
  ![targetStart d,d.m,tStart d,d.w,uStart d,d.w,sourceStart side d,d.sourceWidth]
def patchValues (d : Widths) : Fin 7 → ℕ :=
  ![0,d.addressBits,targetStart d,d.m,tStart d,d.w,uStart d]

def initial (d : Widths) : State := fun i =>
  if h : i.val<10 then some (originalValues d ⟨i.val,h⟩) else none

def finished (side : SourceSide) (d : Widths) : State :=
  ![some d.H,some d.B,some d.F,some d.before,some d.after,some d.m,some d.w,
    some d.sourceOffset,some d.sourceWidth,some d.addressBits,
    some (targetStart d),some d.m,some (tStart d),some d.w,some (uStart d),some d.w,
    some (sourceStart side d),some d.sourceWidth,
    some 0,some d.addressBits,some (targetStart d),some d.m,some (tStart d),some d.w,some (uStart d),
    none,none,none]

def sourceBase : SourceSide → Fin 28 | .before => 27 | .after => 26

def schedule (side : SourceSide) : List Command :=
  [.difference 0 6 25 (by decide),
   .copy 0 26 (by decide),.add 26 1 (by decide),
   .copy 26 20 (by decide),.add 20 4 (by decide),
   .copy 20 27 (by decide),.add 27 5 (by decide),
   .copy 27 22 (by decide),.add 22 25 (by decide),.add 22 2 (by decide),.add 22 3 (by decide),
   .copy 22 24 (by decide),.add 24 0 (by decide),
   .copy (sourceBase side) 16 (by cases side <;> decide),.add 16 7 (by decide),
   .zero 18,.copy 9 19 (by decide),.copy 5 21 (by decide),.copy 6 23 (by decide),
   .copy 20 10 (by decide),.copy 5 11 (by decide),.copy 22 12 (by decide),.copy 6 13 (by decide),
   .copy 24 14 (by decide),.copy 6 15 (by decide),.copy 8 17 (by decide),
   .erase 25,.erase 26,.erase 27]

 theorem schedule_valid (side : SourceSide) (d : Widths) (hw : d.w≤d.H) :
    validSchedule (schedule side) (initial d) := by
  cases side
  all_goals simp [schedule,validSchedule,valid,eval,put,initial,originalValues,sourceBase,Function.update,hw]

 theorem execute_eq (side : SourceSide) (d : Widths) :
    execute (schedule side) (initial d)=finished side d := by
  cases side <;> funext i <;> fin_cases i
  all_goals simp [schedule,execute,eval,put,initial,originalValues,sourceBase,Function.update,finished,
    targetStart,prefixStart,tStart,uStart,sourceStart]
  all_goals omega

 theorem initial_bounded (d : Widths) (hb : ∀ i, originalValues d i≤d.addressBits) :
    Bounded (initial d) d.addressBits := by
  intro i
  by_cases hi : i.val<10
  · simpa [initial,hi] using hb ⟨i.val,hi⟩
  · simp [initial,hi]

def constant := 300*3^29

theorem schedule_length (side : SourceSide) : (schedule side).length=29 := rfl

theorem cost_bound (side : SourceSide) (d : Widths)
    (hb : ∀ i, originalValues d i≤d.addressBits) :
    scheduleCost (schedule side) (initial d)≤constant*(d.addressBits+1) := by
  have h := scheduleCost_bounded (schedule side) (initial d) d.addressBits (initial_bounded d hb)
  simpa only [schedule_length,constant] using h

end
end IntegerMultBounds.Machine.ActiveRepairRankHeadersData
