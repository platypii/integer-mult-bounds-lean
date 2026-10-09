import IntegerMultBounds.Machine.CompactChildHeadersArithmetic

/-! Paid generation of the root enumerator's numeric state: exponent zero,
left boundary zero and width one are written, each selected piece advances
the generated boundary and decrements its digit clock, and each next base
digit increments the exponent and multiplies the generated width. -/
namespace IntegerMultBounds.Machine.CompactComplexRootPieceNumbers
noncomputable section
open CompactChildHeadersArithmetic
open ActiveRepairRankHeadersCommands (State put bank)
variable {a : ℕ}

def seed : List Op := [.constant 1 0,.constant 2 0,.constant 3 1]
def seeded (st : State) := put (put (put st 1 0) 2 0) 3 1

theorem seed_runs (st : State) (h1 : st 1=none) (h2 : st 2=none) (h3 : st 3=none) :
    HoareTime (compile (a := a) seed).2 (fun v => v=bank st) (fun v => v=bank (seeded st))
      (scheduleCost seed st) := by
  have hv : validSchedule seed st := by simp [seed,validSchedule,valid,eval,put,Function.update,h1,h2,h3]
  have he : execute seed st=seeded st := rfl
  simpa only [he] using schedule_runs (a := a) seed st hv

def piece : List Op :=
  [.existing (.command (.add 2 3 (by decide))),.constant 22 1,
    .existing (.command (.difference 4 22 23 (by decide))),
    .existing (.command (.erase 4)),.existing (.command (.copy 23 4 (by decide))),
    .existing (.command (.erase 22)),.existing (.command (.erase 23))]
def pieceDone (st : State) (left width count : ℕ) := put (put st 2 (left+width)) 4 (count-1)

theorem piece_execute (st : State) (left width count : ℕ)
    (h2 : st 2=some left) (h3 : st 3=some width) (h4 : st 4=some count)
    (h22 : st 22=none) (h23 : st 23=none) : execute piece st=pieceDone st left width count := by
  funext i
  by_cases hi2 : i=2
  · subst i; simp [piece,execute,eval,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,put,pieceDone,Function.update,h2,h3]
  by_cases hi4 : i=4
  · subst i; simp [piece,execute,eval,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,put,pieceDone,Function.update,h4]
  by_cases hi22 : i=22
  · subst i; simp [piece,execute,eval,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,put,pieceDone,Function.update,h22]
  by_cases hi23 : i=23
  · subst i; simp [piece,execute,eval,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,put,pieceDone,Function.update,h23]
  simp [piece,execute,eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,put,pieceDone,Function.update,hi2,hi4,hi22,hi23]

theorem piece_runs (st : State) (left width count : ℕ) (hc : 0 < count)
    (h2 : st 2=some left) (h3 : st 3=some width) (h4 : st 4=some count)
    (h22 : st 22=none) (h23 : st 23=none) :
    HoareTime (compile (a := a) piece).2 (fun v => v=bank st)
      (fun v => v=bank (pieceDone st left width count)) (scheduleCost piece st) := by
  have hv : validSchedule piece st := by
    simp [piece,validSchedule,valid,eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,put,Function.update,
      h2,h3,h4,h22,h23]
    omega
  have h := schedule_runs (a := a) piece st hv
  rw [piece_execute st left width count h2 h3 h4 h22 h23] at h
  exact h

def level (base : ℕ) : List Op :=
  [.constant 22 base,.existing (.product ![22,3,23] (by decide)),.constant 24 1,
    .existing (.command (.add 1 24 (by decide))),
    .existing (.command (.erase 3)),.existing (.command (.copy 23 3 (by decide))),
    .existing (.command (.erase 22)),.existing (.command (.erase 23)),.existing (.command (.erase 24))]
def levelDone (st : State) (exponent width base : ℕ) := put (put st 1 (exponent+1)) 3 (width*base)

theorem level_execute (st : State) (exponent width base : ℕ)
    (h1 : st 1=some exponent) (h3 : st 3=some width)
    (h22 : st 22=none) (h23 : st 23=none) (h24 : st 24=none) :
    execute (level base) st=levelDone st exponent width base := by
  funext i
  by_cases hi1 : i=1
  · subst i; simp [level,execute,eval,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,put,levelDone,Function.update,h1]
  by_cases hi3 : i=3
  · subst i; simp [level,execute,eval,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,put,levelDone,Function.update,h3]
  by_cases hi22 : i=22
  · subst i; simp [level,execute,eval,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,put,levelDone,Function.update,h22]
  by_cases hi23 : i=23
  · subst i; simp [level,execute,eval,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,put,levelDone,Function.update,h23]
  by_cases hi24 : i=24
  · subst i; simp [level,execute,eval,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,put,levelDone,Function.update,h24]
  simp [level,execute,eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,put,levelDone,Function.update,hi1,hi3,hi22,hi23,hi24]

theorem level_runs (st : State) (exponent width base : ℕ) (hb : 0 < base)
    (h1 : st 1=some exponent) (h3 : st 3=some width)
    (h22 : st 22=none) (h23 : st 23=none) (h24 : st 24=none) :
    HoareTime (compile (a := a) (level base)).2 (fun v => v=bank st)
      (fun v => v=bank (levelDone st exponent width base)) (scheduleCost (level base) st) := by
  have hv : validSchedule (level base) st := by
    simp [level,validSchedule,valid,eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,put,Function.update,
      h1,h3,h22,h23,h24,hb]
  have h := schedule_runs (a := a) (level base) st hv
  rw [level_execute st exponent width base h1 h3 h22 h23 h24] at h
  exact h


theorem seed_cost_le (st : State) : scheduleCost seed st ≤ 30 := by
  have h0 : (RecursiveChildQuotientsConstant.bits 0).length = 0 := rfl
  have h1 := ActiveRepairRankHeadersCommands.bits_length 1
  simp [seed,scheduleCost,cost,RecursiveChildQuotientsConstant.cost]
  omega

theorem piece_cost_le (st : State) (left width count : ℕ)
    (h2 : st 2=some left) (h3 : st 3=some width) (h4 : st 4=some count) :
    scheduleCost piece st ≤ 1000*(left+width+count+1) := by
  have h1 := ActiveRepairRankHeadersCommands.bits_length 1
  have hpred : count-1 ≤ count := Nat.sub_le _ _
  simp [piece,scheduleCost,cost,eval,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,put,Function.update,
    h2,h3,h4,RecursiveChildQuotientsConstant.cost]
  omega

theorem level_cost_le (st : State) (exponent width base : ℕ) (hb : 0 < base)
    (h1 : st 1=some exponent) (h3 : st 3=some width) :
    scheduleCost (level base) st ≤ 1000*(exponent+width*base+base+1) := by
  have hm := ActiveRepairRankHeadersCommands.bits_length base
  have ho := ActiveRepairRankHeadersCommands.bits_length 1
  have hwidth : width ≤ width*base := Nat.le_mul_of_pos_right _ hb
  simp [level,scheduleCost,cost,eval,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,put,Function.update,
    h1,h3,RecursiveChildQuotientsConstant.cost]
  omega

def clearClock : List Op := [.existing (.command (.erase 4))]
theorem clearClock_runs (st : State) (h4 : st 4=some 0) :
    HoareTime (compile (a := a) clearClock).2 (fun v => v=bank st)
      (fun v => v=bank (Function.update st 4 none)) 101 := by
  have hv : validSchedule clearClock st := by
    simp [clearClock,validSchedule,valid,ActivePrefixStageHeadersOps.valid,
      ActiveRepairRankHeadersCommands.valid,h4]
  have h := schedule_runs (a := a) clearClock st hv
  simpa [clearClock,execute,eval,scheduleCost,cost,ActivePrefixStageHeadersOps.eval,
    ActivePrefixStageHeadersOps.cost,ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.cost,h4] using h

/-- Root widths are generated from one by actual paid multiplication. -/
theorem seeded_width (st : State) : seeded st 3=some 1 := by simp [seeded,put]
theorem level_power (st : State) (exponent base : ℕ) :
    levelDone st exponent (base^exponent) base 3=some (base^(exponent+1)) := by
  simp [levelDone,put,pow_succ]

end
end IntegerMultBounds.Machine.CompactComplexRootPieceNumbers
