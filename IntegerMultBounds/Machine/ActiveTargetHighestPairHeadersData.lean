import IntegerMultBounds.Machine.ActiveTargetHighestPairData
import IntegerMultBounds.Machine.ActiveRepairRankHeadersCommands
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersPowerRound

/-! A finite arithmetic/power schedule derives all ten highest-bit consumer
headers from five numeric geometry inputs, with no supplied dimensions. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestPairHeadersData
noncomputable section
open ActiveTargetHighestPairData
open ActiveRepairRankHeadersCommands

def originalValues (g : Geometry) : Fin 5 → ℕ := ![g.L,g.G,g.K,g.rows,g.payload]
def initial (g : Geometry) : State := fun i =>
  if h : i.val<5 then some (originalValues g ⟨i.val,h⟩) else none
def seeded (g : Geometry) := put (initial g) 9 1

def arithmetic (g : Geometry) : State := fun i =>
  if h : i.val<5 then some (originalValues g ⟨i.val,h⟩)
  else if h : i.val<12 then some (values g ⟨i.val-5,by omega⟩) else none

def poweredG (g : Geometry) := put (arithmetic g) 14 (gap g)
def poweredL (g : Geometry) := put (poweredG g) 16 (2^g.L)
def multipliedP (g : Geometry) := put (poweredL g) 13 (P g)
def poweredK (g : Geometry) := put (multipliedP g) 15 (2^g.K)
def multipliedB (g : Geometry) := put (poweredK g) 12 (suffix g)
def finished (g : Geometry) : State := fun i =>
  if h : i.val<5 then some (originalValues g ⟨i.val,h⟩)
  else if h : i.val<15 then some (values g ⟨i.val-5,by omega⟩) else none

def arithmeticSchedule : List Command :=
  [.copy 0 5 (by decide),.add 5 9 (by decide),.add 5 1 (by decide),
   .copy 1 6 (by decide),.copy 1 7 (by decide),.copy 9 8 (by decide),.add 8 9 (by decide),
   .copy 9 10 (by decide),.copy 3 11 (by decide)]
def scratchCleanup : List Command := [.erase 15,.erase 16]
def outputCleanup : List Command := [.erase 5,.erase 6,.erase 7,.erase 8,.erase 9,
  .erase 10,.erase 11,.erase 12,.erase 13,.erase 14]

theorem arithmetic_valid (g : Geometry) : validSchedule arithmeticSchedule (seeded g) := by
  simp [arithmeticSchedule,validSchedule,valid,eval,put,seeded,initial,originalValues,Function.update]
theorem arithmetic_eq (g : Geometry) : execute arithmeticSchedule (seeded g)=arithmetic g := by
  funext i; fin_cases i
  all_goals simp [arithmeticSchedule,execute,eval,put,seeded,initial,originalValues,Function.update,
    arithmetic,values,W]

theorem scratch_valid (g : Geometry) : validSchedule scratchCleanup (multipliedB g) := by
  simp [scratchCleanup,validSchedule,valid,eval,put,multipliedB,poweredK,multipliedP,poweredL,poweredG,Function.update]
theorem scratch_eq (g : Geometry) : execute scratchCleanup (multipliedB g)=finished g := by
  funext i; fin_cases i
  all_goals simp [scratchCleanup,execute,eval,put,multipliedB,poweredK,multipliedP,poweredL,poweredG,
    arithmetic,finished,values,Function.update]

theorem cleanup_valid (g : Geometry) : validSchedule outputCleanup (finished g) := by
  simp [outputCleanup,validSchedule,valid,eval,finished,Function.update]
theorem cleanup_eq (g : Geometry) : execute outputCleanup (finished g)=initial g := by
  funext i; fin_cases i
  all_goals simp [outputCleanup,execute,eval,finished,initial,Function.update]

end
end IntegerMultBounds.Machine.ActiveTargetHighestPairHeadersData
