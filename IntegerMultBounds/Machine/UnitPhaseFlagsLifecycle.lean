import IntegerMultBounds.Machine.UnitPhaseNumerator

/-! The accumulator flags are physically initialized to zero and erased
after every coefficient. Both operations take one actual transition. -/
namespace IntegerMultBounds.Machine.UnitPhaseFlagsLifecycle
open UnitPhaseNumerator (flags)

def write (sy : Fin 6) : Program 2 2 2 where
  tapes_pos := by decide
  start := 0
  transition := fun st _ => if st=0 then some (1,fun _ => (sy,Move.stay)) else none
def prepare := write (bitSymbol false)
def cleanup := write blank

theorem prepares : HoareTime prepare (fun v => v=SharedBank.empty 2 2)
    (fun v => v=flags 0) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(flags 0).head,(flags 0).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,prepare,write,Tapes.start,ite_true,Move.offset,add_zero]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z
      fin_cases i <;> simp [flags,MarkedWordCleanup.one,Tapes.append,putWord,
        UnitPhaseNumerator.low,UnitPhaseNumerator.high,SharedBank.empty,Fin.addCases,Function.update_apply]
      all_goals rfl
  · simp [step,prepare,write]

theorem cleans (p : Fin 4) : HoareTime cleanup (fun v => v=flags p)
    (fun v => v=SharedBank.empty 2 2) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(SharedBank.empty 2 2).head,(SharedBank.empty 2 2).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,cleanup,write,Tapes.start,ite_true,Move.offset,add_zero]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z
      fin_cases i <;> simp [flags,MarkedWordCleanup.one,Tapes.append,putWord,SharedBank.empty,Fin.addCases]
      all_goals intro hz; simp [hz]
  · simp [step,cleanup,write]

end IntegerMultBounds.Machine.UnitPhaseFlagsLifecycle
