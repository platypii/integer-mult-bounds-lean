import IntegerMultBounds.Machine.NativeColumnPhaseFlagsPlaced

/-! Fixed Gaussian-unit flags are written by one actual transition. In
particular phase2 writes false/true, without accepting external phase bits. -/
namespace IntegerMultBounds.Machine.NativeFixedPhaseFlags
open UnitPhaseNumerator (flags low high)
open MarkedWordCleanup (one)

def write (p : Fin 4) : Program 2 2 2 where
  tapes_pos := by decide
  start := 0
  transition := fun st _ => if st=0 then some (1,fun i =>
    (bitSymbol (if i=0 then low p else high p),Move.stay)) else none

def negative := write 2

theorem writes (p : Fin 4) : HoareTime (write p)
    (fun v => v=SharedBank.empty 2 2) (fun v => v=flags p) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(flags p).head,(flags p).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,write,Tapes.start,ite_true,Move.offset,add_zero]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z
      fin_cases i <;> simp [flags,one,Tapes.append,putWord,SharedBank.empty,Fin.addCases,
        Function.update_apply]
  · simp [step,write]

theorem negative_runs : HoareTime negative
    (fun v => v=SharedBank.empty 2 2) (fun v => v=flags 2) 1 := writes 2

noncomputable def triple (p : Fin 4) := RawLinearCombinationCleanup.prepend (write p) 1

theorem triple_runs (p : Fin 4) (header : Tapes 1 2) :
    HoareTime (triple p) (fun v => v=header.append (SharedBank.empty 2 2))
      (fun v => v=header.append (flags p)) 1 :=
  RawLinearCombinationCleanup.prepend_runs (write p) _ _ header (writes p)

end IntegerMultBounds.Machine.NativeFixedPhaseFlags
