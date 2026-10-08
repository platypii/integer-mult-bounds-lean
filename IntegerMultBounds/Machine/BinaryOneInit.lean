import IntegerMultBounds.Machine.Placement
import IntegerMultBounds.Machine.CountedCopyReuse
import IntegerMultBounds.Machine.GrowingCounterData

/-! Literal constant-one binary descriptor construction from a blank tape.
This fixed two-transition bootstrap supplies the one used to form Q minus one
for coordinate negation; no prewritten sentinel or digit is assumed. -/
namespace IntegerMultBounds.Machine.BinaryOneInit

def bank (f : ℤ → Fin 4) (p : ℤ) : Tapes 1 0 := ⟨fun _ => p,fun _ => f⟩

def initial : Tapes 1 0 := bank (fun _ => blank) 0

def finalBank : Tapes 1 0 := bank (CountedCopyReuse.binary [true]) 1

/-- Write the sentinel, advance once, write one, and truly halt. -/
def program : Program 1 3 0 where
  tapes_pos := by decide
  start := 0
  transition := fun state _ =>
    if state = 0 then some (1,fun _ => (separator,Move.right))
    else if state = 1 then some (2,fun _ => (bitSymbol true,Move.stay)) else none

theorem init_exact : Placement.ExactRun program 2 initial finalBank := by
  refine ⟨⟨2,finalBank.head,finalBank.tape⟩,?_,?_,rfl⟩
  · simp only [run,step,program,Tapes.start,initial,bank,ite_true,Option.bind_some]
    norm_num [Move.offset]
    refine ⟨rfl,?_⟩
    funext i z
    by_cases h₁ : z = 1 <;> by_cases h₀ : z = 0 <;>
      simp [finalBank,bank,CountedCopyReuse.binary,CountedCopyReuse.empty,putBits,
        h₁,h₀]
  · simp [step,program]

theorem init_hoare : HoareTime program (fun v => v = initial) (fun v => v = finalBank) 2 := by
  rintro v rfl
  obtain ⟨last,hr,hh,hf⟩ := init_exact
  exact ⟨2,last,le_rfl,hr,hh,hf⟩

@[simp] theorem value_one : Counter.value [true] = 1 := by decide

theorem canonical_one : GrowingCounterData.Canonical [true] := by
  exact Or.inr rfl

end IntegerMultBounds.Machine.BinaryOneInit
