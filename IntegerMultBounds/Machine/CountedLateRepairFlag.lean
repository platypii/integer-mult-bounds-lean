import IntegerMultBounds.Machine.ExactFrame

/-! Combine the two physically written exceptional flags of the later repair.
Both input heads are at one; the result head stays at one and the second
flag tape is erased and returned to zero. -/
namespace IntegerMultBounds.Machine.CountedLateRepairFlag
variable {a : ℕ}

def key (x : Bool) : ℤ → Fin (a+4) := Function.update (fun _ => blank) 0 (bitSymbol x)
def input (x y : Bool) : Tapes 2 a := ⟨![1,1],![key x,key y]⟩
def output (x y : Bool) : Tapes 2 a := ⟨![1,0],![key (x || y),fun _ => blank]⟩

def program : Program 2 3 a where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s=0 then some (1,fun i => (symbols i,.left))
    else if s=1 then some (2,fun i =>
      if i=0 then (bitSymbol (decide (symbols 0=bitSymbol true) ||
        decide (symbols 1=bitSymbol true)),.right) else (blank,.stay))
    else none

private theorem rewind (x y : Bool) :
    step program ((input (a := a) x y).start program) =
      some (⟨1,![0,0],![key x,key y]⟩ : Config 2 3 a) := by
  unfold step Tapes.start program input
  simp only [key,ite_true,Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i j; fin_cases i <;> simp [Function.update_apply] <;> omega

private theorem combine (x y : Bool) :
    step program (⟨1,![0,0],![key x,key y]⟩ : Config 2 3 a) =
      some (⟨2,(output (a := a) x y).head,(output (a := a) x y).tape⟩ : Config 2 3 a) := by
  cases x <;> cases y <;> unfold step program output key
  all_goals simp only [bitSymbol,blank]
  all_goals simp
  all_goals constructor
  all_goals (first | (funext i; fin_cases i <;> rfl) |
    (funext i j; fin_cases i <;> by_cases hj : j=0 <;> simp [hj]))

theorem runs (x y : Bool) :
    HoareTime (program (a := a)) (fun v => v=input x y)
      (fun v => v=output x y) 2 := by
  rintro v rfl
  refine ⟨2,⟨2,(output (a := a) x y).head,(output (a := a) x y).tape⟩,le_refl _,?_,?_,rfl⟩
  · rw [run,rewind]
    simp only [Option.bind_some]
    rw [run,combine]
    rfl
  · simp [step,program]

end IntegerMultBounds.Machine.CountedLateRepairFlag
