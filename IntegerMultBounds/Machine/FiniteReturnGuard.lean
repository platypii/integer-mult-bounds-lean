import IntegerMultBounds.Machine.FiniteReturnStackAt

/-! A physical empty-stack guard. It peeks one cell left of the stack head,
then returns that head exactly; empty stacks halt at state2, occupied stacks
halt at state3. No bottom marker or free empty-stack oracle is assumed. -/
namespace IntegerMultBounds.Machine.FiniteReturnGuard
variable {t a : ℕ}

def action (slot : Fin t) (move : Move) (sy : Fin t → Fin (a+4)) (i : Fin t) :=
  (sy i,if i=slot then move else Move.stay)
def program (slot : Fin t) : Program t 4 a where
  tapes_pos := Nat.zero_lt_of_lt slot.isLt
  start := 0
  transition := fun st sy =>
    if st=0 then some (1,action slot .left sy)
    else if st=1 then some (if sy slot=blank then 2 else 3,action slot .right sy)
    else none

def probe (slot : Fin t) (v : Tapes t a) : Config t 4 a :=
  ⟨1,Function.update v.head slot (v.head slot-1),v.tape⟩
def terminal (v : Tapes t a) (empty : Bool) : Config t 4 a :=
  ⟨if empty then 2 else 3,v.head,v.tape⟩

private theorem first (slot : Fin t) (v : Tapes t a) :
    step (program slot) (v.start (program slot))=some (probe slot v) := by
  simp only [step,program,Tapes.start,ite_true,probe]
  congr 1
  congr 1
  · funext i
    by_cases hi : i=slot <;> simp [action,hi,Move.offset,sub_eq_add_neg]
  · funext i z
    by_cases hz : z=v.head i <;> simp [hz,action]

private theorem second (slot : Fin t) (v : Tapes t a) :
    step (program slot) (probe slot v)=
      some (terminal v (decide (v.tape slot (v.head slot-1)=blank))) := by
  simp only [step,program,probe,Fin.reduceEq,ite_false,ite_true,Function.update_self,terminal]
  congr 1
  congr 1
  · simp
  · funext i
    by_cases hi : i=slot <;> simp [action,hi,Move.offset]
  · funext i z
    by_cases hz : z=Function.update v.head slot (v.head slot-1) i <;> simp [hz,action]

theorem exact_run (slot : Fin t) (v : Tapes t a) :
    run (program slot) 2 (v.start (program slot))=
      some (terminal v (decide (v.tape slot (v.head slot-1)=blank))) := by
  rw [show 2=1+1 from rfl,run_add,run_one,first]
  simp only [Option.bind_some,run_one,second]

theorem terminal_halt (slot : Fin t) (v : Tapes t a) (empty : Bool) :
    step (program slot) (terminal v empty)=none := by
  cases empty <;> simp [step,program,terminal]

/-- Every tape cell and every head, including the probed stack, is restored. -/
theorem preserves (slot : Fin t) (v : Tapes t a) :
    HoareTime (program slot) (fun w => w=v) (fun w => w=v) 2 := by
  intro w hw
  subst w
  exact ⟨2,_,le_rfl,exact_run slot v,terminal_halt slot v _,rfl⟩

end IntegerMultBounds.Machine.FiniteReturnGuard
