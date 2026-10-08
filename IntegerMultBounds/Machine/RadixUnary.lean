import IntegerMultBounds.Machine.RadixDigits
import IntegerMultBounds.Machine.Hoare

/-! Literal finite-state digit transduction on two tapes. The lookup table is
fixed independently of the word width. Each input digit costs one transition,
the complete source tape is preserved, and only the output segment changes. -/

namespace IntegerMultBounds.Machine.RadixUnary

open RadixDigits
variable {q s : ℕ}

/-- One finite lookup selects the next control state and output digit. -/
abbrev Table (q s : ℕ) := Fin s → Fin q → Fin s × Fin q

def outputs (next : Table q s) : Fin s → List (Fin q) → List (Fin q)
  | _, [] => []
  | state, x :: xs => (next state x).2 :: outputs next (next state x).1 xs

def finalState (next : Table q s) : Fin s → List (Fin q) → Fin s
  | state, [] => state
  | state, x :: xs => finalState next (next state x).1 xs

@[simp] theorem outputs_length (next : Table q s) (state : Fin s) (xs : List (Fin q)) :
    (outputs next state xs).length = xs.length := by
  induction xs generalizing state with
  | nil => rfl
  | cons x xs ih => simp [outputs,ih]

/-- The only information inspected is finite control and the scanned digit. -/
def program (q s : ℕ) (start : Fin s) (next : Table q s) : Program 2 s q where
  tapes_pos := by decide
  start := start
  transition := fun state symbols =>
    match readDigit (symbols 0) with
    | some x => some ((next state x).1, fun i =>
        (if i = 1 then digitSymbol (next state x).2 else symbols i, .right))
    | none => none

def cfg (f out : ℤ → Fin (q + 4)) (p r : ℤ) (state : Fin s) : Config 2 s q where
  state := state
  head := fun i => if i = 0 then p else r
  tape := fun i => if i = 0 then f else out

theorem digit_step (start state : Fin s) (next : Table q s) (x : Fin q)
    (f out : ℤ → Fin (q + 4)) (p r : ℤ) (hx : f p = digitSymbol x) :
    step (program q s start next) (cfg f out p r state) =
      some (cfg f (Function.update out r (digitSymbol (next state x).2))
        (p+1) (r+1) (next state x).1) := by
  have ht : (program q s start next).transition state
      (fun i => (cfg f out p r state).tape i ((cfg f out p r state).head i)) =
      some ((next state x).1, fun i =>
        (if i = 1 then digitSymbol (next state x).2
          else (cfg f out p r state).tape i ((cfg f out p r state).head i), Move.right)) := by
    simp [program,cfg,hx]
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply,eq_comm]
    intro hj
    rw [hj]

/-- Any non-digit source symbol, including blank, actually halts the machine. -/
theorem halt (start state : Fin s) (next : Table q s)
    (f out : ℤ → Fin (q+4)) (p r : ℤ) (h : readDigit (f p) = none) :
    step (program q s start next) (cfg f out p r state) = none := by
  simp [step,program,cfg,h]

/-- Exact width execution for arbitrary control, head offsets, and backgrounds. -/
theorem columns_run (start state : Fin s) (next : Table q s) (xs : List (Fin q))
    (f out : ℤ → Fin (q+4)) (p r : ℤ) :
    run (program q s start next) xs.length
      (cfg (putWord f p (xs.map digitSymbol)) out p r state) =
      some (cfg (putWord f p (xs.map digitSymbol))
        (putWord out r ((outputs next state xs).map digitSymbol))
        (p+xs.length) (r+xs.length) (finalState next state xs)) := by
  induction xs generalizing state f out p r with
  | nil => simp [run,outputs,finalState,putWord]
  | cons x xs ih =>
    have hs := digit_step start state next x (putWord f p ((x::xs).map digitSymbol)) out p r
      (by rw [List.map_cons,putWord_head])
    simp only [List.length_cons,run,hs,Option.bind_some]
    have hr := ih (next state x).1 (Function.update f p (digitSymbol x))
      (Function.update out r (digitSymbol (next state x).2)) (p+1) (r+1)
    simpa only [← putWord_cons,List.map_cons,outputs,finalState,List.length_cons,
      Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using hr

/-- Exact width execution followed by halt at the unchanged non-digit terminator. -/
theorem exact_run (start state : Fin s) (next : Table q s) (xs : List (Fin q))
    (f out : ℤ → Fin (q+4)) (p r : ℤ)
    (hf : readDigit (f (p+xs.length)) = none) :
    run (program q s start next) xs.length
      (cfg (putWord f p (xs.map digitSymbol)) out p r state) =
      some (cfg (putWord f p (xs.map digitSymbol))
        (putWord out r ((outputs next state xs).map digitSymbol))
        (p+xs.length) (r+xs.length) (finalState next state xs)) ∧
    step (program q s start next)
      (cfg (putWord f p (xs.map digitSymbol))
        (putWord out r ((outputs next state xs).map digitSymbol))
        (p+xs.length) (r+xs.length) (finalState next state xs)) = none := by
  refine ⟨columns_run start state next xs f out p r,?_⟩
  apply halt
  rw [putWord_outside _ _ _ _ (Or.inr (by simp))]
  exact hf

/-- Full-tape Hoare postcondition; only the designated output word is overwritten. -/
theorem hoare (start : Fin s) (next : Table q s) (xs : List (Fin q))
    (f out : ℤ → Fin (q+4)) (p r : ℤ)
    (hf : readDigit (f (p+xs.length)) = none) :
    HoareTime (program q s start next)
      (fun v => v = (cfg (putWord f p (xs.map digitSymbol)) out p r start).tapes)
      (fun v => v = (cfg (putWord f p (xs.map digitSymbol))
        (putWord out r ((outputs next start xs).map digitSymbol))
        (p+xs.length) (r+xs.length) (finalState next start xs)).tapes)
      xs.length := by
  rintro v rfl
  obtain ⟨hr,hh⟩ := exact_run start start next xs f out p r hf
  exact ⟨xs.length,_,le_rfl,hr,hh,rfl⟩

/-- Blank initialization gives a complete output word with a globally blank tail. -/
theorem to_blank (start : Fin s) (next : Table q s) (xs : List (Fin q)) :
    run (program q s start next) xs.length
      (cfg (wordTape (xs.map digitSymbol)) (fun _ => blank) 0 0 start) =
      some (cfg (wordTape (xs.map digitSymbol))
        (wordTape ((outputs next start xs).map digitSymbol))
        xs.length xs.length (finalState next start xs)) ∧
    step (program q s start next)
      (cfg (wordTape (xs.map digitSymbol))
        (wordTape ((outputs next start xs).map digitSymbol))
        xs.length xs.length (finalState next start xs)) = none := by
  have hw (ds : List (Fin q)) : putWord (fun _ => (blank : Fin (q+4))) 0 (ds.map digitSymbol) =
      wordTape (ds.map digitSymbol) := by
    funext j
    simpa using putWord_blank 0 j (ds.map digitSymbol)
  have h := exact_run start start next xs (fun _ => (blank : Fin (q+4)))
    (fun _ => blank) 0 0 readDigit_blank
  simpa only [hw,zero_add] using h

end IntegerMultBounds.Machine.RadixUnary
