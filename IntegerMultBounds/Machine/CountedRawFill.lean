import IntegerMultBounds.Machine.CountedLoopReuse
import IntegerMultBounds.Machine.GrowingCounterData

/-! Exact delimiter-free constant filling with a physical reusable countdown.
The immutable count is supplied on its own tape; no generated count is assumed.
The inner clock is reset and cleared to its retained sentinel by this subroutine. -/
namespace IntegerMultBounds.Machine.CountedRawFill

/-- Replace precisely one finite interval and retain every surrounding cell. -/
def filled (f : ℤ → Fin 4) (p : ℤ) (n : ℕ) (symbol : Fin 4) : ℤ → Fin 4 :=
  fun z => if p ≤ z ∧ z < p+n then symbol else f z

@[simp] theorem filled_zero (f : ℤ → Fin 4) (p : ℤ) (symbol : Fin 4) : filled f p 0 symbol = f := by
  funext z
  simp [filled]

theorem filled_outside (f : ℤ → Fin 4) (p : ℤ) (n : ℕ) (symbol : Fin 4) (z : ℤ)
    (hz : z < p ∨ p+n ≤ z) : filled f p n symbol z = f z := by
  simp only [filled,ite_eq_right (by omega : ¬(p ≤ z ∧ z < p+n))]

theorem filled_succ (f : ℤ → Fin 4) (p : ℤ) (n : ℕ) (symbol : Fin 4) :
    Function.update (filled f p n symbol) (p+n) symbol = filled f p (n+1) symbol := by
  funext z
  by_cases hz : z = p+n
  · subst z; simp [filled]
  · rw [Function.update_of_ne hz]
    simp only [filled]
    have he : (p ≤ z ∧ z < p+(n : ℤ)) ↔ (p ≤ z ∧ z < p+((n+1 : ℕ) : ℤ)) := by omega
    simp only [he]

/-- Filling is the literal raw constant word on the same tape background. -/
theorem filled_word (f : ℤ → Fin 4) (p : ℤ) (n : ℕ) (symbol : Fin 4) :
    filled f p n symbol = putWord f p (List.replicate n symbol) := by
  induction n with
  | zero => simp [putWord]
  | succ n ih =>
    have h := putWord_append_forward f p (List.replicate n symbol) [symbol]
    simp only [List.length_replicate,putWord] at h
    have hs := filled_succ f p n symbol
    rw [ih] at hs
    simpa only [List.replicate_add,List.replicate_one,List.length_replicate,putWord] using
      hs.symm.trans h

/-- Consecutive fills coalesce; this supports streamed row groups without
resetting or recreating any payload data. -/
theorem filled_adjacent (f : ℤ → Fin 4) (p : ℤ) (n m : ℕ) (symbol : Fin 4) :
    filled (filled f p n symbol) (p+n) m symbol = filled f p (n+m) symbol := by
  funext z
  simp only [filled]
  split_ifs <;> try rfl
  all_goals omega

/-- Erasing a placed word recovers its exact clean background, including
every cell outside its occupied interval. -/
theorem erased_word (f : ℤ → Fin 4) (p : ℤ) (xs : List (Fin 4))
    (hblank : ∀ z : ℤ, p ≤ z → z < p+xs.length → f z = blank) :
    filled (putWord f p xs) p xs.length blank = f := by
  funext z
  by_cases hz : p ≤ z ∧ z < p+xs.length
  · simp only [filled,ite_eq_left hz]
    exact (hblank z hz.1 hz.2).symm
  · rw [filled_outside _ _ _ _ _ (by omega)]
    exact putWord_outside f p z xs (by omega)

def one (f : ℤ → Fin 4) (p : ℤ) : Tapes 1 0 := ⟨fun _ => p,fun _ => f⟩

def cell (symbol : Fin 4) : Program 1 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun state _ => if state = 0 then some (1,fun _ => (symbol,Move.right)) else none

theorem cell_hoare (symbol : Fin 4) (f : ℤ → Fin 4) (p : ℤ) :
    HoareTime (cell symbol) (fun v => v = one f p)
      (fun v => v = one (Function.update f p symbol) (p+1)) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,fun _ => p+1,fun _ => Function.update f p symbol⟩,le_rfl,?_,?_,rfl⟩
  · simp [run_one,step,cell,Tapes.start,one,Move.offset]
    funext i z
    by_cases h : z = p <;> simp [h]
  · simp [step,cell]

def program (symbol : Fin 4) : Program 3 18 0 := CountedLoopReuse.program (cell symbol)

def bank (f : ℤ → Fin 4) (p : ℤ) (bs : List Bool) : Tapes 3 0 :=
  CountedLoopReuse.bank (one f p) CountedCopyReuse.empty (CountedCopyReuse.binary bs) 1 1

/-- Count preparation, every actual fill transition, all joins and clock
cleanup are charged. The data head finishes just after the filled interval. -/
theorem fill_hoare (symbol : Fin 4) (f : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :
    HoareTime (program symbol) (fun v => v = bank f p bs)
      (fun v => v = bank (filled f p (Counter.value bs) symbol) (p+Counter.value bs) bs)
      (7*Counter.value bs+7*bs.length+16) := by
  let v := fun i : ℕ => one (filled f p i symbol) (p+i)
  have hb : ∀ i < Counter.value bs,
      HoareTime (cell symbol) (fun w => w = v i) (fun w => w = v (i+1)) 1 := by
    intro i _
    have h := cell_hoare symbol (filled f p i symbol) (p+i)
    rw [filled_succ] at h
    simpa only [v,Nat.cast_add,Nat.cast_one,add_assoc] using h
  have h := CountedLoopReuse.loop_hoare (cell symbol) bs (Counter.value bs) v (fun _ => 1) rfl hb
  simpa [program,bank,v,Nat.mul_succ,show ∀ n : ℕ, n+6*n = 7*n by omega] using h

theorem fill_linear (symbol : Fin 4) (f : ℤ → Fin 4) (p : ℤ) (bs : List Bool)
    (hc : GrowingCounterData.Canonical bs) :
    HoareTime (program symbol) (fun v => v = bank f p bs)
      (fun v => v = bank (filled f p (Counter.value bs) symbol) (p+Counter.value bs) bs)
      (14*Counter.value bs+23) := by
  have hw := GrowingCounterData.canonical_width bs hc
  have hl := Nat.log2_le_self (Counter.value bs)
  exact (fill_hoare symbol f p bs).consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.CountedRawFill
