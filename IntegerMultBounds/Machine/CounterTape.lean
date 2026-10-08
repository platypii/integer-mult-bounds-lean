import IntegerMultBounds.Machine.BitTape
import IntegerMultBounds.Machine.Counter
import IntegerMultBounds.Machine.Loop

/-! A three-state, four-symbol tape implementation of fixed-width binary
increment. It propagates carry, then returns to a left boundary marker. The
runtime accounts for every movement in both directions, including overflow. -/

namespace IntegerMultBounds.Machine

namespace CounterTape

/-- State zero propagates carry, one rewinds, and two halts. -/
def program : Program 1 3 0 where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols =>
    if state = 0 then
      if symbols 0 = bitSymbol true then some (0, fun _ => (bitSymbol false, .right))
      else if symbols 0 = bitSymbol false then some (1, fun _ => (bitSymbol true, .left))
      else if symbols 0 = blank then some (1, fun _ => (blank, .left))
      else none
    else if state = 1 then
      if symbols 0 = separator then some (2, fun _ => (separator, .right))
      else some (1, fun i => (symbols i, .left))
    else none

def cfg (f : ℤ → Fin 4) (head : ℤ) (state : Fin 3) : Config 1 3 0 :=
  ⟨state, fun _ => head, fun _ => f⟩

theorem step_true (f : ℤ → Fin 4) (p : ℤ) (h : f p = bitSymbol true) :
    step program (cfg f p 0) =
      some (cfg (Function.update f p (bitSymbol false)) (p + 1) 0) := by
  simp only [step, program, cfg, h, ↓reduceIte, Move.offset]
  congr 1
  congr 1
  funext i j
  simp [Function.update_apply, eq_comm]

theorem step_false (f : ℤ → Fin 4) (p : ℤ) (h : f p = bitSymbol false) :
    step program (cfg f p 0) =
      some (cfg (Function.update f p (bitSymbol true)) (p - 1) 1) := by
  simp only [step, program, cfg, h]
  norm_num [bitSymbol, Move.offset]
  constructor
  · funext i; omega
  · funext i j; simp [Function.update_apply, eq_comm]

theorem step_blank (f : ℤ → Fin 4) (p : ℤ) (h : f p = blank) :
    step program (cfg f p 0) = some (cfg f (p - 1) 1) := by
  simp only [step, program, cfg, h]
  norm_num [bitSymbol, blank, Move.offset]
  constructor
  · funext i; omega
  · funext i j
    by_cases hj : j = p
    · subst j; simpa [blank] using h.symm
    · simp [hj]

theorem step_rewind (f : ℤ → Fin 4) (p : ℤ) (h : f p ≠ separator) :
    step program (cfg f p 1) = some (cfg f (p - 1) 1) := by
  simp only [step, program, cfg]
  norm_num [h, Move.offset]
  constructor
  · funext i; omega
  · funext i j
    by_cases hj : j = p
    · subst j; simp
    · simp [hj]

theorem step_marker (f : ℤ → Fin 4) (p : ℤ) (h : f p = separator) :
    step program (cfg f p 1) = some (cfg f (p + 1) 2) := by
  simp only [step, program, cfg]
  norm_num [h, Move.offset]
  funext i j
  by_cases hj : j = p
  · subst j; simpa using h.symm
  · simp [hj]

theorem halt (f : ℤ → Fin 4) (p : ℤ) : step program (cfg f p 2) = none := by
  simp [step, program, cfg]

/-- Forward transitions, including the blank transition on overflow. -/
def carrySteps : List Bool → ℕ
  | [] => 1
  | false :: _ => 1
  | true :: bs => carrySteps bs + 1

theorem carrySteps_bounds (bs : List Bool) :
    1 ≤ carrySteps bs ∧ carrySteps bs ≤ bs.length + 1 ∧
      carrySteps bs ≤ Counter.flips bs + 1 := by
  induction bs with
  | nil => simp [carrySteps, Counter.flips]
  | cons b bs ih =>
    cases b with
    | false => simp [carrySteps, Counter.flips]
    | true => simp only [carrySteps, Counter.flips, List.length_cons]; omega

/-- The carry phase performs exactly the list-level modular increment and
stops one cell to the left of the last inspected cell. -/
theorem carry_run (f : ℤ → Fin 4) (p : ℤ) (bs : List Bool)
    (hend : f (p + bs.length) = blank) :
    run program (carrySteps bs) (cfg (putBits f p bs) p 0) =
      some (cfg (putBits f p (Counter.increment bs)) (p + carrySteps bs - 2) 1) := by
  induction bs generalizing p f with
  | nil =>
    simp only [List.length_nil, Nat.cast_zero, add_zero] at hend
    simpa [carrySteps, Counter.increment, putBits, run_one,
      show p + 1 - 2 = p - 1 by omega] using step_blank f p hend
  | cons b bs ih =>
    cases b with
    | false =>
      have hs := step_false (putBits f p (false :: bs)) p (putBits_head f p false bs)
      simpa [carrySteps, Counter.increment, run_one, putBits, Function.update_idem,
        show p + 1 - 2 = p - 1 by omega] using hs
    | true =>
      have hs := step_true (putBits f p (true :: bs)) p (putBits_head f p true bs)
      have he : Function.update (putBits f p (true :: bs)) p (bitSymbol false) =
          putBits (Function.update f p (bitSymbol false)) (p + 1) bs := by
        rw [putBits_update_before f (p + 1) p (bitSymbol false) bs (by omega)]
        simp [putBits]
      rw [he] at hs
      have hend' : (Function.update f p (bitSymbol false)) (p + 1 + bs.length) = blank := by
        rw [Function.update_of_ne (by omega)]
        simpa [List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hend
      have hr := ih (Function.update f p (bitSymbol false)) (p + 1) hend'
      simp only [carrySteps, Counter.increment]
      rw [show carrySteps bs + 1 = 1 + carrySteps bs by omega, run_add]
      simp only [run_one, hs, Option.bind_some]
      simpa only [← putBits_cons, Nat.cast_add, Nat.cast_one, add_assoc,
        add_comm, add_left_comm] using hr

/-- Rewinding preserves every cell and stops at the first digit after the
marker. Its runtime includes the final right movement onto that digit. -/
theorem rewind_run (f : ℤ → Fin 4) (n : ℕ) (hzero : f 0 = separator)
    (hno : ∀ j : ℕ, 1 ≤ j → j ≤ n → f j ≠ separator) :
    run program (n + 1) (cfg f n 1) = some (cfg f 1 2) := by
  induction n with
  | zero => simpa only [Nat.cast_zero, run_one, zero_add] using step_marker f 0 hzero
  | succ n ih =>
    have hs : step program (cfg f ((n : ℤ) + 1) 1) = some (cfg f n 1) := by
      simpa only [add_sub_cancel_right] using
        step_rewind f ((n : ℤ) + 1) (by exact_mod_cast hno (n + 1) (by omega) le_rfl)
    simp only [Nat.cast_add, Nat.cast_one, run, hs, Option.bind_some]
    exact ih (fun j hj hn => hno j hj (by omega))

/-- One fixed program works for every width and every initial bit pattern.
Only the marker and end blank are prescribed outside the represented digits. -/
theorem increment_exact (f : ℤ → Fin 4) (bs : List Bool)
    (hzero : f 0 = separator) (hend : f (1 + bs.length) = blank) :
    run program (2 * carrySteps bs) (cfg (putBits f 1 bs) 1 0) =
      some (cfg (putBits f 1 (Counter.increment bs)) 1 2) := by
  obtain ⟨hpos, hlen, _⟩ := carrySteps_bounds bs
  let n := carrySteps bs - 1
  have hn : n + 1 = carrySteps bs := by dsimp [n]; omega
  have hh : (1 : ℤ) + carrySteps bs - 2 = (n : ℤ) := by omega
  have hmark : putBits f 1 (Counter.increment bs) 0 = separator := by
    rw [putBits_outside f 1 0 _ (Or.inl (by omega)), hzero]
  have hno : ∀ j : ℕ, 1 ≤ j → j ≤ n →
      putBits f 1 (Counter.increment bs) j ≠ separator := by
    intro j hj hjn
    apply putBits_ne_separator
    · omega
    · rw [Counter.increment_length]; omega
  rw [show 2 * carrySteps bs = carrySteps bs + (n + 1) by omega, run_add,
    carry_run f 1 bs hend]
  simp only [Option.bind_some, hh]
  exact rewind_run _ n hmark hno

/-- Complete tape runtime, including the head return, with the same potential
as the list-level increment. -/
theorem increment_potential (bs : List Bool) :
    2 * carrySteps bs + 2 * Counter.weight (Counter.increment bs) ≤
      6 + 2 * Counter.weight bs := by
  have hcarry := (carrySteps_bounds bs).2.2
  have hflip := Counter.increment_potential bs
  omega

def tapes (f : ℤ → Fin 4) (bs : List Bool) : Tapes 1 0 :=
  ⟨fun _ => 1, fun _ => putBits f 1 bs⟩

/-- The counter is available to the verified composition and tape-frame rules. -/
theorem increment_hoare (f : ℤ → Fin 4) (bs : List Bool)
    (hzero : f 0 = separator) (hend : f (1 + bs.length) = blank) :
    HoareTime program (fun v => v = tapes f bs)
      (fun v => v = tapes f (Counter.increment bs)) (2 * carrySteps bs) := by
  rintro v rfl
  exact ⟨2 * carrySteps bs, cfg (putBits f 1 (Counter.increment bs)) 1 2,
    le_rfl, increment_exact f bs hzero hend, halt _ _, rfl⟩

/-- A fixed controller for successive increments. It has four states regardless
of the number of completed increments; callers can use the loop boundaries.
This controller cycles indefinitely, so this definition makes no halting claim. -/
def cycleProgram : Program 1 4 0 := whileLoop program (fun _ => true)

def cycleTime : ℕ → List Bool → ℕ
  | 0, _ => 0
  | n + 1, bs => 2 * carrySteps bs + 2 + cycleTime n (Counter.increment bs)

/-- Every finite prefix of the cyclic controller implements the stated number
of increments, including both loop-control transitions per invocation. -/
theorem cycle_exact (n : ℕ) (f : ℤ → Fin 4) (bs : List Bool)
    (hzero : f 0 = separator) (hend : f (1 + bs.length) = blank) :
    run cycleProgram (cycleTime n bs) ((tapes f bs).start cycleProgram) =
      some ((tapes f (Counter.advance n bs)).start cycleProgram) := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih =>
    have hi := while_run_iteration program (fun _ => true) (tapes f bs) rfl
      (increment_exact f bs hzero hend) (halt _ _)
    change run cycleProgram (2 * carrySteps bs + 2) ((tapes f bs).start cycleProgram) =
      some ((tapes f (Counter.increment bs)).start cycleProgram) at hi
    simp only [cycleTime, Counter.advance, run_add, hi, Option.bind_some]
    exact ih (Counter.increment bs) (by simpa [Counter.increment_length] using hend)

/-- Amortization pays for the carry, head return, and fixed loop controller. -/
theorem cycle_potential (n : ℕ) (bs : List Bool) :
    cycleTime n bs + 2 * Counter.weight (Counter.advance n bs) ≤
      8 * n + 2 * Counter.weight bs := by
  induction n generalizing bs with
  | zero => simp [cycleTime, Counter.advance]
  | succ n ih =>
    have hstep := increment_potential bs
    have hrest := ih (Counter.increment bs)
    simp only [cycleTime, Counter.advance]
    omega

/-- Linear total tape-transition cost from arbitrary initial counter contents. -/
theorem cycle_amortized (n : ℕ) (bs : List Bool) :
    cycleTime n bs ≤ 8 * n + 2 * bs.length := by
  have hp := cycle_potential n bs
  have hw := Counter.weight_le_length bs
  omega

end CounterTape

end IntegerMultBounds.Machine
