import IntegerMultBounds.Machine.CountdownData
import IntegerMultBounds.Machine.BitTape
import IntegerMultBounds.Machine.WordTape
import IntegerMultBounds.Machine.Hoare

/-! Binary-counted transfer of an implicit-address stream. A five-state
three-tape machine decrements its little-endian clock before each copy. Carry
propagation and every head return are charged; no width scan occurs per symbol.
The initial clock and its local boundaries are explicit preconditions. -/

namespace IntegerMultBounds.Machine.CountedCopy

open CountdownData

/-- Only the clock tape moves during a ripple or return transition. -/
def clockAction (symbols : Fin 3 → Fin 4) (x : Fin 4) (move : Move) :
    Fin 3 → Fin 4 × Move := fun i => if i = 2 then (x,move) else (symbols i,.stay)

/-- States: decrement, successful return, underflow return, copy, halt. -/
def program : Program 3 5 0 where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s = 0 then
      if symbols 2 = bitSymbol false then
        some (0,clockAction symbols (bitSymbol true) .right)
      else if symbols 2 = bitSymbol true then
        some (1,clockAction symbols (bitSymbol false) .left)
      else if symbols 2 = blank then
        some (2,clockAction symbols blank .left)
      else none
    else if s = 1 ∨ s = 2 then
      if symbols 2 = separator then
        some ((if s = 1 then 3 else 4),clockAction symbols separator .right)
      else some (s,clockAction symbols (symbols 2) .left)
    else if s = 3 then
      some (0,fun i => if i = 2 then (symbols i,.stay) else (symbols 0,.right))
    else none

/-- The source and destination use arbitrary origins; the independent clock
head is exposed so all movement is part of the specification. -/
def cfg (source dest clock : ℤ → Fin 4) (p q r : ℤ) (s : Fin 5) : Config 3 5 0 where
  state := s
  head := fun i => if i = 0 then p else if i = 1 then q else r
  tape := fun i => if i = 0 then source else if i = 1 then dest else clock

private theorem clock_step (source dest clock : ℤ → Fin 4) (p q r : ℤ) (s t : Fin 5)
    (x : Fin 4) (move : Move)
    (h : program.transition s (fun i => (cfg source dest clock p q r s).tape i
      ((cfg source dest clock p q r s).head i)) =
      some (t,clockAction (fun i => (cfg source dest clock p q r s).tape i
        ((cfg source dest clock p q r s).head i)) x move)) :
    step program (cfg source dest clock p q r s) =
      some (cfg source dest (Function.update clock r x) p q (r + move.offset) t) := by
  simp only [step,cfg] at h ⊢
  rw [h]
  dsimp only
  congr 1
  congr 1
  · funext i
    fin_cases i <;> simp [clockAction,Move.offset]
  · funext i j
    fin_cases i <;> simp [clockAction,Function.update_apply,eq_comm] <;> intro h <;> subst j <;> rfl

private theorem step_zero (source dest clock : ℤ → Fin 4) (p q r : ℤ)
    (h : clock r = bitSymbol false) :
    step program (cfg source dest clock p q r 0) =
      some (cfg source dest (Function.update clock r (bitSymbol true)) p q (r+1) 0) := by
  apply clock_step (move := .right)
  simp [program,cfg,h]

private theorem step_one (source dest clock : ℤ → Fin 4) (p q r : ℤ)
    (h : clock r = bitSymbol true) :
    step program (cfg source dest clock p q r 0) =
      some (cfg source dest (Function.update clock r (bitSymbol false)) p q (r-1) 1) := by
  apply clock_step (move := .left)
  simp [program,cfg,h,bitSymbol]

private theorem step_blank (source dest clock : ℤ → Fin 4) (p q r : ℤ)
    (h : clock r = blank) :
    step program (cfg source dest clock p q r 0) =
      some (cfg source dest clock p q (r-1) 2) := by
  have hh := clock_step source dest clock p q r 0 2 blank .left (by
    simp [program,cfg,h,bitSymbol,blank])
  have he : Function.update clock r _ = clock := Function.update_eq_self_iff.mpr h.symm
  simpa only [Move.offset,sub_eq_add_neg,he] using hh

private theorem step_return (source dest clock : ℤ → Fin 4) (p q r : ℤ)
    (s : Fin 5) (hs : s = 1 ∨ s = 2) (h : clock r ≠ separator) :
    step program (cfg source dest clock p q r s) =
      some (cfg source dest clock p q (r-1) s) := by
  have hz : s ≠ 0 := by rcases hs with rfl | rfl <;> decide
  have hh := clock_step source dest clock p q r s s (clock r) .left (by
    simp [program,cfg,h,hs,hz])
  simpa only [Move.offset,sub_eq_add_neg,Function.update_eq_self] using hh

private theorem step_marker (source dest clock : ℤ → Fin 4) (p q r : ℤ)
    (s : Fin 5) (hs : s = 1 ∨ s = 2) (h : clock r = separator) :
    step program (cfg source dest clock p q r s) =
      some (cfg source dest clock p q (r+1) (if s = 1 then 3 else 4)) := by
  have hz : s ≠ 0 := by rcases hs with rfl | rfl <;> decide
  have hh := clock_step source dest clock p q r s (if s = 1 then 3 else 4) separator .right (by
    simp [program,cfg,h,hs,hz])
  have he : Function.update clock r _ = clock := Function.update_eq_self_iff.mpr h.symm
  simpa only [Move.offset,sub_eq_add_neg,he] using hh

private theorem step_copy (source dest clock : ℤ → Fin 4) (p q r : ℤ) :
    step program (cfg source dest clock p q r 3) =
      some (cfg source (Function.update dest q (source p)) clock (p+1) (q+1) r 0) := by
  simp only [step,program,cfg]
  norm_num
  constructor
  · funext i
    fin_cases i <;> simp [Move.offset]
  · funext i j
    fin_cases i <;> simp [Function.update_apply,eq_comm] <;> intro h <;> subst j <;> rfl

theorem halt (source dest clock : ℤ → Fin 4) (p q r : ℤ) :
    step program (cfg source dest clock p q r 4) = none := by
  simp [step,program,cfg]

/-- Exact ripple execution, retaining whether the decrement underflowed. -/
theorem borrow_run (source dest clock : ℤ → Fin 4) (p q r : ℤ) (bs : List Bool)
    (hend : clock (r+bs.length) = blank) :
    run program (borrowSteps bs) (cfg source dest (putBits clock r bs) p q r 0) =
      some (cfg source dest (putBits clock r (decrement bs)) p q
        (r + borrowSteps bs - 2) (if underflow bs then 2 else 1)) := by
  induction bs generalizing clock r with
  | nil =>
    simp only [List.length_nil,Nat.cast_zero,add_zero] at hend
    simpa [borrowSteps,decrement,underflow,putBits,run_one,
      show r+1-2 = r-1 by omega] using step_blank source dest clock p q r hend
  | cons b bs ih =>
    cases b with
    | true =>
      have hs := step_one source dest (putBits clock r (true::bs)) p q r
        (putBits_head clock r true bs)
      simpa [borrowSteps,decrement,underflow,run_one,putBits,Function.update_idem,
        show r+1-2 = r-1 by omega] using hs
    | false =>
      have hs := step_zero source dest (putBits clock r (false::bs)) p q r
        (putBits_head clock r false bs)
      have he : Function.update (putBits clock r (false::bs)) r (bitSymbol true) =
          putBits (Function.update clock r (bitSymbol true)) (r+1) bs := by
        rw [putBits_update_before clock (r+1) r (bitSymbol true) bs (by omega)]
        simp [putBits]
      rw [he] at hs
      have hend' : (Function.update clock r (bitSymbol true)) (r+1+bs.length) = blank := by
        rw [Function.update_of_ne (by omega)]
        simpa [List.length_cons,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using hend
      have hr := ih (Function.update clock r (bitSymbol true)) (r+1) hend'
      simp only [borrowSteps,decrement,underflow]
      rw [show borrowSteps bs+1 = 1+borrowSteps bs by omega,run_add]
      simp only [run_one,hs,Option.bind_some]
      convert hr using 1
      simp only [← putBits_cons,Nat.cast_add,Nat.cast_one,add_assoc]
      rfl

private theorem return_run (source dest clock : ℤ → Fin 4) (p q : ℤ)
    (s : Fin 5) (hs : s = 1 ∨ s = 2) (n : ℕ) (hzero : clock 0 = separator)
    (hno : ∀ j : ℕ, 1 ≤ j → j ≤ n → clock j ≠ separator) :
    run program (n+1) (cfg source dest clock p q n s) =
      some (cfg source dest clock p q 1 (if s = 1 then 3 else 4)) := by
  induction n with
  | zero => simpa only [Nat.cast_zero,run_one,zero_add] using
      step_marker source dest clock p q 0 s hs hzero
  | succ n ih =>
    have hstep : step program (cfg source dest clock p q ((n:ℤ)+1) s) =
        some (cfg source dest clock p q n s) := by
      simpa only [add_sub_cancel_right] using step_return source dest clock p q ((n:ℤ)+1) s hs
        (by exact_mod_cast hno (n+1) (by omega) le_rfl)
    simp only [Nat.cast_add,Nat.cast_one,run,hstep,Option.bind_some]
    exact ih (fun j hj hn => hno j hj (by omega))

/-- A complete decrement returns its clock head to the least significant bit.
Underflow reaches the true halt state; success reaches the one-symbol copy. -/
theorem decrement_exact (source dest clock : ℤ → Fin 4) (p q : ℤ) (bs : List Bool)
    (hzero : clock 0 = separator) (hend : clock (1+bs.length) = blank) :
    run program (2*borrowSteps bs) (cfg source dest (putBits clock 1 bs) p q 1 0) =
      some (cfg source dest (putBits clock 1 (decrement bs)) p q 1
        (if underflow bs then 4 else 3)) := by
  have hpos : 1 ≤ borrowSteps bs := (borrowSteps_bounds bs).1
  have hlen : borrowSteps bs ≤ bs.length+1 := (borrowSteps_bounds bs).2.1
  let n := borrowSteps bs-1
  have hn : n+1 = borrowSteps bs := by dsimp [n]; omega
  have hh : (1:ℤ)+borrowSteps bs-2 = (n:ℤ) := by omega
  have hmark : putBits clock 1 (decrement bs) 0 = separator := by
    rw [putBits_outside clock 1 0 _ (Or.inl (by omega)),hzero]
  have hno : ∀ j : ℕ, 1 ≤ j → j ≤ n → putBits clock 1 (decrement bs) j ≠ separator := by
    intro j hj hjn
    apply putBits_ne_separator
    · omega
    · rw [decrement_length]; omega
  rw [show 2*borrowSteps bs = borrowSteps bs+(n+1) by omega,run_add,borrow_run _ _ _ _ _ _ bs hend]
  simp only [Option.bind_some,hh]
  have hr := return_run source dest (putBits clock 1 (decrement bs)) p q
    (if underflow bs then 2 else 1) (by cases underflow bs <;> simp) n hmark hno
  cases hu : underflow bs <;> simpa [hu] using hr

/-- Exact cost of n successful copies followed by the terminating zero check. -/
def runtime (n : ℕ) (bs : List Bool) : ℕ :=
  totalCost n bs + 2*borrowSteps (advance n bs)

private theorem runtime_succ (n : ℕ) (bs : List Bool) :
    runtime (n+1) bs = 2*borrowSteps bs+1+runtime n (decrement bs) := by
  simp only [runtime,totalCost,advance]
  omega

/-- Transfer exactly the binary-specified number of symbols. Even blank data
symbols are copied: only the independent clock controls termination. The source
is preserved, and writing is confined to the destination word and clock bits. -/
theorem copy_run (source dest clock : ℤ → Fin 4) (p q : ℤ)
    (xs : List (Fin 4)) (bs : List Bool) (hcount : Counter.value bs = xs.length)
    (hzero : clock 0 = separator) (hend : clock (1+bs.length) = blank) :
    run program (runtime xs.length bs)
      (cfg (putWord source p xs) dest (putBits clock 1 bs) p q 1 0) =
      some (cfg (putWord source p xs) (putWord dest q xs)
        (putBits clock 1 (List.replicate bs.length true))
        (p+xs.length) (q+xs.length) 1 4) := by
  induction xs generalizing source dest p q bs with
  | nil =>
    have hv : Counter.value bs = 0 := hcount
    have hu := (underflow_eq_true_iff bs).2 hv
    have hd := decrement_exact source dest clock p q bs hzero hend
    simpa only [List.length_nil,runtime,totalCost,advance,zero_add,putWord,hu,
      ite_true,decrement_zero bs hv,Nat.cast_zero,add_zero] using hd
  | cons x xs ih =>
    have hv : 0 < Counter.value bs := by simp only [List.length_cons] at hcount; omega
    have hu := (underflow_eq_false_iff bs).2 hv
    have hd := decrement_exact (putWord source p (x::xs)) dest clock p q bs hzero hend
    simp only [hu,Bool.false_eq_true,ite_false] at hd
    have hcount' : Counter.value (decrement bs) = xs.length := by
      have hh := decrement_value bs hv
      simp only [List.length_cons] at hcount
      omega
    have hr := ih (Function.update source p x) (Function.update dest q x) (p+1) (q+1)
      (decrement bs) hcount' (by simpa only [decrement_length] using hend)
    simp only [List.length_cons,runtime_succ,run_add,hd,Option.bind_some,run_one,
      step_copy,putWord_head]
    simpa only [← putWord_cons,decrement_length,Nat.cast_add,Nat.cast_one,
      add_assoc,add_comm,add_left_comm] using hr

/-- Actual halting and an explicit linear tape-transition bound. Clock
preparation/reset and data-head repositioning remain separately charged calls. -/
theorem copy_exact (source dest clock : ℤ → Fin 4) (p q : ℤ)
    (xs : List (Fin 4)) (bs : List Bool) (hcount : Counter.value bs = xs.length)
    (hzero : clock 0 = separator) (hend : clock (1+bs.length) = blank) :
    runtime xs.length bs ≤ 5*xs.length+2*bs.length+2 ∧
    run program (runtime xs.length bs)
      (cfg (putWord source p xs) dest (putBits clock 1 bs) p q 1 0) =
      some (cfg (putWord source p xs) (putWord dest q xs)
        (putBits clock 1 (List.replicate bs.length true))
        (p+xs.length) (q+xs.length) 1 4) ∧
    step program (cfg (putWord source p xs) (putWord dest q xs)
      (putBits clock 1 (List.replicate bs.length true))
      (p+xs.length) (q+xs.length) 1 4) = none := by
  refine ⟨?_,copy_run source dest clock p q xs bs hcount hzero hend,halt _ _ _ _ _ _⟩
  simpa only [countdownCost,hcount,runtime] using countdown_cost bs

/-- Complete-tape Hoare contract; the source and destination need no sentinels,
and their backgrounds may contain arbitrary existing data. -/
theorem copy_hoare (source dest clock : ℤ → Fin 4) (p q : ℤ)
    (xs : List (Fin 4)) (bs : List Bool) (hcount : Counter.value bs = xs.length)
    (hzero : clock 0 = separator) (hend : clock (1+bs.length) = blank) :
    HoareTime program
      (fun v => v = (cfg (putWord source p xs) dest (putBits clock 1 bs) p q 1 0).tapes)
      (fun v => v = (cfg (putWord source p xs) (putWord dest q xs)
        (putBits clock 1 (List.replicate bs.length true))
        (p+xs.length) (q+xs.length) 1 4).tapes)
      (5*xs.length+2*bs.length+2) := by
  rintro v rfl
  obtain ⟨hb,hr,hh⟩ := copy_exact source dest clock p q xs bs hcount hzero hend
  exact ⟨runtime xs.length bs,_,hb,hr,hh,rfl⟩

/-- Canonical-sized clocks give the requested symbol count plus logarithmic
setup-size bound. The width hypothesis is about the supplied binary descriptor;
preparing that descriptor is not an uncharged action of this machine. -/
theorem runtime_le_log (xs : List (Fin 4)) (bs : List Bool)
    (hcount : Counter.value bs = xs.length)
    (hwidth : bs.length ≤ Nat.log2 (xs.length+1)+1) :
    runtime xs.length bs ≤ 5*xs.length+2*Nat.log2 (xs.length+1)+4 := by
  have hh := countdown_cost bs
  change runtime (Counter.value bs) bs ≤ 5*Counter.value bs+2*bs.length+2 at hh
  rw [hcount] at hh
  omega

end IntegerMultBounds.Machine.CountedCopy
