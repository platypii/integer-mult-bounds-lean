import IntegerMultBounds.Machine.RadixCounterData
import IntegerMultBounds.Machine.Loop
import IntegerMultBounds.Machine.Frame
import IntegerMultBounds.Machine.WordSegments

/-! Literal fixed-width radix increment with complete head returns. The program
and alphabet are fixed with q; width and prefix length are tape data. Arbitrary
framed payload tapes are untouched throughout each increment and every cycle. -/
namespace IntegerMultBounds.Machine.RadixCounter

open RadixDigits RadixCounterData
variable {q : ℕ} (hq : 2 ≤ q)

/-- Carry, rewind, halt. Overflow wraps the fixed-width word to all zeroes. -/
def program : Program 1 3 q where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols =>
    if state = 0 then
      match readDigit (symbols 0) with
      | some x => if h : x.val+1 < q then some (1,fun _ => (digitSymbol ⟨x.val+1,h⟩,.left))
        else some (0,fun _ => (digitSymbol (zeroDigit hq),.right))
      | none => if symbols 0 = blank then some (1,fun _ => (blank,.left)) else none
    else if state = 1 then
      if symbols 0 = separator then some (2,fun _ => (separator,.right))
      else some (1,fun i => (symbols i,.left))
    else none

def digitsTape (f : ℤ → Fin (q+4)) (p : ℤ) (xs : List (Fin q)) : ℤ → Fin (q+4) :=
  putWord f p (xs.map digitSymbol)

def cfg (f : ℤ → Fin (q+4)) (p : ℤ) (state : Fin 3) : Config 1 3 q :=
  ⟨state,fun _ => p,fun _ => f⟩

private theorem step_small (f : ℤ → Fin (q+4)) (p : ℤ) (x : Fin q) (hx : x.val+1 < q)
    (h : f p = digitSymbol x) :
    step (program hq) (cfg f p 0) =
      some (cfg (Function.update f p (digitSymbol ⟨x.val+1,hx⟩)) (p-1) 1) := by
  simp only [step,program,cfg,h,ite_true,readDigit_symbol,hx,↓reduceDIte]
  congr 1
  congr 1
  funext i z
  simp [Function.update_apply,eq_comm]

private theorem step_max (f : ℤ → Fin (q+4)) (p : ℤ) (x : Fin q) (hx : ¬x.val+1 < q)
    (h : f p = digitSymbol x) :
    step (program hq) (cfg f p 0) =
      some (cfg (Function.update f p (digitSymbol (zeroDigit hq))) (p+1) 0) := by
  simp only [step,program,cfg,h,ite_true,readDigit_symbol,hx,↓reduceDIte]
  congr 1
  congr 1
  funext i z
  simp [Function.update_apply,eq_comm]

private theorem step_blank (f : ℤ → Fin (q+4)) (p : ℤ) (h : f p = blank) :
    step (program hq) (cfg f p 0) = some (cfg f (p-1) 1) := by
  simp only [step,program,cfg,h,ite_true,readDigit_blank]
  congr 1
  congr 1
  funext i z
  by_cases hz : z = p
  · subst z; simp [h]
  · simp [hz]

private theorem step_rewind (f : ℤ → Fin (q+4)) (p : ℤ) (h : f p ≠ separator) :
    step (program hq) (cfg f p 1) = some (cfg f (p-1) 1) := by
  simp only [step,program,cfg,show (1 : Fin 3) ≠ 0 by decide,ite_false,ite_true,h]
  congr 1
  congr 1
  funext i z
  by_cases hz : z = p <;> simp [hz]

private theorem step_marker (f : ℤ → Fin (q+4)) (p : ℤ) (h : f p = separator) :
    step (program hq) (cfg f p 1) = some (cfg f (p+1) 2) := by
  simp only [step,program,cfg,show (1 : Fin 3) ≠ 0 by decide,ite_false,ite_true,h]
  congr 1
  congr 1
  funext i z
  by_cases hz : z = p
  · subst z; simp [h]
  · simp [hz]

private theorem halt (f : ℤ → Fin (q+4)) (p : ℤ) : step (program hq) (cfg f p 2) = none := by
  simp [step,program,cfg]

private theorem digitsTape_head (f : ℤ → Fin (q+4)) (p : ℤ) (x : Fin q) (xs : List (Fin q)) :
    digitsTape f p (x::xs) p = digitSymbol x := by simp [digitsTape,putWord]

private theorem digitsTape_outside (f : ℤ → Fin (q+4)) (p z : ℤ) (xs : List (Fin q))
    (h : z < p ∨ p+xs.length ≤ z) : digitsTape f p xs z = f z :=
  putWord_outside f p z _ (by simpa only [List.length_map] using h)

private theorem digitsTape_ne_separator (f : ℤ → Fin (q+4)) (p z : ℤ) (xs : List (Fin q))
    (hl : p ≤ z) (hu : z < p+xs.length) : digitsTape f p xs z ≠ separator := by
  have hz : z = p+((z-p).toNat : ℤ) := by omega
  have hi : (z-p).toNat < (xs.map digitSymbol).length := by simp only [List.length_map]; omega
  rw [digitsTape,hz,WordSegments.get _ _ _ _ hi,List.getElem_map]
  simp [digitSymbol,separator,Fin.ext_iff]

/-- Exact carry traversal, including the unique blank step on overflow. -/
theorem carry_run (f : ℤ → Fin (q+4)) (p : ℤ) (xs : List (Fin q))
    (hend : f (p+xs.length) = blank) :
    run (program hq) (carrySteps xs) (cfg (digitsTape f p xs) p 0) =
      some (cfg (digitsTape f p (increment hq xs)) (p+carrySteps xs-2) 1) := by
  induction xs generalizing f p with
  | nil =>
    simp only [List.length_nil,Nat.cast_zero,add_zero] at hend
    simpa [carrySteps,increment,digitsTape,putWord,run_one,show p+1-2 = p-1 by omega] using
      step_blank hq f p hend
  | cons x xs ih =>
    by_cases hx : x.val+1 < q
    · have hs := step_small hq (digitsTape f p (x::xs)) p x hx (digitsTape_head f p x xs)
      simpa [carrySteps,increment,hx,run_one,digitsTape,putWord,Function.update_idem,
        show p+1-2 = p-1 by omega] using hs
    · have hs := step_max hq (digitsTape f p (x::xs)) p x hx (digitsTape_head f p x xs)
      have he : Function.update (digitsTape f p (x::xs)) p (digitSymbol (zeroDigit hq)) =
          digitsTape (Function.update f p (digitSymbol (zeroDigit hq))) (p+1) xs :=
        putWord_replace_head f p (digitSymbol x) _ (xs.map digitSymbol)
      rw [he] at hs
      have hend' : (Function.update f p (digitSymbol (zeroDigit hq))) (p+1+xs.length) = blank := by
        rw [Function.update_of_ne (by omega)]
        simpa [List.length_cons,add_assoc,add_comm,add_left_comm] using hend
      have hr := ih (Function.update f p (digitSymbol (zeroDigit hq))) (p+1) hend'
      simp only [carrySteps,increment,hx,↓reduceIte,↓reduceDIte]
      rw [show carrySteps xs+1 = 1+carrySteps xs by omega,run_add]
      simp only [run_one,hs,Option.bind_some]
      simpa only [digitsTape,List.map_cons,← putWord_cons,Nat.cast_add,Nat.cast_one,add_assoc] using hr

private theorem rewind_run (f : ℤ → Fin (q+4)) (n : ℕ) (hzero : f 0 = separator)
    (hno : ∀ j : ℕ, 1 ≤ j → j ≤ n → f j ≠ separator) :
    run (program hq) (n+1) (cfg f n 1) = some (cfg f 1 2) := by
  induction n with
  | zero => simpa only [Nat.cast_zero,run_one,zero_add] using step_marker hq f 0 hzero
  | succ n ih =>
    have hs : step (program hq) (cfg f ((n:ℤ)+1) 1) = some (cfg f n 1) := by
      simpa only [add_sub_cancel_right] using
        step_rewind hq f ((n:ℤ)+1) (by exact_mod_cast hno (n+1) (by omega) le_rfl)
    simp only [Nat.cast_add,Nat.cast_one,run,hs,Option.bind_some]
    exact ih (fun j hj hn => hno j hj (by omega))

/-- A successful call returns its head to one even when all digits overflow. -/
theorem increment_exact (f : ℤ → Fin (q+4)) (xs : List (Fin q))
    (hzero : f 0 = separator) (hend : f (1+xs.length) = blank) :
    run (program hq) (2*carrySteps xs) (cfg (digitsTape f 1 xs) 1 0) =
      some (cfg (digitsTape f 1 (increment hq xs)) 1 2) := by
  obtain ⟨hpos,hlen⟩ := carrySteps_bounds xs
  let n := carrySteps xs-1
  have hn : n+1 = carrySteps xs := by dsimp [n]; omega
  have hh : (1:ℤ)+carrySteps xs-2 = (n:ℤ) := by omega
  have hmark : digitsTape f 1 (increment hq xs) 0 = separator := by
    rw [digitsTape_outside f 1 0 _ (Or.inl (by omega)),hzero]
  have hno : ∀ j : ℕ, 1 ≤ j → j ≤ n → digitsTape f 1 (increment hq xs) j ≠ separator := by
    intro j hj hjn
    apply digitsTape_ne_separator
    · omega
    · rw [increment_length]; omega
  rw [show 2*carrySteps xs = carrySteps xs+(n+1) by omega,run_add,carry_run hq f 1 xs hend]
  simp only [Option.bind_some,hh]
  exact rewind_run hq _ n hmark hno

def tapes (f : ℤ → Fin (q+4)) (xs : List (Fin q)) : Tapes 1 q :=
  ⟨fun _ => 1,fun _ => digitsTape f 1 xs⟩

theorem increment_hoare (f : ℤ → Fin (q+4)) (xs : List (Fin q))
    (hzero : f 0 = separator) (hend : f (1+xs.length) = blank) :
    HoareTime (program hq) (fun v => v = tapes f xs)
      (fun v => v = tapes f (increment hq xs)) (2*carrySteps xs) := by
  rintro v rfl
  exact ⟨2*carrySteps xs,cfg (digitsTape f 1 (increment hq xs)) 1 2,
    le_rfl,increment_exact hq f xs hzero hend,halt hq _ _,rfl⟩

/-- Finite-prefix execution of a four-state cyclic controller. It intentionally
does not halt: an enclosing prefix scheduler chooses the number of iterations. -/
def cycleProgram : Program 1 4 q := whileLoop (program hq) (fun _ => true)

theorem cycle_exact (n : ℕ) (f : ℤ → Fin (q+4)) (xs : List (Fin q))
    (hzero : f 0 = separator) (hend : f (1+xs.length) = blank) :
    run (cycleProgram hq) (cycleTime hq n xs) ((tapes f xs).start (cycleProgram hq)) =
      some ((tapes f (advance hq n xs)).start (cycleProgram hq)) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    have hi := while_run_iteration (program hq) (fun _ => true) (tapes f xs) rfl
      (increment_exact hq f xs hzero hend) (halt hq _ _)
    change run (cycleProgram hq) (2*carrySteps xs+2) ((tapes f xs).start (cycleProgram hq)) =
      some ((tapes f (increment hq xs)).start (cycleProgram hq)) at hi
    simp only [cycleTime,advance,run_add,hi,Option.bind_some]
    exact ih (increment hq xs) (by simpa [increment_length] using hend)

/-- Arbitrary framed payloads are retained exactly, with the same amortized
transition bound. No payload or spectator tape head moves during this counter. -/
theorem framed_cycle {t : ℕ} (frame : Tapes t q) (n : ℕ)
    (f : ℤ → Fin (q+4)) (xs : List (Fin q))
    (hzero : f 0 = separator) (hend : f (1+xs.length) = blank) :
    ∃ k, k ≤ 6*n+2*xs.length ∧
      run (extend (cycleProgram hq) t) k (((tapes f xs).append frame).start (extend (cycleProgram hq) t)) =
        some (((tapes f (advance hq n xs)).append frame).start (extend (cycleProgram hq) t)) := by
  refine ⟨cycleTime hq n xs,cycle_amortized hq n xs,?_⟩
  exact extend_run (cycleProgram hq) frame (cycle_exact hq n f xs hzero hend)

/-- Every radix control value is exposed at the loop boundary, followed by an
exact reset to zero after a full Q-state traversal. -/
theorem enumeration (b n : ℕ) (hn : n < q^b) :
    value (advance hq n (zeros hq b)) = n ∧
      advance hq (q^b) (zeros hq b) = zeros hq b ∧
      cycleTime hq (q^b) (zeros hq b) ≤ 6*q^b+2*b := by
  refine ⟨enumerate_value hq b n hn,full_cycle hq b,?_⟩
  simpa only [zeros_length] using cycle_amortized hq (q^b) (zeros hq b)

/-- One complete field traversal restores the exact counter and arbitrary
framed payload, within eight transitions per enumerated control value. -/
theorem full_cycle_framed {t : ℕ} (frame : Tapes t q) (b : ℕ)
    (f : ℤ → Fin (q+4)) (hzero : f 0 = separator) (hend : f (1+b) = blank) :
    ∃ k, k ≤ 8*q^b ∧
      run (extend (cycleProgram hq) t) k
        (((tapes f (zeros hq b)).append frame).start (extend (cycleProgram hq) t)) =
        some (((tapes f (zeros hq b)).append frame).start (extend (cycleProgram hq) t)) := by
  refine ⟨cycleTime hq (q^b) (zeros hq b),full_cycle_cost hq b,?_⟩
  have h := extend_run (cycleProgram hq) frame
    (cycle_exact hq (q^b) f (zeros hq b) hzero (by simpa only [zeros_length] using hend))
  rw [full_cycle] at h
  exact h

end IntegerMultBounds.Machine.RadixCounter
