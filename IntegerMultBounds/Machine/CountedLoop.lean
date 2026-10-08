import IntegerMultBounds.Machine.CountedCopy
import IntegerMultBounds.Machine.Frame

/-! A fixed finite binary-counted body loop. The final tape is the dedicated
mutable clock. CountedCopy's literal ripple/return transitions drive the loop;
a successful decrement enters the body, and its actual halt returns to the
clock. One terminal underflow halts the whole machine. Clock preparation and
cleanup are explicit caller work, and no descriptor is rescanned per body call. -/

namespace IntegerMultBounds.Machine.CountedLoop

open CountdownData
variable {t q : ℕ}

/-- The body occupies the first tapes; the last tape holds the independent
clock. Five clock states and the body's existing finite states suffice. -/
def program (M : Program t q 0) : Program (t+1) (q+5) 0 where
  tapes_pos := by omega
  start := Fin.natAdd q 0
  transition := fun state symbols => Fin.addCases
    (fun s => match M.transition s (fun i => symbols (Fin.castAdd 1 i)) with
      | none => some (Fin.natAdd q 0,fun i => (symbols i,.stay))
      | some (s',act) => some (Fin.castAdd 5 s',Fin.addCases act
          (fun i => (symbols (Fin.natAdd t i),.stay))))
    (fun s => if s = 3 then some (Fin.castAdd 5 M.start,fun i => (symbols i,.stay)) else
      (CountedCopy.program.transition s (fun i => if i = 2 then symbols (Fin.natAdd t 0) else blank)).map
        (fun (s',act) => (Fin.natAdd q s',Fin.addCases
          (fun i => (symbols (Fin.castAdd 1 i),.stay)) (fun _ => act 2)))) state

/-- Complete tapes at a loop boundary, with arbitrary background outside the
binary clock segment and its specified sentinel/end blank. -/
def bank (v : Tapes t 0) (clock : ℤ → Fin 4) (bs : List Bool) : Tapes (t+1) 0 :=
  v.append ⟨fun _ => 1,fun _ => putBits clock 1 bs⟩

private def cfg (_M : Program t q 0) (v : Tapes t 0) (clock : ℤ → Fin 4)
    (head : ℤ) (state : Fin 5) : Config (t+1) (q+5) 0 :=
  ⟨Fin.natAdd q state,(v.append ⟨fun _ => head,fun _ => clock⟩).head,
    (v.append ⟨fun _ => head,fun _ => clock⟩).tape⟩

private theorem clock_step (M : Program t q 0) (v : Tapes t 0)
    (clock : ℤ → Fin 4) (r : ℤ) (s u : Fin 5) (hs : s ≠ 3) (x : Fin 4) (move : Move)
    (h : CountedCopy.program.transition s (fun i => if i = 2 then clock r else blank) =
      some (u,CountedCopy.clockAction (fun i => if i = 2 then clock r else blank) x move)) :
    step (program M) (cfg M v clock r s) =
      some (cfg M v (Function.update clock r x) (r+move.offset) u) := by
  simp only [step,program,cfg,Tapes.append,Fin.addCases_right,Fin.addCases_left,hs,ite_false]
  rw [h]
  dsimp only [Option.map_some]
  congr 1
  congr 1
  · funext i
    induction i using Fin.addCases with
    | left i => simp [CountedCopy.clockAction,Move.offset]
    | right i => fin_cases i; simp [CountedCopy.clockAction]
  · funext i j
    induction i using Fin.addCases with
    | left i =>
      simp only [Fin.addCases_left]
      by_cases hj : j = v.head i
      · subst j; simp
      · simp [hj]
    | right i => fin_cases i; simp [CountedCopy.clockAction,Function.update_apply]

private theorem step_zero (M : Program t q 0) (v : Tapes t 0) (clock : ℤ → Fin 4) (r : ℤ)
    (h : clock r = bitSymbol false) :
    step (program M) (cfg M v clock r 0) =
      some (cfg M v (Function.update clock r (bitSymbol true)) (r+1) 0) := by
  apply clock_step (move := .right) (hs := by decide)
  simp [CountedCopy.program,h]

private theorem step_one (M : Program t q 0) (v : Tapes t 0) (clock : ℤ → Fin 4) (r : ℤ)
    (h : clock r = bitSymbol true) :
    step (program M) (cfg M v clock r 0) =
      some (cfg M v (Function.update clock r (bitSymbol false)) (r-1) 1) := by
  apply clock_step (move := .left) (hs := by decide)
  simp [CountedCopy.program,h,bitSymbol]

private theorem step_blank (M : Program t q 0) (v : Tapes t 0) (clock : ℤ → Fin 4) (r : ℤ)
    (h : clock r = blank) :
    step (program M) (cfg M v clock r 0) = some (cfg M v clock (r-1) 2) := by
  have hh := clock_step M v clock r 0 2 (by decide) blank .left (by
    simp [CountedCopy.program,h,bitSymbol,blank])
  have he : Function.update clock r blank = clock := Function.update_eq_self_iff.mpr h.symm
  simpa only [Move.offset,sub_eq_add_neg,he] using hh

private theorem step_return (M : Program t q 0) (v : Tapes t 0) (clock : ℤ → Fin 4) (r : ℤ)
    (s : Fin 5) (hs : s = 1 ∨ s = 2) (h : clock r ≠ separator) :
    step (program M) (cfg M v clock r s) = some (cfg M v clock (r-1) s) := by
  have hz : s ≠ 0 := by rcases hs with rfl | rfl <;> decide
  have hthree : s ≠ 3 := by rcases hs with rfl | rfl <;> decide
  have hh := clock_step M v clock r s s hthree (clock r) .left (by
    simp [CountedCopy.program,h,hs,hz])
  simpa only [Move.offset,sub_eq_add_neg,Function.update_eq_self] using hh

private theorem step_marker (M : Program t q 0) (v : Tapes t 0) (clock : ℤ → Fin 4) (r : ℤ)
    (s : Fin 5) (hs : s = 1 ∨ s = 2) (h : clock r = separator) :
    step (program M) (cfg M v clock r s) =
      some (cfg M v clock (r+1) (if s = 1 then 3 else 4)) := by
  have hz : s ≠ 0 := by rcases hs with rfl | rfl <;> decide
  have hthree : s ≠ 3 := by rcases hs with rfl | rfl <;> decide
  have hh := clock_step M v clock r s (if s = 1 then 3 else 4) hthree separator .right (by
    simp [CountedCopy.program,h,hs,hz])
  have he : Function.update clock r separator = clock := Function.update_eq_self_iff.mpr h.symm
  simpa only [Move.offset,he] using hh

private theorem halt (M : Program t q 0) (v : Tapes t 0) (clock : ℤ → Fin 4) (r : ℤ) :
    step (program M) (cfg M v clock r 4) = none := by
  simp [step,program,cfg,Tapes.append,CountedCopy.program]

/-- The literal clock scan preserves every body tape and head. -/
private theorem borrow_run (M : Program t q 0) (v : Tapes t 0) (clock : ℤ → Fin 4)
    (r : ℤ) (bs : List Bool) (hend : clock (r+bs.length) = blank) :
    run (program M) (borrowSteps bs) (cfg M v (putBits clock r bs) r 0) =
      some (cfg M v (putBits clock r (decrement bs))
        (r+borrowSteps bs-2) (if underflow bs then 2 else 1)) := by
  induction bs generalizing clock r with
  | nil =>
    simp only [List.length_nil,Nat.cast_zero,add_zero] at hend
    simpa [borrowSteps,decrement,underflow,putBits,run_one,show r+1-2 = r-1 by omega] using
      step_blank M v clock r hend
  | cons b bs ih =>
    cases b with
    | true =>
      have hs := step_one M v (putBits clock r (true::bs)) r (putBits_head clock r true bs)
      simpa [borrowSteps,decrement,underflow,run_one,putBits,Function.update_idem,
        show r+1-2 = r-1 by omega] using hs
    | false =>
      have hs := step_zero M v (putBits clock r (false::bs)) r (putBits_head clock r false bs)
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

private theorem return_run (M : Program t q 0) (v : Tapes t 0) (clock : ℤ → Fin 4)
    (s : Fin 5) (hs : s = 1 ∨ s = 2) (n : ℕ) (hzero : clock 0 = separator)
    (hno : ∀ j : ℕ, 1 ≤ j → j ≤ n → clock j ≠ separator) :
    run (program M) (n+1) (cfg M v clock n s) =
      some (cfg M v clock 1 (if s = 1 then 3 else 4)) := by
  induction n with
  | zero => simpa only [Nat.cast_zero,run_one,zero_add] using step_marker M v clock 0 s hs hzero
  | succ n ih =>
    have hstep : step (program M) (cfg M v clock ((n:ℤ)+1) s) = some (cfg M v clock n s) := by
      simpa only [add_sub_cancel_right] using step_return M v clock ((n:ℤ)+1) s hs
        (by exact_mod_cast hno (n+1) (by omega) le_rfl)
    simp only [Nat.cast_add,Nat.cast_one,run,hstep,Option.bind_some]
    exact ih (fun j hj hn => hno j hj (by omega))

private theorem decrement_exact (M : Program t q 0) (v : Tapes t 0) (clock : ℤ → Fin 4)
    (bs : List Bool) (hzero : clock 0 = separator) (hend : clock (1+bs.length) = blank) :
    run (program M) (2*borrowSteps bs) (cfg M v (putBits clock 1 bs) 1 0) =
      some (cfg M v (putBits clock 1 (decrement bs)) 1 (if underflow bs then 4 else 3)) := by
  have hpos := (borrowSteps_bounds bs).1
  have hlen := (borrowSteps_bounds bs).2.1
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
  rw [show 2*borrowSteps bs = borrowSteps bs+(n+1) by omega,run_add,borrow_run M v clock 1 bs hend]
  simp only [Option.bind_some,hh]
  have hr := return_run M v (putBits clock 1 (decrement bs))
    (if underflow bs then 2 else 1) (by cases underflow bs <;> simp) n hmark hno
  cases hu : underflow bs <;> simpa [hu] using hr

private def bodyCfg (c : Config t q 0) (clock : ℤ → Fin 4) (r : ℤ) :
    Config (t+1) (q+5) 0 :=
  (c.extend (⟨fun _ => r,fun _ => clock⟩ : Tapes 1 0)).mapState (Fin.castAdd 5)

private theorem body_step (M : Program t q 0) (clock : ℤ → Fin 4) (r : ℤ)
    {c d : Config t q 0} (h : step M c = some d) :
    step (program M) (bodyCfg c clock r) = some (bodyCfg d clock r) := by
  unfold step at h ⊢
  simp only [program,bodyCfg,Config.mapState,Config.extend,Config.tapes,Tapes.append,Fin.addCases_left]
  cases ht : M.transition c.state (fun i => c.tape i (c.head i)) with
  | none => simp [ht] at h
  | some result =>
    rcases result with ⟨state,action⟩
    simp only [ht] at h ⊢
    cases h
    congr 1
    congr 1
    · funext i
      induction i using Fin.addCases with
      | left i => simp
      | right i => simp [Move.offset]
    · funext i j
      induction i using Fin.addCases with
      | left i => simp
      | right i =>
        simp only [Fin.addCases_right]
        by_cases hj : j = r
        · subst j; simp
        · simp [hj]

private theorem body_return (M : Program t q 0) (clock : ℤ → Fin 4) (r : ℤ)
    {c : Config t q 0} (h : step M c = none) :
    step (program M) (bodyCfg c clock r) = some (cfg M c.tapes clock r 0) := by
  unfold step at h ⊢
  simp only [program,bodyCfg,Config.mapState,Config.extend,Config.tapes,Tapes.append,Fin.addCases_left]
  cases ht : M.transition c.state (fun i => c.tape i (c.head i)) with
  | some result => simp [ht] at h
  | none =>
    simp only [Move.offset,add_zero,cfg,Tapes.append]
    congr 1
    congr 1
    funext i j
    by_cases hj : j = Fin.addCases c.head (fun _ => r) i
    · subst j; simp
    · simp [hj]

private theorem body_enter (M : Program t q 0) (v : Tapes t 0) (clock : ℤ → Fin 4) (r : ℤ) :
    step (program M) (cfg M v clock r 3) = some (bodyCfg (v.start M) clock r) := by
  simp only [step,program,cfg,Tapes.append,Fin.addCases_right,ite_true,bodyCfg,
    Config.mapState,Config.extend,Config.tapes,Tapes.start,Move.offset,add_zero]
  congr 1
  congr 1
  funext i j
  by_cases hj : j = Fin.addCases v.head (fun _ => r) i
  · subst j; simp
  · simp [hj]

private theorem body_run (M : Program t q 0) (clock : ℤ → Fin 4) (r : ℤ)
    (v : Tapes t 0) {c : Config t q 0} {n : ℕ}
    (hr : run M n (v.start M) = some c) (hh : step M c = none) :
    run (program M) (n+2) (cfg M v clock r 3) = some (cfg M c.tapes clock r 0) := by
  have hs := run_simulation M (program M) (fun c => bodyCfg c clock r)
    (fun _ _ h => body_step M clock r h) hr
  rw [show n+2 = 1+n+1 by omega,run_add,run_add]
  simp only [run_one,body_enter,Option.bind_some,hs,body_return M clock r hh]

/-- All countdown transitions and both body joins, including the sole terminal
underflow. Its value is independent of the body's actual execution costs. -/
def clockTime (n : ℕ) (bs : List Bool) : ℕ := CountedCopy.runtime n bs+n

private theorem clockTime_succ (n : ℕ) (bs : List Bool) :
    clockTime (n+1) bs = 2*borrowSteps bs+2+clockTime n (decrement bs) := by
  simp only [clockTime,CountedCopy.runtime,totalCost,advance]
  omega

private theorem run_chain (M : Program t q 0) (clock : ℤ → Fin 4)
    (hzero : clock 0 = separator) (n : ℕ) (v : ℕ → Tapes t 0) (cost : ℕ → ℕ)
    (bs : List Bool) (hcount : Counter.value bs = n) (hend : clock (1+bs.length) = blank)
    (hbody : ∀ i < n, HoareTime M (fun w => w = v i) (fun w => w = v (i+1)) (cost i)) :
    ∃ k, k ≤ (∑ i ∈ Finset.range n, cost i)+clockTime n bs ∧
      run (program M) k (cfg M (v 0) (putBits clock 1 bs) 1 0) =
        some (cfg M (v n) (putBits clock 1 (List.replicate bs.length true)) 1 4) := by
  induction n generalizing v cost bs with
  | zero =>
    have hu := (underflow_eq_true_iff bs).2 hcount
    have hr := decrement_exact M (v 0) clock bs hzero hend
    refine ⟨2*borrowSteps bs,?_,?_⟩
    · simp [clockTime,CountedCopy.runtime,totalCost,advance]
    · simpa only [hu,ite_true,decrement_zero bs hcount] using hr
  | succ n ih =>
    have hv : 0 < Counter.value bs := by omega
    have hu := (underflow_eq_false_iff bs).2 hv
    have hnext : Counter.value (decrement bs) = n := by
      have hh := decrement_value bs hv
      omega
    obtain ⟨k,c,hk,hr,hh,hc⟩ := hbody 0 (by omega) (v 0) rfl
    have hb := body_run M (putBits clock 1 (decrement bs)) 1 (v 0) hr hh
    rw [hc] at hb
    obtain ⟨l,hl,hs⟩ := ih (fun i => v (i+1)) (fun i => cost (i+1)) (decrement bs) hnext
      (by simpa only [decrement_length] using hend) (fun i hi => hbody (i+1) (by omega))
    have hd := decrement_exact M (v 0) clock bs hzero hend
    simp only [hu,Bool.false_eq_true,ite_false] at hd
    refine ⟨2*borrowSteps bs+(k+2)+l,?_,?_⟩
    · rw [clockTime_succ,Finset.sum_range_succ']
      omega
    · rw [run_add,run_add,hd]
      simp only [Option.bind_some,hb]
      simpa only [decrement_length] using hs

/-- The loop's clock overhead is amortized over all N bodies, rather than
charging a full-width subtraction or zero test at each iteration. -/
theorem clockTime_le (bs : List Bool) :
    clockTime (Counter.value bs) bs ≤ 6*Counter.value bs+2*bs.length+2 := by
  have hh := countdown_cost bs
  change CountedCopy.runtime (Counter.value bs) bs ≤ 5*Counter.value bs+2*bs.length+2 at hh
  dsimp only [clockTime]
  omega

/-- Actual finite-machine execution of an arbitrary Hoare chain. The time bound
retains the sum of the individual body costs, which may differ by iteration. -/
theorem loop_exact (M : Program t q 0) (clock : ℤ → Fin 4) (bs : List Bool)
    (n : ℕ) (v : ℕ → Tapes t 0) (cost : ℕ → ℕ)
    (hcount : Counter.value bs = n) (hzero : clock 0 = separator)
    (hend : clock (1+bs.length) = blank)
    (hbody : ∀ i < n, HoareTime M (fun w => w = v i) (fun w => w = v (i+1)) (cost i)) :
    ∃ k c, k ≤ (∑ i ∈ Finset.range n, cost i)+6*n+2*bs.length+2 ∧
      run (program M) k ((bank (v 0) clock bs).start (program M)) = some c ∧
      step (program M) c = none ∧
      c.tapes = bank (v n) clock (List.replicate bs.length true) := by
  obtain ⟨k,hk,hr⟩ := run_chain M clock hzero n v cost bs hcount hend hbody
  have hb := clockTime_le bs
  rw [hcount] at hb
  exact ⟨k,_,by omega,hr,halt M (v n) _ 1,rfl⟩

/-- Composition-ready contract for the literal counted loop. The body tapes
follow the supplied chain; only the independent clock is additionally modified. -/
theorem loop_hoare (M : Program t q 0) (clock : ℤ → Fin 4) (bs : List Bool)
    (n : ℕ) (v : ℕ → Tapes t 0) (cost : ℕ → ℕ)
    (hcount : Counter.value bs = n) (hzero : clock 0 = separator)
    (hend : clock (1+bs.length) = blank)
    (hbody : ∀ i < n, HoareTime M (fun w => w = v i) (fun w => w = v (i+1)) (cost i)) :
    HoareTime (program M)
      (fun w => w = bank (v 0) clock bs)
      (fun w => w = bank (v n) clock (List.replicate bs.length true))
      ((∑ i ∈ Finset.range n, cost i)+6*n+2*bs.length+2) := by
  rintro w rfl
  exact loop_exact M clock bs n v cost hcount hzero hend hbody

end IntegerMultBounds.Machine.CountedLoop
