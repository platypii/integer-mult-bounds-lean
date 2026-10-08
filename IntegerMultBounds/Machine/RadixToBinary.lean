import IntegerMultBounds.Machine.RadixToBinaryData
import IntegerMultBounds.Machine.GrowingCounter
import IntegerMultBounds.Machine.Alphabet
import IntegerMultBounds.Machine.Placement
import IntegerMultBounds.Machine.WordSegments
import IntegerMultBounds.Machine.CountedCopyReuse
import IntegerMultBounds.Machine.Copy
import IntegerMultBounds.Machine.Rewind

/-! Literal radix countdown with a binary growing-counter body. The source
radix digits are finite symbols; no unit-cost arithmetic is used by the machine. -/
namespace IntegerMultBounds.Machine.RadixToBinary

open RadixDigits RadixToBinaryData
variable {q t s : ℕ} (hq : 2 ≤ q)

private def predDigit (x : Fin q) : Fin q := ⟨x.val-1,lt_of_le_of_lt (Nat.sub_le _ _) x.isLt⟩

private def clockTransition (state : Fin 5) (symbol : Fin (q+4)) :
    Option (Fin 5 × Fin (q+4) × Move) :=
  if state = 0 then
    match readDigit symbol with
    | some x => if x.val = 0 then some (0,digitSymbol (lastDigit hq),.right)
      else some (1,digitSymbol (predDigit x),.left)
    | none => if symbol = blank then some (2,blank,.left) else none
  else if state = 1 ∨ state = 2 then
    if symbol = separator then some ((if state = 1 then 3 else 4),separator,.right)
    else some (state,symbol,.left)
  else none

/-- Five radix-clock states plus the fixed body's states. -/
def loopProgram (M : Program t s q) : Program (t+1) (s+5) q where
  tapes_pos := by omega
  start := Fin.natAdd s 0
  transition := fun state symbols => Fin.addCases
    (fun st => match M.transition st (fun i => symbols (Fin.castAdd 1 i)) with
      | none => some (Fin.natAdd s 0,fun i => (symbols i,.stay))
      | some (st',act) => some (Fin.castAdd 5 st',Fin.addCases act
          (fun i => (symbols (Fin.natAdd t i),.stay))))
    (fun st => if st = 3 then some (Fin.castAdd 5 M.start,fun i => (symbols i,.stay)) else
      (clockTransition hq st (symbols (Fin.natAdd t 0))).map
        (fun (st',x,move) => (Fin.natAdd s st',Fin.addCases
          (fun i => (symbols (Fin.castAdd 1 i),.stay)) (fun _ => (x,move))))) state

private def putRadix (f : ℤ → Fin (q+4)) (r : ℤ) (xs : List (Fin q)) : ℤ → Fin (q+4) :=
  putWord f r (xs.map digitSymbol)

private theorem putRadix_head (f : ℤ → Fin (q+4)) (r : ℤ) (x : Fin q) (xs : List (Fin q)) :
    putRadix f r (x::xs) r = digitSymbol x := by simp [putRadix,putWord]

private theorem putRadix_outside (f : ℤ → Fin (q+4)) (r z : ℤ) (xs : List (Fin q))
    (h : z < r ∨ r+xs.length ≤ z) : putRadix f r xs z = f z :=
  putWord_outside f r z _ (by simpa only [List.length_map] using h)

private theorem putRadix_ne_separator (f : ℤ → Fin (q+4)) (r z : ℤ) (xs : List (Fin q))
    (hl : r ≤ z) (hu : z < r+xs.length) : putRadix f r xs z ≠ separator := by
  have hz : z = r+((z-r).toNat : ℤ) := by omega
  have hi : (z-r).toNat < (xs.map digitSymbol).length := by simp only [List.length_map]; omega
  rw [putRadix,hz,WordSegments.get _ _ _ _ hi,List.getElem_map]
  simp [digitSymbol,separator,Fin.ext_iff]

/-- Arbitrary body bank plus an independent radix clock with local sentinel. -/
def bank (v : Tapes t q) (clock : ℤ → Fin (q+4)) (xs : List (Fin q)) : Tapes (t+1) q :=
  v.append ⟨fun _ => 1,fun _ => putRadix clock 1 xs⟩

private def cfg (_M : Program t s q) (v : Tapes t q) (clock : ℤ → Fin (q+4))
    (head : ℤ) (state : Fin 5) : Config (t+1) (s+5) q :=
  ⟨Fin.natAdd s state,(v.append ⟨fun _ => head,fun _ => clock⟩).head,
    (v.append ⟨fun _ => head,fun _ => clock⟩).tape⟩

private theorem clock_step (M : Program t s q) (v : Tapes t q)
    (clock : ℤ → Fin (q+4)) (r : ℤ) (st u : Fin 5) (hs : st ≠ 3) (x : Fin (q+4)) (move : Move)
    (h : clockTransition hq st (clock r) = some (u,x,move)) :
    step (loopProgram hq M) (cfg M v clock r st) =
      some (cfg M v (Function.update clock r x) (r+move.offset) u) := by
  simp only [step,loopProgram,cfg,Tapes.append,Fin.addCases_right,Fin.addCases_left,hs,ite_false]
  rw [h]
  dsimp only [Option.map_some]
  congr 1
  congr 1
  · funext i
    induction i using Fin.addCases with
    | left i => simp [Move.offset]
    | right i => fin_cases i; simp
  · funext i z
    induction i using Fin.addCases with
    | left i =>
      simp only [Fin.addCases_left]
      by_cases hz : z = v.head i <;> simp [hz]
    | right i => fin_cases i; simp [Function.update_apply]

private theorem step_zero (M : Program t s q) (v : Tapes t q) (clock : ℤ → Fin (q+4)) (r : ℤ)
    (x : Fin q) (hx : x.val = 0) (h : clock r = digitSymbol x) :
    step (loopProgram hq M) (cfg M v clock r 0) =
      some (cfg M v (Function.update clock r (digitSymbol (lastDigit hq))) (r+1) 0) := by
  apply clock_step hq (move := .right) (hs := by decide)
  simp [clockTransition,h,hx]

private theorem step_nonzero (M : Program t s q) (v : Tapes t q) (clock : ℤ → Fin (q+4)) (r : ℤ)
    (x : Fin q) (hx : x.val ≠ 0) (h : clock r = digitSymbol x) :
    step (loopProgram hq M) (cfg M v clock r 0) =
      some (cfg M v (Function.update clock r (digitSymbol (predDigit x))) (r-1) 1) := by
  apply clock_step hq (move := .left) (hs := by decide)
  simp [clockTransition,h,hx]

private theorem step_blank (M : Program t s q) (v : Tapes t q) (clock : ℤ → Fin (q+4)) (r : ℤ)
    (h : clock r = blank) :
    step (loopProgram hq M) (cfg M v clock r 0) = some (cfg M v clock (r-1) 2) := by
  have hh := clock_step hq M v clock r 0 2 (by decide) blank .left (by simp [clockTransition,h])
  have he : Function.update clock r blank = clock := Function.update_eq_self_iff.mpr h.symm
  simpa only [Move.offset,sub_eq_add_neg,he] using hh

private theorem step_return (M : Program t s q) (v : Tapes t q) (clock : ℤ → Fin (q+4)) (r : ℤ)
    (st : Fin 5) (hs : st = 1 ∨ st = 2) (h : clock r ≠ separator) :
    step (loopProgram hq M) (cfg M v clock r st) = some (cfg M v clock (r-1) st) := by
  have hz : st ≠ 0 := by rcases hs with rfl | rfl <;> decide
  have hthree : st ≠ 3 := by rcases hs with rfl | rfl <;> decide
  have hh := clock_step hq M v clock r st st hthree (clock r) .left (by simp [clockTransition,h,hs,hz])
  simpa only [Move.offset,sub_eq_add_neg,Function.update_eq_self] using hh

private theorem step_marker (M : Program t s q) (v : Tapes t q) (clock : ℤ → Fin (q+4)) (r : ℤ)
    (st : Fin 5) (hs : st = 1 ∨ st = 2) (h : clock r = separator) :
    step (loopProgram hq M) (cfg M v clock r st) =
      some (cfg M v clock (r+1) (if st = 1 then 3 else 4)) := by
  have hz : st ≠ 0 := by rcases hs with rfl | rfl <;> decide
  have hthree : st ≠ 3 := by rcases hs with rfl | rfl <;> decide
  have hh := clock_step hq M v clock r st (if st = 1 then 3 else 4) hthree separator .right (by
    simp [clockTransition,h,hs,hz])
  have he : Function.update clock r separator = clock := Function.update_eq_self_iff.mpr h.symm
  simpa only [Move.offset,he] using hh

private theorem halt (M : Program t s q) (v : Tapes t q) (clock : ℤ → Fin (q+4)) (r : ℤ) :
    step (loopProgram hq M) (cfg M v clock r 4) = none := by
  simp [step,loopProgram,cfg,Tapes.append,clockTransition]

private theorem borrow_run (M : Program t s q) (v : Tapes t q) (clock : ℤ → Fin (q+4))
    (r : ℤ) (xs : List (Fin q)) (hend : clock (r+xs.length) = blank) :
    run (loopProgram hq M) (borrowSteps xs) (cfg M v (putRadix clock r xs) r 0) =
      some (cfg M v (putRadix clock r (decrement hq xs))
        (r+borrowSteps xs-2) (if underflow xs then 2 else 1)) := by
  induction xs generalizing clock r with
  | nil =>
    simp only [List.length_nil,Nat.cast_zero,add_zero] at hend
    simpa [borrowSteps,decrement,underflow,putRadix,putWord,run_one,show r+1-2 = r-1 by omega] using
      step_blank hq M v clock r hend
  | cons x xs ih =>
    by_cases hx : x.val = 0
    · have hs := step_zero hq M v (putRadix clock r (x::xs)) r x hx (putRadix_head clock r x xs)
      have he : Function.update (putRadix clock r (x::xs)) r (digitSymbol (lastDigit hq)) =
          putRadix (Function.update clock r (digitSymbol (lastDigit hq))) (r+1) xs := by
        exact putWord_replace_head clock r (digitSymbol x) _ (xs.map digitSymbol)
      rw [he] at hs
      have hend' : (Function.update clock r (digitSymbol (lastDigit hq))) (r+1+xs.length) = blank := by
        rw [Function.update_of_ne (by omega)]
        simpa [List.length_cons,add_assoc,add_comm,add_left_comm] using hend
      have hr := ih (Function.update clock r (digitSymbol (lastDigit hq))) (r+1) hend'
      simp only [borrowSteps,decrement,underflow,hx,↓reduceIte,↓reduceDIte]
      rw [show borrowSteps xs+1 = 1+borrowSteps xs by omega,run_add]
      simp only [run_one,hs,Option.bind_some]
      convert hr using 1
      simp only [putRadix,List.map_cons,← putWord_cons,Nat.cast_add,Nat.cast_one,add_assoc]
    · have hs := step_nonzero hq M v (putRadix clock r (x::xs)) r x hx (putRadix_head clock r x xs)
      simpa [borrowSteps,decrement,underflow,hx,run_one,putRadix,putWord,predDigit,Function.update_idem,
        show r+1-2 = r-1 by omega] using hs

private theorem return_run (M : Program t s q) (v : Tapes t q) (clock : ℤ → Fin (q+4))
    (st : Fin 5) (hs : st = 1 ∨ st = 2) (n : ℕ) (hzero : clock 0 = separator)
    (hno : ∀ j : ℕ, 1 ≤ j → j ≤ n → clock j ≠ separator) :
    run (loopProgram hq M) (n+1) (cfg M v clock n st) =
      some (cfg M v clock 1 (if st = 1 then 3 else 4)) := by
  induction n with
  | zero => simpa only [Nat.cast_zero,run_one,zero_add] using step_marker hq M v clock 0 st hs hzero
  | succ n ih =>
    have hstep : step (loopProgram hq M) (cfg M v clock ((n:ℤ)+1) st) = some (cfg M v clock n st) := by
      simpa only [add_sub_cancel_right] using step_return hq M v clock ((n:ℤ)+1) st hs
        (by exact_mod_cast hno (n+1) (by omega) le_rfl)
    simp only [Nat.cast_add,Nat.cast_one,run,hstep,Option.bind_some]
    exact ih (fun j hj hn => hno j hj (by omega))

private theorem decrement_exact (M : Program t s q) (v : Tapes t q) (clock : ℤ → Fin (q+4))
    (xs : List (Fin q)) (hzero : clock 0 = separator) (hend : clock (1+xs.length) = blank) :
    run (loopProgram hq M) (2*borrowSteps xs) (cfg M v (putRadix clock 1 xs) 1 0) =
      some (cfg M v (putRadix clock 1 (decrement hq xs)) 1 (if underflow xs then 4 else 3)) := by
  have hpos := (borrowSteps_bounds xs).1
  have hlen := (borrowSteps_bounds xs).2
  let n := borrowSteps xs-1
  have hn : n+1 = borrowSteps xs := by dsimp [n]; omega
  have hh : (1:ℤ)+borrowSteps xs-2 = (n:ℤ) := by omega
  have hmark : putRadix clock 1 (decrement hq xs) 0 = separator := by
    rw [putRadix_outside clock 1 0 _ (Or.inl (by omega)),hzero]
  have hno : ∀ j : ℕ, 1 ≤ j → j ≤ n → putRadix clock 1 (decrement hq xs) j ≠ separator := by
    intro j hj hjn
    apply putRadix_ne_separator
    · omega
    · rw [decrement_length]; omega
  rw [show 2*borrowSteps xs = borrowSteps xs+(n+1) by omega,run_add,borrow_run hq M v clock 1 xs hend]
  simp only [Option.bind_some,hh]
  have hr := return_run hq M v (putRadix clock 1 (decrement hq xs))
    (if underflow xs then 2 else 1) (by cases underflow xs <;> simp) n hmark hno
  cases hu : underflow xs <;> simpa [hu] using hr
private def bodyCfg (c : Config t s q) (clock : ℤ → Fin (q+4)) (r : ℤ) :
    Config (t+1) (s+5) q :=
  (c.extend (⟨fun _ => r,fun _ => clock⟩ : Tapes 1 q)).mapState (Fin.castAdd 5)

private theorem body_step (M : Program t s q) (clock : ℤ → Fin (q+4)) (r : ℤ)
    {c d : Config t s q} (h : step M c = some d) :
    step (loopProgram hq M) (bodyCfg c clock r) = some (bodyCfg d clock r) := by
  unfold step at h ⊢
  simp only [loopProgram,bodyCfg,Config.mapState,Config.extend,Config.tapes,Tapes.append,Fin.addCases_left]
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

private theorem body_return (M : Program t s q) (clock : ℤ → Fin (q+4)) (r : ℤ)
    {c : Config t s q} (h : step M c = none) :
    step (loopProgram hq M) (bodyCfg c clock r) = some (cfg M c.tapes clock r 0) := by
  unfold step at h ⊢
  simp only [loopProgram,bodyCfg,Config.mapState,Config.extend,Config.tapes,Tapes.append,Fin.addCases_left]
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

private theorem body_enter (M : Program t s q) (v : Tapes t q) (clock : ℤ → Fin (q+4)) (r : ℤ) :
    step (loopProgram hq M) (cfg M v clock r 3) = some (bodyCfg (v.start M) clock r) := by
  simp only [step,loopProgram,cfg,Tapes.append,Fin.addCases_right,ite_true,bodyCfg,
    Config.mapState,Config.extend,Config.tapes,Tapes.start,Move.offset,add_zero]
  congr 1
  congr 1
  funext i j
  by_cases hj : j = Fin.addCases v.head (fun _ => r) i
  · subst j; simp
  · simp [hj]

private theorem body_run (M : Program t s q) (clock : ℤ → Fin (q+4)) (r : ℤ)
    (v : Tapes t q) {c : Config t s q} {n : ℕ}
    (hr : run M n (v.start M) = some c) (hh : step M c = none) :
    run (loopProgram hq M) (n+2) (cfg M v clock r 3) = some (cfg M c.tapes clock r 0) := by
  have hs := run_simulation M (loopProgram hq M) (fun c => bodyCfg c clock r)
    (fun _ _ h => body_step hq M clock r h) hr
  rw [show n+2 = 1+n+1 by omega,run_add,run_add]
  simp only [run_one,body_enter,Option.bind_some,hs,body_return hq M clock r hh]



/-- Exact successful-clock overhead followed by one terminal underflow. -/
def clockTime (n : ℕ) (xs : List (Fin q)) : ℕ :=
  totalCost hq n xs+2*borrowSteps (advance hq n xs)

private theorem clockTime_succ (n : ℕ) (xs : List (Fin q)) :
    clockTime hq (n+1) xs = 2*borrowSteps xs+2+clockTime hq n (decrement hq xs) := by
  simp only [clockTime,totalCost,advance]
  omega

private theorem run_chain (M : Program t s q) (clock : ℤ → Fin (q+4))
    (hzero : clock 0 = separator) (n : ℕ) (v : ℕ → Tapes t q) (cost : ℕ → ℕ)
    (bs : List (Fin q)) (hcount : value bs = n) (hend : clock (1+bs.length) = blank)
    (hbody : ∀ i < n, HoareTime M (fun w => w = v i) (fun w => w = v (i+1)) (cost i)) :
    ∃ k, k ≤ (∑ i ∈ Finset.range n, cost i)+clockTime hq n bs ∧
      run (loopProgram hq M) k (cfg M (v 0) (putRadix clock 1 bs) 1 0) =
        some (cfg M (v n) (putRadix clock 1 (List.replicate bs.length (lastDigit hq))) 1 4) := by
  induction n generalizing v cost bs with
  | zero =>
    have hu := (underflow_eq_true_iff hq bs).2 hcount
    have hr := decrement_exact hq M (v 0) clock bs hzero hend
    refine ⟨2*borrowSteps bs,?_,?_⟩
    · simp [clockTime,totalCost,advance]
    · simpa only [hu,ite_true,decrement_zero hq bs hcount] using hr
  | succ n ih =>
    have hv : 0 < value bs := by omega
    have hu := (underflow_eq_false_iff hq bs).2 hv
    have hnext : value (decrement hq bs) = n := by
      have hh := decrement_value hq bs hv
      omega
    obtain ⟨k,c,hk,hr,hh,hc⟩ := hbody 0 (by omega) (v 0) rfl
    have hb := body_run hq M (putRadix clock 1 (decrement hq bs)) 1 (v 0) hr hh
    rw [hc] at hb
    obtain ⟨l,hl,hs⟩ := ih (fun i => v (i+1)) (fun i => cost (i+1)) (decrement hq bs) hnext
      (by simpa only [decrement_length] using hend) (fun i hi => hbody (i+1) (by omega))
    have hd := decrement_exact hq M (v 0) clock bs hzero hend
    simp only [hu,Bool.false_eq_true,ite_false] at hd
    refine ⟨2*borrowSteps bs+(k+2)+l,?_,?_⟩
    · rw [clockTime_succ,Finset.sum_range_succ']
      omega
    · rw [run_add,run_add,hd]
      simp only [Option.bind_some,hb]
      simpa only [decrement_length] using hs


/-- Radix countdown overhead is uniform in q and linear in value plus width. -/
theorem clockTime_le (xs : List (Fin q)) :
    clockTime hq (value xs) xs ≤ 6*value xs+2*xs.length+2 := by
  have hp := total_potential hq (value xs) xs le_rfl
  have hz := zeroWeight_of_zero hq _ (countdown_zero hq xs)
  have hs := borrowSteps_of_zero hq _ (countdown_zero hq xs)
  have hw := zeroWeight_le_length xs
  rw [advance_length] at hz hs
  dsimp only [clockTime]
  omega

/-- General radix-controlled literal execution, preserving all body frames. -/
theorem loop_hoare (M : Program t s q) (clock : ℤ → Fin (q+4)) (xs : List (Fin q))
    (n : ℕ) (v : ℕ → Tapes t q) (cost : ℕ → ℕ)
    (hcount : value xs = n) (hzero : clock 0 = separator)
    (hend : clock (1+xs.length) = blank)
    (hbody : ∀ i < n, HoareTime M (fun w => w = v i) (fun w => w = v (i+1)) (cost i)) :
    HoareTime (loopProgram hq M) (fun w => w = bank (v 0) clock xs)
      (fun w => w = bank (v n) clock (List.replicate xs.length (lastDigit hq)))
      ((∑ i ∈ Finset.range n, cost i)+6*n+2*xs.length+2) := by
  rintro w rfl
  obtain ⟨k,hk,hr⟩ := run_chain hq M clock hzero n v cost xs hcount hend hbody
  have hb := clockTime_le hq xs
  rw [hcount] at hb
  exact ⟨k,_,by omega,hr,halt hq M (v n) _ 1,rfl⟩

omit hq in
def binaryEncoding : Alphabet.Encoding 0 q where
  encode := fun x => ⟨x.val,Nat.lt_of_lt_of_le x.isLt (Nat.le_add_left 4 q)⟩
  decode := fun x => if h : x.val < 4 then ⟨x.val,h⟩ else blank
  decode_encode := by intro x; simp [x.isLt]

/-- The binary incrementer operates only on its own widened four-symbol tape. -/
def incrementProgram (q : ℕ) : Program 1 3 q :=
  Alphabet.program (binaryEncoding (q := q)) GrowingCounter.program

def binaryState (q : ℕ) (bits : List Bool) : Tapes 1 q :=
  Alphabet.mapTapes (binaryEncoding (q := q)) (GrowingCounter.tapes CountedCopyReuse.empty bits)

private theorem increment_hoare (bits : List Bool) :
    HoareTime (incrementProgram q) (fun v => v = binaryState q bits)
      (fun v => v = binaryState q (GrowingCounterData.increment bits))
      (2*GrowingCounterData.carrySteps bits) := by
  have h := GrowingCounter.increment_hoare CountedCopyReuse.empty bits
    (by simp [CountedCopyReuse.empty])
    (by simp [CountedCopyReuse.empty,show (1:ℤ)+bits.length ≠ 0 by omega])
  apply (Alphabet.map_hoare (binaryEncoding (q := q)) h).consequence _ _ le_rfl
  · intro v hv
    exact ⟨_,rfl,hv⟩
  · rintro v ⟨w,rfl,hv⟩
    exact hv

private theorem cost_sum (n : ℕ) (bits : List Bool) :
    (∑ i ∈ Finset.range n, 2*GrowingCounterData.carrySteps (GrowingCounterData.advance i bits)) =
      GrowingCounterData.totalCost n bits := by
  induction n generalizing bits with
  | zero => simp [GrowingCounterData.totalCost]
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [GrowingCounterData.advance,ih,GrowingCounterData.totalCost]
    omega

/-- Core conversion consumes a prepared private radix clock and grows a
canonical binary output without touching any source tape. -/
def coreProgram : Program 2 8 q := loopProgram hq (incrementProgram q)

theorem core_hoare (clock : ℤ → Fin (q+4)) (xs : List (Fin q))
    (hzero : clock 0 = separator) (hend : clock (1+xs.length) = blank) :
    HoareTime (coreProgram hq) (fun v => v = bank (binaryState q []) clock xs)
      (fun v => v = bank (binaryState q (RadixToBinaryData.output xs)) clock
        (List.replicate xs.length (lastDigit hq))) (10*value xs+2*xs.length+2) := by
  have hbody (i : ℕ) (_ : i < value xs) : HoareTime (incrementProgram q)
      (fun v => v = binaryState q (GrowingCounterData.advance i []))
      (fun v => v = binaryState q (GrowingCounterData.advance (i+1) []))
      (2*GrowingCounterData.carrySteps (GrowingCounterData.advance i [])) := by
    have hh := increment_hoare (q := q) (GrowingCounterData.advance i [])
    have hi (n : ℕ) (bits : List Bool) :
        GrowingCounterData.increment (GrowingCounterData.advance n bits) =
          GrowingCounterData.advance (n+1) bits := by
      induction n generalizing bits with
      | zero => rfl
      | succ n ih => exact ih (GrowingCounterData.increment bits)
    simpa only [hi] using hh
  have h := loop_hoare hq (incrementProgram q) clock xs (value xs)
    (fun i => binaryState q (GrowingCounterData.advance i []))
    (fun i => 2*GrowingCounterData.carrySteps (GrowingCounterData.advance i [])) rfl hzero hend hbody
  rw [cost_sum] at h
  have hc := GrowingCounterData.amortized_cost (value xs) []
  simp only [List.length_nil,Nat.mul_zero,Nat.add_zero] at hc
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)


private def empty : ℤ → Fin (q+4) := fun z => if z = 0 then separator else blank

private def triple (out clock source : ℤ → Fin (q+4)) (p r u : ℤ) : Tapes 3 q :=
  ⟨![p,r,u],![out,clock,source]⟩

private def markedRadix (xs : List (Fin q)) := putRadix empty 1 xs

def sourceWord (xs : List (Fin q)) := putRadix (fun _ => blank) 1 xs

/-- The radix input begins at cell one; its initial head is on the blank cell
zero. Both work tapes are completely blank, including their marker positions. -/
def input (xs : List (Fin q)) : Tapes 3 q :=
  triple (fun _ => blank) (fun _ => blank) (sourceWord xs) 0 0 0

private def prepared (bits : List Bool) (clock source : List (Fin q)) (r u : ℤ) : Tapes 3 q :=
  triple ((binaryState q bits).tape 0) (markedRadix clock) (markedRadix source) 1 r u

private def initializeProgram : Program 3 2 q where
  tapes_pos := by decide
  start := 0
  transition := fun state _ => if state = 0 then some (1,fun _ => (separator,.right)) else none

private theorem empty_update : Function.update (fun _ : ℤ => (blank : Fin (q+4))) 0 separator = empty := by
  funext z
  simp [Function.update_apply,empty]

private theorem binary_nil : (binaryState q []).tape 0 = empty := by
  funext z
  by_cases hz : z = 0 <;> simp [binaryState,Alphabet.mapTapes,binaryEncoding,GrowingCounter.tapes,
    CountedCopyReuse.empty,putBits,empty,hz,separator,blank]

private theorem markedRadix_marker (xs : List (Fin q)) : markedRadix xs 0 = separator := by
  rw [markedRadix,putRadix_outside _ _ _ _ (Or.inl (by omega))]
  rfl

private theorem markedRadix_end (xs : List (Fin q)) : markedRadix xs (1+xs.length) = blank := by
  rw [markedRadix,putRadix_outside _ _ _ _ (Or.inr (by omega))]
  simp [empty,show (1:ℤ)+xs.length ≠ 0 by omega]

private theorem markedRadix_ne_marker (xs : List (Fin q)) (z : ℤ) (hz : 0 < z) : markedRadix xs z ≠ separator := by
  by_cases hi : z < 1+xs.length
  · exact putRadix_ne_separator _ _ _ _ (by omega) hi
  · rw [markedRadix,putRadix_outside _ _ _ _ (Or.inr (by omega))]
    simp [empty,show z ≠ 0 by omega,blank,separator]

private theorem initialize_hoare (xs : List (Fin q)) :
    HoareTime (initializeProgram (q := q)) (fun v => v = input xs)
      (fun v => v = prepared [] [] xs 1 1) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(prepared [] [] xs 1 1).head,(prepared [] [] xs 1 1).tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,initializeProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i
      · funext z
        simp [input,prepared,triple,binary_nil,empty]
      · funext z
        simp [input,prepared,triple,markedRadix,putRadix,putWord,empty]
      · have he : Function.update (putWord (fun _ => blank) 1 (xs.map digitSymbol)) 0 separator =
            markedRadix xs := by
          rw [← putWord_update_before _ _ _ _ _ (by omega),empty_update]
          rfl
        funext z
        simpa [input,prepared,triple,sourceWord,putRadix,Function.update_apply] using congrFun he z
  · simp [step,initializeProgram]

private def copyPlacement : Fin (2+1) ≃ Fin 3 := Equiv.swap 0 2

private def copyProgram : Program 3 1 q := Placement.placed (Copy.program blank false) copyPlacement

private theorem copy_hoare (xs : List (Fin q)) :
    HoareTime (copyProgram (q := q)) (fun v => v = prepared [] [] xs 1 1)
      (fun v => v = prepared [] xs xs (1+xs.length) (1+xs.length)) xs.length := by
  have h := Copy.copy_hoare blank false empty empty 1 1 (xs.map digitSymbol)
    (by intro x hx; obtain ⟨d,_,rfl⟩ := List.mem_map.mp hx; simp [digitSymbol,blank,Fin.ext_iff])
    (by simp only [List.length_map]; simp [empty,show (1:ℤ)+xs.length ≠ 0 by omega])
  have ha : Placement.active copyPlacement (prepared [] [] xs 1 1) =
      Copy.tapes (putWord empty 1 (xs.map digitSymbol)) empty 1 1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hh := Placement.hoare_at h copyPlacement (prepared [] [] xs 1 1) ha
  apply hh.consequence (fun _ h => h) _ (by simp)
  rintro v ⟨w,rfl,rfl⟩
  have hid : (xs.map digitSymbol).map (Copy.retained false) = xs.map digitSymbol := by
    simp [Copy.retained]
  rw [hid]
  have he : Placement.extra copyPlacement (prepared [] [] xs 1 1) =
      Placement.extra copyPlacement (prepared [] xs xs (1+xs.length) (1+xs.length)) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hf : Placement.active copyPlacement (prepared [] xs xs (1+xs.length) (1+xs.length)) =
      Copy.tapes (putWord empty 1 (xs.map digitSymbol)) (putWord empty 1 (xs.map digitSymbol))
        (1+(xs.map digitSymbol).length) (1+(xs.map digitSymbol).length) := by
    simp only [List.length_map]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [Placement.replace,he]
  simpa only [hf] using Placement.view copyPlacement (prepared [] xs xs (1+xs.length) (1+xs.length))

/-- Rewind the source and its exact copy together, preserving the binary output. -/
private def resetProgram : Program 3 2 q where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols => if state = 0 then
    if symbols 1 = separator then some (1,fun i => (symbols i,if i = 0 then .stay else .right))
    else some (0,fun i => (symbols i,if i = 0 then .stay else .left)) else none

private def resetCfg (xs : List (Fin q)) (r : ℤ) (st : Fin 2) : Config 3 2 q :=
  ⟨st,(prepared [] xs xs r r).head,(prepared [] xs xs r r).tape⟩

private theorem reset_step (xs : List (Fin q)) (r : ℤ) (hr : 0 < r) :
    step resetProgram (resetCfg xs r 0) = some (resetCfg xs (r-1) 0) := by
  have hn := markedRadix_ne_marker xs r hr
  simp only [step,resetProgram,resetCfg,prepared,triple]
  simp only [Matrix.cons_val_one,Matrix.cons_val_zero,ite_true,hn,ite_false]
  congr 1
  congr 1
  · funext i
    fin_cases i <;> simp [Move.offset,sub_eq_add_neg]
  · funext i z
    by_cases hz : z = (![1,r,r] : Fin 3 → ℤ) i <;> simp [hz]

private theorem reset_scan (xs : List (Fin q)) (n : ℕ) :
    run resetProgram n (resetCfg xs n 0) = some (resetCfg xs 0 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run,Nat.cast_add,Nat.cast_one]
    rw [reset_step xs (n+1) (by omega)]
    simpa using ih

private theorem reset_hoare (xs : List (Fin q)) :
    HoareTime (resetProgram (q := q))
      (fun v => v = prepared [] xs xs (1+xs.length) (1+xs.length))
      (fun v => v = prepared [] xs xs 1 1) (xs.length+2) := by
  rintro v rfl
  have hr := reset_scan xs (xs.length+1)
  have hcast : ((xs.length+1 : ℕ) : ℤ) = 1+xs.length := by omega
  rw [hcast] at hr
  refine ⟨xs.length+2,resetCfg xs 1 1,le_rfl,?_,?_,rfl⟩
  · rw [show xs.length+2 = (xs.length+1)+1 by omega,run_add]
    change (run resetProgram (xs.length+1) (resetCfg xs (1+xs.length) 0)).bind _ = _
    rw [hr]
    simp only [Option.bind_some,run_one,step,resetProgram,resetCfg,prepared,triple]
    simp only [Matrix.cons_val_one,Matrix.cons_val_zero,markedRadix_marker,ite_true]
    congr 1
    congr 1
    · funext i
      fin_cases i <;> rfl
    · funext i z
      by_cases hz : z = (![1,0,0] : Fin 3 → ℤ) i <;> simp [hz]
  · simp [step,resetProgram,resetCfg]


private def oneTape (f : ℤ → Fin (q+4)) (r : ℤ) : Tapes 1 q := ⟨fun _ => r,fun _ => f⟩

private def clearProgram : Program 1 1 q where
  tapes_pos := by decide
  start := 0
  transition := fun _ symbols => if symbols 0 = blank then none
    else some (0,fun _ => (blank,.right))

private def clearCfg (f : ℤ → Fin (q+4)) (p : ℤ) : Config 1 1 q := ⟨0,fun _ => p,fun _ => f⟩

private theorem clear_step (f : ℤ → Fin (q+4)) (p : ℤ) (h : f p ≠ blank) :
    step clearProgram (clearCfg f p) = some (clearCfg (Function.update f p blank) (p+1)) := by
  simp only [step,clearProgram,clearCfg,h,↓reduceIte,Move.offset]
  congr 1
  congr 1
  funext i z
  simp [Function.update_apply,eq_comm]

private theorem clear_run (f : ℤ → Fin (q+4)) (p : ℤ) (xs : List (Fin (q+4)))
    (hxs : ∀ x ∈ xs, x ≠ blank) :
    run clearProgram xs.length (clearCfg (putWord f p xs) p) =
      some (clearCfg (putWord f p (xs.map (fun _ => blank))) (p+xs.length)) := by
  induction xs generalizing f p with
  | nil => simp [run,putWord]
  | cons x xs ih =>
    have hs := clear_step (putWord f p (x::xs)) p
      (by rw [putWord_head]; exact hxs x (by simp))
    rw [putWord_replace_head] at hs
    simp only [List.length_cons,run,hs,Option.bind_some]
    have hr := ih (Function.update f p blank) (p+1) (fun y hy => hxs y (by simp [hy]))
    simpa only [List.map_cons,← putWord_cons,Nat.cast_add,Nat.cast_one,
      add_assoc,add_comm,add_left_comm] using hr

private theorem putWord_blank_eq (f : ℤ → Fin (q+4)) (p : ℤ) (xs : List (Fin (q+4)))
    (hf : ∀ z : ℤ, p ≤ z → f z = blank) :
    putWord f p (xs.map (fun _ => blank)) = f := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,putWord,ih (p+1) (fun z hz => hf z (by omega))]
    exact Function.update_eq_self_iff.mpr (hf p le_rfl).symm

private theorem clear_hoare (xs : List (Fin q)) :
    HoareTime (clearProgram (q := q)) (fun v => v = oneTape (markedRadix xs) 1)
      (fun v => v = oneTape empty (1+xs.length)) xs.length := by
  have hxs : ∀ x ∈ xs.map digitSymbol, x ≠ (blank : Fin (q+4)) := by
    intro x hx
    obtain ⟨d,_,rfl⟩ := List.mem_map.mp hx
    simp [digitSymbol,blank,Fin.ext_iff]
  have hr := clear_run empty 1 (xs.map digitSymbol) hxs
  have he : putWord empty 1 ((xs.map digitSymbol).map (fun _ => blank)) = empty :=
    putWord_blank_eq empty 1 _ (by intro z hz; simp [empty,show z ≠ 0 by omega])
  rw [he,List.length_map] at hr
  rintro v rfl
  refine ⟨xs.length,clearCfg empty (1+xs.length),le_rfl,hr,?_,rfl⟩
  simp [step,clearProgram,clearCfg,empty,show (1:ℤ)+xs.length ≠ 0 by omega]

private def clockPlacement : Fin (1+2) ≃ Fin 3 := Equiv.swap 0 1

private def atClock {k : ℕ} (M : Program 1 k q) : Program 3 k q := Placement.placed M clockPlacement

private def clockBank (bits : List Bool) (xs : List (Fin q)) (f : ℤ → Fin (q+4)) (r : ℤ) : Tapes 3 q :=
  triple ((binaryState q bits).tape 0) f (markedRadix xs) 1 r 1

private theorem clock_hoare {k n : ℕ} (M : Program 1 k q) (bits : List Bool) (xs : List (Fin q))
    (f g : ℤ → Fin (q+4)) (r u : ℤ)
    (h : HoareTime M (fun v => v = oneTape f r) (fun v => v = oneTape g u) n) :
    HoareTime (atClock M) (fun v => v = clockBank bits xs f r)
      (fun v => v = clockBank bits xs g u) n := by
  have ha : Placement.active clockPlacement (clockBank bits xs f r) = oneTape f r := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have he : Placement.extra clockPlacement (clockBank bits xs f r) =
      Placement.extra clockPlacement (clockBank bits xs g u) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hf : Placement.active clockPlacement (clockBank bits xs g u) = oneTape g u := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  apply (Placement.hoare_at h clockPlacement (clockBank bits xs f r) ha).consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [Placement.replace,he]
  simpa only [hf] using Placement.view clockPlacement (clockBank bits xs g u)

private theorem rewind_empty_hoare (n : ℕ) :
    HoareTime (Rewind.program (separator : Fin (q+4)))
      (fun v => v = oneTape empty n) (fun v => v = oneTape empty 0) n := by
  have h := Rewind.rewind_hoare (separator : Fin (q+4)) empty n n
    (by intro j hj; simp [empty,show (n:ℤ)-j ≠ 0 by omega,blank,separator])
    (by simp [empty])
  simpa only [sub_self,Rewind.cfg,Config.tapes,oneTape] using h

/-- Final binary descriptor, completely erased work tape, and original radix
source restored exactly, including its blank marker cell and original head. -/
def output (xs : List (Fin q)) : Tapes 3 q :=
  triple ((binaryState q (RadixToBinaryData.output xs)).tape 0) (fun _ => blank) (sourceWord xs) 1 0 0

private def unmarkProgram : Program 3 3 q where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols =>
    if state = 0 then some (1,fun i => (symbols i,if i = 2 then .left else .stay))
    else if state = 1 then some (2,fun i => (if i = 0 then symbols i else blank,.stay))
    else none

private theorem source_unmark (xs : List (Fin q)) :
    Function.update (markedRadix xs) 0 blank = sourceWord xs := by
  rw [markedRadix,putRadix,← putWord_update_before _ _ _ _ _ (by omega)]
  have he : Function.update (empty : ℤ → Fin (q+4)) 0 blank = fun _ => blank := by
    funext z
    by_cases hz : z = 0 <;> simp [hz,empty]
  rw [he]
  rfl

private theorem unmark_hoare (xs : List (Fin q)) :
    HoareTime (unmarkProgram (q := q))
      (fun v => v = clockBank (RadixToBinaryData.output xs) xs empty 0)
      (fun v => v = output xs) 2 := by
  let middle := triple ((binaryState q (RadixToBinaryData.output xs)).tape 0) empty (markedRadix xs) 1 0 0
  have hs : step unmarkProgram ((clockBank (RadixToBinaryData.output xs) xs empty 0).start unmarkProgram) =
      some (⟨1,middle.head,middle.tape⟩ : Config 3 3 q) := by
    simp only [step,unmarkProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i
      fin_cases i <;> rfl
    · funext i z
      by_cases hz : z = (clockBank (RadixToBinaryData.output xs) xs empty 0).head i
      · simp [hz,middle,clockBank,triple]
      · simp only [clockBank,triple] at hz
        simp [hz,middle,clockBank,triple]
  rintro v rfl
  refine ⟨2,⟨2,(output xs).head,(output xs).tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_add unmarkProgram 1 1,run_one,hs]
    simp only [Option.bind_some,run_one,step,unmarkProgram,show (1 : Fin 3) ≠ 0 by decide,ite_false,ite_true]
    congr 1
    congr 1
    · funext i
      fin_cases i <;> rfl
    · funext i z
      fin_cases i
      · by_cases hz : z = 1 <;> simp [middle,output,triple,hz]
      · by_cases hz : z = 0 <;> simp [middle,output,triple,empty,hz]
      · simpa [middle,output,triple,Function.update_apply] using congrFun (source_unmark xs) z
  · simp [step,unmarkProgram]

private def cleanupProgram : Program 3 5 q :=
  seq (seq (atClock clearProgram) (atClock (Rewind.program separator))) unmarkProgram

private theorem cleanup_hoare (xs : List (Fin q)) :
    HoareTime (cleanupProgram (q := q))
      (fun v => v = prepared (RadixToBinaryData.output xs)
        (List.replicate xs.length (lastDigit hq)) xs 1 1)
      (fun v => v = output xs) (2*xs.length+5) := by
  have hc := clock_hoare clearProgram (RadixToBinaryData.output xs) xs _ _ _ _
    (clear_hoare (List.replicate xs.length (lastDigit hq)))
  simp only [List.length_replicate] at hc
  have hr := clock_hoare (Rewind.program separator) (RadixToBinaryData.output xs) xs _ _ _ _
    (rewind_empty_hoare (q := q) (xs.length+1))
  have hcast : ((xs.length+1 : ℕ) : ℤ) = 1+xs.length := by omega
  rw [hcast] at hr
  apply ((hc.seq hr).seq (unmark_hoare xs)).consequence (fun _ h => h) (fun _ h => h) _
  omega

/-- Fixed complete converter: marker setup, copy/rewind, radix countdown with
binary growth, clock erasure, and restoration of the temporary source marker. -/
def convertProgram : Program 3 18 q :=
  seq (seq (seq (seq initializeProgram copyProgram) resetProgram) (extend (coreProgram hq) 1)) cleanupProgram

/-- Exact physical conversion from an untouched radix word and blank work.
Zero values, leading radix zeroes, and the empty word are all supported. -/
theorem convert_hoare (xs : List (Fin q)) :
    HoareTime (convertProgram hq) (fun v => v = input xs) (fun v => v = output xs)
      (10*value xs+6*xs.length+14) := by
  have hcore := (core_hoare hq empty xs (by rfl)
    (by simp [empty,show (1:ℤ)+xs.length ≠ 0 by omega])).extend (oneTape (markedRadix xs) 1)
  have hc : HoareTime (extend (coreProgram hq) 1)
      (fun v => v = prepared [] xs xs 1 1)
      (fun v => v = prepared (RadixToBinaryData.output xs)
        (List.replicate xs.length (lastDigit hq)) xs 1 1) (10*value xs+2*xs.length+2) := by
    apply hcore.consequence _ _ le_rfl
    · intro v hv
      refine ⟨_,rfl,?_⟩
      rw [hv]
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
    · rintro v ⟨w,rfl,rfl⟩
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  apply (((((initialize_hoare xs).seq (copy_hoare xs)).seq (reset_hoare xs)).seq hc).seq
    (cleanup_hoare hq xs)).consequence (fun _ h => h) (fun _ h => h) _
  omega

/-- The conversion overhead is absorbed by one nonempty q^b-wide payload fiber. -/
theorem convert_hoare_power (xs : List (Fin q)) :
    HoareTime (convertProgram hq) (fun v => v = input xs) (fun v => v = output xs)
      (16*q^xs.length+14) := by
  apply (convert_hoare hq xs).consequence (fun _ h => h) (fun _ h => h) _
  have hv := value_lt hq xs
  have hw := width_le_power hq xs.length
  omega

/-- The output slot is the encoded canonical binary word for the radix value. -/
theorem output_binary (xs : List (Fin q)) :
    (output xs).head 0 = 1 ∧
      (output xs).tape 0 = fun z => (binaryEncoding (q := q)).encode
        (CountedCopyReuse.binary (RadixToBinaryData.output xs) z) := ⟨rfl,rfl⟩

/-- Source cells and their original head position are restored exactly. -/
theorem source_preserved (xs : List (Fin q)) :
    (output xs).head 2 = (input xs).head 2 ∧ (output xs).tape 2 = (input xs).tape 2 := ⟨rfl,rfl⟩

/-- Both the work tape and its head return to their original blank condition. -/
theorem work_restored (xs : List (Fin q)) :
    (output xs).head 1 = 0 ∧ (output xs).tape 1 = fun _ => blank := ⟨rfl,rfl⟩

/-- For a nonempty payload block, conversion is uniformly linear in fiber volume. -/
theorem convert_hoare_fiber (xs : List (Fin q)) (B : ℕ) (hB : 0 < B) :
    HoareTime (convertProgram hq) (fun v => v = input xs) (fun v => v = output xs)
      (30*(q^xs.length*B)) := by
  apply (convert_hoare_power hq xs).consequence (fun _ h => h) (fun _ h => h) _
  have hp : 1 ≤ q^xs.length := Nat.one_le_pow _ _ (by omega)
  have hm : q^xs.length ≤ q^xs.length*B := by nlinarith
  omega

end IntegerMultBounds.Machine.RadixToBinary
