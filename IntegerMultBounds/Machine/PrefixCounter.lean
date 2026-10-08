import IntegerMultBounds.Machine.PrefixCounterData
import IntegerMultBounds.Machine.RadixCounter

/-! A concrete carry scheduler over a fixed finite family of separate radix
fields. Overflow restores the selected field's head and immediately enters the
next field. Long spectators incur only actual ripple visits, never a width scan
per fiber. Field order is compiled into the finite transition table. -/
namespace IntegerMultBounds.Machine.PrefixCounter

open RadixDigits RadixCounterData PrefixCounterData
variable {q c : ℕ} (hq : 2 ≤ q)

private def state (i : Fin c) (mode : Fin 3) : Fin (c*3+1) :=
  Fin.castAdd 1 (finProdFinEquiv (i,mode))

private def haltState : Fin (c*3+1) := Fin.natAdd (c*3) 0

private def jump : Option (Fin c) → Fin (c*3+1)
  | none => haltState
  | some i => state i 0

private def fieldTransition (next : Fin c → Option (Fin c)) (i : Fin c) (mode : Fin 3)
    (symbol : Fin (q+4)) : Option (Fin (c*3+1) × Fin (q+4) × Move) :=
  if mode = 0 then
    match readDigit symbol with
    | some x => if h : x.val+1 < q then some (state i 1,digitSymbol ⟨x.val+1,h⟩,.left)
      else some (state i 0,digitSymbol (zeroDigit hq),.right)
    | none => if symbol = blank then some (state i 2,blank,.left) else none
  else if symbol = separator then
    some ((if mode = 1 then haltState else jump (next i)),separator,.right)
  else some (state i mode,symbol,.left)

private def action (symbols : Fin c → Fin (q+4)) (i : Fin c) (x : Fin (q+4)) (move : Move) :=
  fun j => if j = i then (x,move) else (symbols j,Move.stay)

/-- Three carry/return states per field and one genuine halt state. -/
def controller (first : Fin c) (next : Fin c → Option (Fin c)) : Program c (c*3+1) q where
  tapes_pos := by have := first.isLt; omega
  start := state first 0
  transition := fun st symbols => Fin.addCases
    (fun st => let im := finProdFinEquiv.symm st
      (fieldTransition hq next im.1 im.2 (symbols im.1)).map
        (fun (st',x,move) => (st',action symbols im.1 x move))) (fun _ => none) st

private def fieldBank (v : Tapes c q) (i : Fin c) (f : ℤ → Fin (q+4)) (r : ℤ) : Tapes c q :=
  ⟨Function.update v.head i r,Function.update v.tape i f⟩

private def cfg (v : Tapes c q) (i : Fin c) (f : ℤ → Fin (q+4)) (r : ℤ)
    (st : Fin (c*3+1)) : Config c (c*3+1) q := ⟨st,(fieldBank v i f r).head,(fieldBank v i f r).tape⟩

private theorem clock_step (first : Fin c) (next : Fin c → Option (Fin c)) (v : Tapes c q)
    (i : Fin c) (f : ℤ → Fin (q+4)) (r : ℤ) (mode : Fin 3) (st : Fin (c*3+1))
    (x : Fin (q+4)) (move : Move)
    (h : fieldTransition hq next i mode (f r) = some (st,x,move)) :
    step (controller hq first next) (cfg v i f r (state i mode)) =
      some (cfg v i (Function.update f r x) (r+move.offset) st) := by
  simp only [step,controller,cfg,fieldBank,state,Fin.addCases_left,Equiv.symm_apply_apply,Function.update_self]
  rw [h]
  dsimp only [Option.map_some]
  congr 1
  congr 1
  · funext j
    by_cases hj : j = i <;> simp [hj,action,Move.offset]
  · funext j z
    by_cases hj : j = i
    · subst j
      simp [action,Function.update_apply]
    · by_cases hz : z = v.head j <;> simp [action,hj,hz]

private theorem step_small (first : Fin c) (next : Fin c → Option (Fin c)) (v : Tapes c q)
    (i : Fin c) (f : ℤ → Fin (q+4)) (r : ℤ) (x : Fin q) (hx : x.val+1 < q)
    (h : f r = digitSymbol x) :
    step (controller hq first next) (cfg v i f r (state i 0)) =
      some (cfg v i (Function.update f r (digitSymbol ⟨x.val+1,hx⟩)) (r-1) (state i 1)) := by
  apply clock_step hq (move := .left)
  simp [fieldTransition,h,hx]

private theorem step_max (first : Fin c) (next : Fin c → Option (Fin c)) (v : Tapes c q)
    (i : Fin c) (f : ℤ → Fin (q+4)) (r : ℤ) (x : Fin q) (hx : ¬x.val+1 < q)
    (h : f r = digitSymbol x) :
    step (controller hq first next) (cfg v i f r (state i 0)) =
      some (cfg v i (Function.update f r (digitSymbol (zeroDigit hq))) (r+1) (state i 0)) := by
  apply clock_step hq (move := .right)
  simp [fieldTransition,h,hx]

private theorem step_blank (first : Fin c) (next : Fin c → Option (Fin c)) (v : Tapes c q)
    (i : Fin c) (f : ℤ → Fin (q+4)) (r : ℤ) (h : f r = blank) :
    step (controller hq first next) (cfg v i f r (state i 0)) =
      some (cfg v i f (r-1) (state i 2)) := by
  have hh := clock_step hq first next v i f r 0 (state i 2) blank .left (by simp [fieldTransition,h])
  have he : Function.update f r blank = f := Function.update_eq_self_iff.mpr h.symm
  simpa only [he,Move.offset,sub_eq_add_neg] using hh

private theorem step_return (first : Fin c) (next : Fin c → Option (Fin c)) (v : Tapes c q)
    (i : Fin c) (f : ℤ → Fin (q+4)) (r : ℤ) (mode : Fin 3) (hm : mode ≠ 0) (h : f r ≠ separator) :
    step (controller hq first next) (cfg v i f r (state i mode)) =
      some (cfg v i f (r-1) (state i mode)) := by
  have hh := clock_step hq first next v i f r mode (state i mode) (f r) .left
    (by simp [fieldTransition,hm,h])
  simpa only [Function.update_eq_self,Move.offset,sub_eq_add_neg] using hh

private theorem step_marker (first : Fin c) (next : Fin c → Option (Fin c)) (v : Tapes c q)
    (i : Fin c) (f : ℤ → Fin (q+4)) (r : ℤ) (mode : Fin 3) (hm : mode ≠ 0) (h : f r = separator) :
    step (controller hq first next) (cfg v i f r (state i mode)) =
      some (cfg v i f (r+1) (if mode = 1 then haltState else jump (next i))) := by
  have hh := clock_step hq first next v i f r mode (if mode = 1 then haltState else jump (next i))
    separator .right (by simp [fieldTransition,hm,h])
  have he : Function.update f r separator = f := Function.update_eq_self_iff.mpr h.symm
  simpa only [he,Move.offset] using hh

private theorem digit_head (f : ℤ → Fin (q+4)) (r : ℤ) (x : Fin q) (xs : List (Fin q)) :
    RadixCounter.digitsTape f r (x::xs) r = digitSymbol x := by simp [RadixCounter.digitsTape,putWord]

private theorem carry_run (first : Fin c) (next : Fin c → Option (Fin c)) (v : Tapes c q)
    (i : Fin c) (f : ℤ → Fin (q+4)) (r : ℤ) (xs : List (Fin q)) (hend : f (r+xs.length) = blank) :
    run (controller hq first next) (carrySteps xs)
      (cfg v i (RadixCounter.digitsTape f r xs) r (state i 0)) =
      some (cfg v i (RadixCounter.digitsTape f r (increment hq xs))
        (r+carrySteps xs-2) (state i (if overflow xs then 2 else 1))) := by
  induction xs generalizing f r with
  | nil =>
    simp only [List.length_nil,Nat.cast_zero,add_zero] at hend
    simpa [carrySteps,increment,overflow,RadixCounter.digitsTape,putWord,run_one,
      show r+1-2 = r-1 by omega] using step_blank hq first next v i f r hend
  | cons x xs ih =>
    by_cases hx : x.val+1 < q
    · have hs := step_small hq first next v i (RadixCounter.digitsTape f r (x::xs)) r x hx (digit_head f r x xs)
      simpa [carrySteps,increment,overflow,hx,run_one,RadixCounter.digitsTape,putWord,Function.update_idem,
        show r+1-2 = r-1 by omega] using hs
    · have hs := step_max hq first next v i (RadixCounter.digitsTape f r (x::xs)) r x hx (digit_head f r x xs)
      have he : Function.update (RadixCounter.digitsTape f r (x::xs)) r (digitSymbol (zeroDigit hq)) =
          RadixCounter.digitsTape (Function.update f r (digitSymbol (zeroDigit hq))) (r+1) xs :=
        putWord_replace_head f r (digitSymbol x) _ (xs.map digitSymbol)
      rw [he] at hs
      have hend' : (Function.update f r (digitSymbol (zeroDigit hq))) (r+1+xs.length) = blank := by
        rw [Function.update_of_ne (by omega)]
        simpa [List.length_cons,add_assoc,add_comm,add_left_comm] using hend
      have hr := ih (Function.update f r (digitSymbol (zeroDigit hq))) (r+1) hend'
      simp only [carrySteps,increment,overflow,hx,↓reduceIte,↓reduceDIte]
      rw [show carrySteps xs+1 = 1+carrySteps xs by omega,run_add]
      simp only [run_one,hs,Option.bind_some]
      simpa only [RadixCounter.digitsTape,List.map_cons,← putWord_cons,Nat.cast_add,Nat.cast_one,add_assoc] using hr

private theorem return_run (first : Fin c) (next : Fin c → Option (Fin c)) (v : Tapes c q)
    (i : Fin c) (f : ℤ → Fin (q+4)) (mode : Fin 3) (hm : mode ≠ 0) (n : ℕ)
    (hzero : f 0 = separator) (hno : ∀ j : ℕ, 1 ≤ j → j ≤ n → f j ≠ separator) :
    run (controller hq first next) (n+1) (cfg v i f n (state i mode)) =
      some (cfg v i f 1 (if mode = 1 then haltState else jump (next i))) := by
  induction n with
  | zero => simpa only [Nat.cast_zero,run_one,zero_add] using step_marker hq first next v i f 0 mode hm hzero
  | succ n ih =>
    have hs : step (controller hq first next) (cfg v i f ((n:ℤ)+1) (state i mode)) =
        some (cfg v i f n (state i mode)) := by
      simpa only [add_sub_cancel_right] using step_return hq first next v i f ((n:ℤ)+1) mode hm
        (by exact_mod_cast hno (n+1) (by omega) le_rfl)
    simp only [Nat.cast_add,Nat.cast_one,run,hs,Option.bind_some]
    exact ih (fun j hj hn => hno j hj (by omega))

private theorem digits_no_marker (f : ℤ → Fin (q+4)) (xs : List (Fin q)) (j : ℕ)
    (hj : 1 ≤ j) (hu : j ≤ xs.length) : RadixCounter.digitsTape f 1 xs j ≠ separator := by
  have hz : (j:ℤ) = 1+((j-1 : ℕ) : ℤ) := by omega
  have hi : j-1 < (xs.map digitSymbol).length := by simp only [List.length_map]; omega
  rw [RadixCounter.digitsTape,hz,WordSegments.get _ _ _ _ hi,List.getElem_map]
  simp [digitSymbol,separator,Fin.ext_iff]

private theorem field_exact (first : Fin c) (next : Fin c → Option (Fin c)) (v : Tapes c q)
    (i : Fin c) (f : ℤ → Fin (q+4)) (xs : List (Fin q))
    (hzero : f 0 = separator) (hend : f (1+xs.length) = blank) :
    run (controller hq first next) (2*carrySteps xs)
      (cfg v i (RadixCounter.digitsTape f 1 xs) 1 (state i 0)) =
      some (cfg v i (RadixCounter.digitsTape f 1 (increment hq xs)) 1
        (if overflow xs then jump (next i) else haltState)) := by
  obtain ⟨hpos,hlen⟩ := carrySteps_bounds xs
  let n := carrySteps xs-1
  have hn : n+1 = carrySteps xs := by dsimp [n]; omega
  have hh : (1:ℤ)+carrySteps xs-2 = (n:ℤ) := by omega
  have hmark : RadixCounter.digitsTape f 1 (increment hq xs) 0 = separator := by
    rw [RadixCounter.digitsTape,putWord_outside _ _ _ _ (Or.inl (by omega)),hzero]
  have hno : ∀ j : ℕ, 1 ≤ j → j ≤ n → RadixCounter.digitsTape f 1 (increment hq xs) j ≠ separator := by
    intro j hj hjn
    exact digits_no_marker _ _ j hj (by rw [increment_length]; omega)
  rw [show 2*carrySteps xs = carrySteps xs+(n+1) by omega,run_add,carry_run hq first next v i f 1 xs hend]
  simp only [Option.bind_some,hh]
  have hr := return_run hq first next v i (RadixCounter.digitsTape f 1 (increment hq xs))
    (if overflow xs then 2 else 1) (by cases overflow xs <;> decide) n hmark hno
  cases ho : overflow xs <;> simpa [ho] using hr

/-- A separate marked word for each field, all least-significant heads at one. -/
def tapes (f : Fin c → ℤ → Fin (q+4)) (ds : Fin c → List (Fin q)) : Tapes c q :=
  ⟨fun _ => 1,fun i => RadixCounter.digitsTape (f i) 1 (ds i)⟩

private def boundary (f : Fin c → ℤ → Fin (q+4)) (ds : Fin c → List (Fin q))
    (st : Fin (c*3+1)) : Config c (c*3+1) q := ⟨st,(tapes f ds).head,(tapes f ds).tape⟩

private theorem field_run (first : Fin c) (next : Fin c → Option (Fin c))
    (f : Fin c → ℤ → Fin (q+4)) (ds : Fin c → List (Fin q)) (i : Fin c)
    (hzero : f i 0 = separator) (hend : f i (1+(ds i).length) = blank) :
    run (controller hq first next) (2*carrySteps (ds i)) (boundary f ds (state i 0)) =
      some (boundary f (Function.update ds i (increment hq (ds i)))
        (if overflow (ds i) then jump (next i) else haltState)) := by
  have h := field_exact hq first next (tapes f ds) i (f i) (ds i) hzero hend
  have ha : fieldBank (tapes f ds) i (RadixCounter.digitsTape (f i) 1 (ds i)) 1 = tapes f ds := by
    apply congrArg₂ Tapes.mk
    · simp [tapes]
    · simp [tapes]
  have hb : fieldBank (tapes f ds) i (RadixCounter.digitsTape (f i) 1 (increment hq (ds i))) 1 =
      tapes f (Function.update ds i (increment hq (ds i))) := by
    apply congrArg₂ Tapes.mk
    · simp [tapes]
    · funext j
      by_cases hj : j = i <;> simp [hj,tapes]
  unfold cfg at h
  rw [ha,hb] at h
  exact h

/-- A fixed successor lookup is compiled once from the chosen field order. -/
def successor : List (Fin c) → Fin c → Option (Fin c)
  | [],_ => none
  | i::is,j => if j = i then is.head? else successor is j

private theorem chain_run (first : Fin c) (next : Fin c → Option (Fin c))
    (is : List (Fin c)) (hn : is.Nodup) (hpath : ∀ i ∈ is, next i = successor is i)
    (f : Fin c → ℤ → Fin (q+4)) (ds : Fin c → List (Fin q))
    (hzero : ∀ i, f i 0 = separator) (hend : ∀ i, f i (1+(ds i).length) = blank) :
    run (controller hq first next) (stepCost hq is ds) (boundary f ds (jump is.head?)) =
      some (boundary f (advanceFields hq is ds) haltState) := by
  induction is generalizing ds with
  | nil => rfl
  | cons i is ih =>
    obtain ⟨hni,hnt⟩ := List.nodup_cons.mp hn
    have hnext : next i = is.head? := by simpa only [successor,ite_true] using hpath i (by simp)
    have htail : ∀ j ∈ is, next j = successor is j := by
      intro j hj
      have hji : j ≠ i := by intro he; subst j; exact hni hj
      simpa only [successor,hji,ite_false] using hpath j (by simp [hj])
    have hd := field_run hq first next f ds i (hzero i) (hend i)
    by_cases ho : overflow (ds i) = true
    · simp only [stepCost,advanceFields,ho,ite_true,List.head?_cons,jump]
      rw [run_add,hd]
      simp only [ho,ite_true,Option.bind_some,hnext]
      exact ih hnt htail _ (fun j => by by_cases hj : j = i <;> simpa [hj] using hend j)
    · simpa only [stepCost,advanceFields,ho,Bool.false_eq_true,ite_false,add_zero,List.head?_cons,jump] using hd

private theorem halted (first : Fin c) (next : Fin c → Option (Fin c))
    (f : Fin c → ℤ → Fin (q+4)) (ds : Fin c → List (Fin q)) :
    step (controller hq first next) (boundary f ds haltState) = none := by
  simp [step,controller,boundary,haltState]

/-- Fixed finite control for any chosen nonempty list of distinct fields.
The list is a compile-time constant, not a tape-supplied schedule or oracle. -/
def program (is : List (Fin c)) (hne : is ≠ []) : Program c (c*3+1) q :=
  controller hq (is.head hne) (successor is)

private theorem start_eq (is : List (Fin c)) (hne : is ≠ [])
    (f : Fin c → ℤ → Fin (q+4)) (ds : Fin c → List (Fin q)) :
    (tapes f ds).start (program hq is hne) = boundary f ds (jump is.head?) := by
  cases is with
  | nil => contradiction
  | cons i is => rfl

/-- Exact mixed-prefix increment. Every digit update, field return and
cross-field carry is a real transition of the fixed scheduler. -/
theorem increment_exact (is : List (Fin c)) (hne : is ≠ []) (hn : is.Nodup)
    (f : Fin c → ℤ → Fin (q+4)) (ds : Fin c → List (Fin q))
    (hzero : ∀ i, f i 0 = separator) (hend : ∀ i, f i (1+(ds i).length) = blank) :
    run (program hq is hne) (stepCost hq is ds) ((tapes f ds).start (program hq is hne)) =
      some (boundary f (advanceFields hq is ds) haltState) := by
  rw [start_eq]
  exact chain_run hq (is.head hne) (successor is) is hn (fun _ _ => rfl) f ds hzero hend

theorem increment_hoare (is : List (Fin c)) (hne : is ≠ []) (hn : is.Nodup)
    (f : Fin c → ℤ → Fin (q+4)) (ds : Fin c → List (Fin q))
    (hzero : ∀ i, f i 0 = separator) (hend : ∀ i, f i (1+(ds i).length) = blank) :
    HoareTime (program hq is hne) (fun v => v = tapes f ds)
      (fun v => v = tapes f (advanceFields hq is ds)) (stepCost hq is ds) := by
  rintro v rfl
  exact ⟨_,_,le_rfl,increment_exact hq is hne hn f ds hzero hend,halted hq _ _ _ _,rfl⟩

/-- A fixed cyclic driver; finite-prefix theorems expose scheduler boundaries.
The driver intentionally cycles, so no terminal halt is asserted here. -/
def cycleProgram (is : List (Fin c)) (hne : is ≠ []) : Program c (c*3+2) q :=
  whileLoop (program hq is hne) (fun _ => true)

theorem cycle_exact (is : List (Fin c)) (hne : is ≠ []) (hn : is.Nodup) (n : ℕ)
    (f : Fin c → ℤ → Fin (q+4)) (ds : Fin c → List (Fin q))
    (hzero : ∀ i, f i 0 = separator) (hend : ∀ i, f i (1+(ds i).length) = blank) :
    run (cycleProgram hq is hne) (PrefixCounterData.cycleTime hq is n ds)
      ((tapes f ds).start (cycleProgram hq is hne)) =
      some ((tapes f (iterateFields hq is n ds)).start (cycleProgram hq is hne)) := by
  induction n generalizing ds with
  | zero => rfl
  | succ n ih =>
    have hi := while_run_iteration (program hq is hne) (fun _ => true) (tapes f ds) rfl
      (increment_exact hq is hne hn f ds hzero hend) (halted hq _ _ _ _)
    change run (cycleProgram hq is hne) (stepCost hq is ds+2) ((tapes f ds).start (cycleProgram hq is hne)) =
      some ((tapes f (advanceFields hq is ds)).start (cycleProgram hq is hne)) at hi
    simp only [PrefixCounterData.cycleTime,iterateFields,run_add,hi,Option.bind_some]
    exact ih (advanceFields hq is ds) (fun i => by simpa only [widths_preserved] using hend i)

/-- All other tapes and their heads are exact frames. The aggregate carry
bound has no per-iteration spectator-width factor. -/
theorem framed_cycle {t : ℕ} (frame : Tapes t q) (is : List (Fin c)) (hne : is ≠ []) (hn : is.Nodup)
    (n : ℕ) (f : Fin c → ℤ → Fin (q+4)) (ds : Fin c → List (Fin q))
    (hzero : ∀ i, f i 0 = separator) (hend : ∀ i, f i (1+(ds i).length) = blank) :
    ∃ k, k ≤ (4*is.length+2)*n+2*∑ i, (ds i).length ∧
      run (extend (cycleProgram hq is hne) t) k
        (((tapes f ds).append frame).start (extend (cycleProgram hq is hne) t)) =
        some (((tapes f (iterateFields hq is n ds)).append frame).start (extend (cycleProgram hq is hne) t)) := by
  refine ⟨PrefixCounterData.cycleTime hq is n ds,PrefixCounterData.cycle_amortized hq is n ds,?_⟩
  exact extend_run (cycleProgram hq is hne) frame (cycle_exact hq is hne hn n f ds hzero hend)

/-- The usual fixed order visits every physical prefix field exactly once,
with field zero fastest. Reversing field placement gives conventional lex order. -/
def lexProgram (hc : 0 < c) : Program c (c*3+1) q :=
  program hq (List.finRange c) (by intro h; have := congrArg List.length h; simp at this; omega)

/-- Exact physical lexicographic prefix update on an arbitrary family of
control and spectator widths. No equality between those widths is required. -/
theorem lex_hoare (hc : 0 < c) (f : Fin c → ℤ → Fin (q+4)) (ds : Fin c → List (Fin q))
    (hzero : ∀ i, f i 0 = separator) (hend : ∀ i, f i (1+(ds i).length) = blank) :
    HoareTime (lexProgram hq hc) (fun v => v = tapes f ds)
      (fun v => v = tapes f (advanceFields hq (List.finRange c) ds) ∧
        value (PrefixCounterData.flatten (List.finRange c) (advanceFields hq (List.finRange c) ds)) =
          (value (PrefixCounterData.flatten (List.finRange c) ds)+1)%
            q^(PrefixCounterData.flatten (List.finRange c) ds).length)
      (stepCost hq (List.finRange c) ds) := by
  have h := increment_hoare hq (List.finRange c)
    (by intro he; have := congrArg List.length he; simp at this; omega) (List.nodup_finRange c) f ds hzero hend
  apply h.consequence (fun _ h => h) _ le_rfl
  intro v hv
  refine ⟨hv,?_⟩
  rw [flatten_advance hq _ (List.nodup_finRange c),increment_value]

/-- The cyclic version of the concrete complete-field scheduler. -/
def lexCycleProgram (hc : 0 < c) : Program c (c*3+2) q :=
  cycleProgram hq (List.finRange c) (by intro h; have := congrArg List.length h; simp at this; omega)

/-- One complete mixed-prefix traversal restores every field and arbitrary
framed payload. Its cost is linear in the number of prefix addresses, with a
constant depending only on the fixed number of fields. -/
theorem full_cycle_framed {t : ℕ} (frame : Tapes t q) (hc : 0 < c)
    (f : Fin c → ℤ → Fin (q+4)) (ds : Fin c → List (Fin q))
    (hzero : ∀ i, f i 0 = separator) (hend : ∀ i, f i (1+(ds i).length) = blank) :
    ∃ k, k ≤ (4*c+4)*q^(∑ i, (ds i).length) ∧
      run (extend (lexCycleProgram hq hc) t) k
        (((tapes f ds).append frame).start (extend (lexCycleProgram hq hc) t)) =
        some (((tapes f ds).append frame).start (extend (lexCycleProgram hq hc) t)) := by
  refine ⟨PrefixCounterData.cycleTime hq (List.finRange c) (q^(∑ i, (ds i).length)) ds,
    PrefixCounterData.full_cycle_cost hq ds,?_⟩
  have hne : List.finRange c ≠ [] := by intro h; have := congrArg List.length h; simp at this; omega
  have h := extend_run (lexCycleProgram hq hc) frame
    (cycle_exact hq (List.finRange c) hne (List.nodup_finRange c) (q^(∑ i, (ds i).length)) f ds hzero hend)
  rw [PrefixCounterData.full_cycle] at h
  exact h

/-- At every boundary the physical family contains the exact next prefix
address, without modifying widths or reading unrelated full spectator words. -/
theorem lex_enumeration (hc : 0 < c) (n : ℕ)
    (f : Fin c → ℤ → Fin (q+4)) (ds : Fin c → List (Fin q))
    (hzero : ∀ i, f i 0 = separator) (hend : ∀ i, f i (1+(ds i).length) = blank) :
    ∃ k, k ≤ (4*c+2)*n+2*∑ i, (ds i).length ∧
      run (lexCycleProgram hq hc) k ((tapes f ds).start (lexCycleProgram hq hc)) =
        some ((tapes f (iterateFields hq (List.finRange c) n ds)).start (lexCycleProgram hq hc)) ∧
      value (PrefixCounterData.flatten (List.finRange c) (iterateFields hq (List.finRange c) n ds)) =
        (value (PrefixCounterData.flatten (List.finRange c) ds)+n)%q^(∑ i, (ds i).length) ∧
      ∀ j, (iterateFields hq (List.finRange c) n ds j).length = (ds j).length := by
  have hne : List.finRange c ≠ [] := by intro h; have := congrArg List.length h; simp at this; omega
  refine ⟨PrefixCounterData.cycleTime hq (List.finRange c) n ds,?_,
    cycle_exact hq (List.finRange c) hne (List.nodup_finRange c) n f ds hzero hend,?_,?_⟩
  · simpa only [List.length_finRange] using PrefixCounterData.cycle_amortized hq (List.finRange c) n ds
  · rw [enumeration_value hq _ (List.nodup_finRange c),flatten_length]
  · exact iterate_widths hq (List.finRange c) n ds

end IntegerMultBounds.Machine.PrefixCounter
