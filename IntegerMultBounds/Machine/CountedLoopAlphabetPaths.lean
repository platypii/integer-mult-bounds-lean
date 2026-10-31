module

public import IntegerMultBounds.Machine.CountedLoopAlphabetBounds

/-! Logical control-only paths stop at body entry. Their terminal boundary is
uniquely determined by the actual binary decrement, so body-level invariants
can retain the exact relationship between iteration index and clock word. -/
@[expose] public section
namespace IntegerMultBounds.Machine.CountedLoopAlphabet
open CountdownData
variable {t q a : ℕ}

def ControlStep (M : Program t q a) (c d : Config (t+1) (q+5) a) : Prop :=
  c.state ≠ Fin.natAdd q 3 ∧ Machine.step (program M) c = some d

abbrev ControlPath (M : Program t q a) := Relation.ReflTransGen (ControlStep M)

theorem control_single (M : Program t q a) (v : Tapes t a) (f : ℤ → Fin (a+4)) (r : ℤ)
    (s : Fin 5) (hs : s ≠ 3) {d : Config (t+1) (q+5) a}
    (hd : Machine.step (program M) (cfg M v f r s) = some d) : ControlPath M (cfg M v f r s) d := by
  apply Relation.ReflTransGen.single
  exact ⟨fun he => hs (by simpa only [cfg,Fin.natAdd_inj] using he),hd⟩

private theorem borrow_path (M : Program t q a) (v : Tapes t a) (clock : ℤ → Fin (a+4))
    (r : ℤ) (bs : List Bool) (hend : clock (r+bs.length) = blank) :
    ControlPath M (cfg M v (putBits clock r bs) r 0)
      (cfg M v (putBits clock r (decrement bs)) (r+borrowSteps bs-2) (if underflow bs then 2 else 1)) := by
  induction bs generalizing clock r with
  | nil =>
    simp only [List.length_nil,Nat.cast_zero,add_zero] at hend
    simpa [borrowSteps,decrement,underflow,putBits,show r+1-2 = r-1 by omega] using
      control_single M v clock r 0 (by decide) (step_blank M v clock r hend)
  | cons b bs ih =>
    cases b with
    | true =>
      have hs := step_one M v (putBits clock r (true::bs)) r (putBits_head clock r true bs)
      have hp := control_single M v (putBits clock r (true::bs)) r 0 (by decide) hs
      simpa [borrowSteps,decrement,underflow,putBits,Function.update_idem,show r+1-2 = r-1 by omega] using hp
    | false =>
      have hs := step_zero M v (putBits clock r (false::bs)) r (putBits_head clock r false bs)
      have he : Function.update (putBits clock r (false::bs)) r (bitSymbol true) =
          putBits (Function.update clock r (bitSymbol true)) (r+1) bs := by
        rw [putBits_update_before clock (r+1) r (bitSymbol true) bs (by omega)]
        simp [putBits]
      rw [he] at hs
      have hp := control_single M v (putBits clock r (false::bs)) r 0 (by decide) hs
      have hend' : (Function.update clock r (bitSymbol true)) (r+1+bs.length) = blank := by
        rw [Function.update_of_ne (by omega)]
        simpa [List.length_cons,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using hend
      have hr := ih (Function.update clock r (bitSymbol true)) (r+1) hend'
      have hpath := hp.trans hr
      have hword : putBits (Function.update clock r (bitSymbol true)) (r+1) (decrement bs) =
          putBits clock r (true::decrement bs) := (putBits_cons clock r true (decrement bs)).symm
      have hhead : r+1+(borrowSteps bs : ℤ)-2 = r+((borrowSteps bs+1 : ℕ) : ℤ)-2 := by omega
      rw [hword,hhead] at hpath
      simp only [borrowSteps,decrement,underflow]
      exact hpath

private theorem return_path (M : Program t q a) (v : Tapes t a) (clock : ℤ → Fin (a+4))
    (s : Fin 5) (hs : s = 1 ∨ s = 2) (n : ℕ) (hzero : clock 0 = separator)
    (hno : ∀ j : ℕ, 1 ≤ j → j ≤ n → clock j ≠ separator) :
    ControlPath M (cfg M v clock n s) (cfg M v clock 1 (if s = 1 then 3 else 4)) := by
  have hs3 : s ≠ 3 := by rcases hs with rfl | rfl <;> decide
  induction n with
  | zero =>
    simpa only [Nat.cast_zero,zero_add] using
      control_single M v clock 0 s hs3 (step_marker M v clock 0 s hs hzero)
  | succ n ih =>
    have hstep : Machine.step (program M) (cfg M v clock ((n : ℤ)+1) s) = some (cfg M v clock n s) := by
      simpa only [add_sub_cancel_right] using step_return M v clock ((n : ℤ)+1) s hs
        (by exact_mod_cast hno (n+1) (by omega) le_rfl)
    have hp := control_single M v clock ((n : ℤ)+1) s hs3 hstep
    simpa only [Nat.cast_add,Nat.cast_one] using hp.trans (ih (fun j hj hn => hno j hj (by omega)))

theorem decrement_path (M : Program t q a) (v : Tapes t a) (clock : ℤ → Fin (a+4))
    (bs : List Bool) (hzero : clock 0 = separator) (hend : clock (1+bs.length) = blank) :
    ControlPath M (cfg M v (putBits clock 1 bs) 1 0)
      (cfg M v (putBits clock 1 (decrement bs)) 1 (if underflow bs then 4 else 3)) := by
  have hpos := (borrowSteps_bounds bs).1
  let n := borrowSteps bs-1
  have hh : (1 : ℤ)+borrowSteps bs-2 = (n : ℤ) := by dsimp [n]; omega
  have hmark : putBits clock 1 (decrement bs) 0 = separator := by
    rw [putBits_outside clock 1 0 _ (Or.inl (by omega)),hzero]
  have hno : ∀ j : ℕ, 1 ≤ j → j ≤ n → putBits clock 1 (decrement bs) j ≠ separator := by
    intro j hj hjn
    apply putBits_ne_separator
    · omega
    · rw [decrement_length]
      have hlen := (borrowSteps_bounds bs).2.1
      dsimp [n] at hjn
      omega
  have hb := borrow_path M v clock 1 bs hend
  rw [hh] at hb
  have hr := return_path M v (putBits clock 1 (decrement bs))
    (if underflow bs then 2 else 1) (by cases underflow bs <;> simp) n hmark hno
  cases hu : underflow bs <;> simpa [hu] using hb.trans hr

private theorem control_terminal (M : Program t q a) (v : Tapes t a) (clock : ℤ → Fin (a+4))
    (r : ℤ) (s : Fin 5) (hs : s = 3 ∨ s = 4) :
    ∀ d, ¬ControlStep M (cfg M v clock r s) d := by
  intro d hd
  rcases hs with rfl | rfl
  · exact hd.1 rfl
  · have ht := hd.2
    rw [halt] at ht
    cases ht

/-- Any control-only path reaching body entry or underflow has the exact
boundary word produced by one decrement. There is no hidden extra iteration. -/
theorem decrement_boundary_eq (M : Program t q a) (v : Tapes t a) (clock : ℤ → Fin (a+4))
    (bs : List Bool) (hzero : clock 0 = separator) (hend : clock (1+bs.length) = blank)
    {f : ℤ → Fin (a+4)} {r : ℤ} {s : Fin 5}
    (hp : ControlPath M (cfg M v (putBits clock 1 bs) 1 0) (cfg M v f r s))
    (hs : s = 3 ∨ s = 4) :
    cfg M v f r s = cfg M v (putBits clock 1 (decrement bs)) 1 (if underflow bs then 4 else 3) := by
  have href := decrement_path M v clock bs hzero hend
  have hunique : Relator.RightUnique (ControlStep M) := by
    intro x y z hy hz
    exact Option.some.inj (hy.2.symm.trans hz.2)
  have ht := control_terminal M v f r s hs
  have ht' := control_terminal M v (putBits clock 1 (decrement bs)) 1
    (if underflow bs then 4 else 3) (by cases underflow bs <;> simp)
  rcases Relation.ReflTransGen.total_of_right_unique hunique hp href with h | h
  · rcases h.cases_head with he | ⟨d,hd,_⟩
    · exact he
    · exact (ht d hd).elim
  · rcases h.cases_head with he | ⟨d,hd,_⟩
    · exact he.symm
    · exact (ht' d hd).elim

/-- A real body entry consumes exactly one positive clock unit and returns
the head to its origin. This is the counter/level handoff used by loop bodies. -/
theorem decrement_body_entry (M : Program t q a) (v : Tapes t a) (clock : ℤ → Fin (a+4))
    (bs : List Bool) (hzero : clock 0 = separator) (hend : clock (1+bs.length) = blank)
    {f : ℤ → Fin (a+4)} {r : ℤ}
    (hp : ControlPath M (cfg M v (putBits clock 1 bs) 1 0) (cfg M v f r 3)) :
    r = 1 ∧ f = putBits clock 1 (decrement bs) ∧ 0 < Counter.value bs ∧
      Counter.value (decrement bs)+1 = Counter.value bs := by
  have he := decrement_boundary_eq M v clock bs hzero hend hp (Or.inl rfl)
  have hu : underflow bs = false := by
    cases hu : underflow bs with
    | false => rfl
    | true =>
      have hs : (3 : Fin 5) = 4 := by
        simpa only [cfg,hu,ite_true,Fin.natAdd_inj] using congrArg Config.state he
      exact ((by decide : (3 : Fin 5) ≠ 4) hs).elim
  simp only [hu,Bool.false_eq_true,ite_false] at he
  have hh := congrArg (fun c => c.head (Fin.natAdd t (0 : Fin 1))) he
  have ht := congrArg (fun c => c.tape (Fin.natAdd t (0 : Fin 1))) he
  have hv := (underflow_eq_false_iff bs).mp hu
  refine ⟨?_,?_,hv,decrement_value bs hv⟩
  · simpa only [cfg,Tapes.append,Fin.addCases_right] using hh
  · simpa only [cfg,Tapes.append,Fin.addCases_right] using ht

end IntegerMultBounds.Machine.CountedLoopAlphabet
