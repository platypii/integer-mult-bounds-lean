module

public import IntegerMultBounds.Machine.Hoare

/-! Head travel during actual runs. Linear-time setup and movement routines
can use these bounds; superlinear recursive bodies need stronger invariants. -/
@[expose] public section
namespace IntegerMultBounds.Machine
variable {t q a : ℕ}

theorem step_head_travel {M : Program t q a} {c d : Config t q a}
    (hs : step M c = some d) (i : Fin t) :
    c.head i-1 ≤ d.head i ∧ d.head i ≤ c.head i+1 := by
  unfold step at hs
  split at hs
  · simp at hs
  · rename_i st act ht
    cases hs
    change c.head i-1 ≤ c.head i+(act i).2.offset ∧ c.head i+(act i).2.offset ≤ c.head i+1
    cases (act i).2 <;> simp only [Move.offset] <;> omega

theorem run_head_travel {M : Program t q a} {c d : Config t q a} {n : ℕ}
    (hr : run M n c = some d) (i : Fin t) :
    c.head i-n ≤ d.head i ∧ d.head i ≤ c.head i+n := by
  induction n generalizing c with
  | zero => simp only [run,Option.some.injEq] at hr; subst d; simp
  | succ n ih =>
    simp only [run] at hr
    cases hs : step M c with
    | none => simp [hs] at hr
    | some x =>
      rw [hs,Option.bind_some] at hr
      have h := ih hr
      have h' := step_head_travel hs i
      push_cast
      omega

/-- No successful prefix extends beyond a known halting run. -/
theorem run_length_le_of_halt {M : Program t q a} {c d z : Config t q a} {n m : ℕ}
    (hn : run M n c = some d) (hm : run M m c = some z) (hz : step M z = none) : n ≤ m := by
  induction m generalizing c n with
  | zero =>
    simp only [run,Option.some.injEq] at hm
    subst z
    cases n with
    | zero => omega
    | succ n => simp [run,hz] at hn
  | succ m ih =>
    cases n with
    | zero => omega
    | succ n =>
      simp only [run] at hm hn
      cases hs : step M c with
      | none => simp [hs] at hm
      | some x =>
        rw [hs,Option.bind_some] at hm hn
        exact Nat.succ_le_succ (ih hn hm)

end IntegerMultBounds.Machine
