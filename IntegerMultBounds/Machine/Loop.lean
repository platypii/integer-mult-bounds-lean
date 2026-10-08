import IntegerMultBounds.Machine.Hoare

/-!
A finite-state while loop whose test reads only the currently scanned symbols.
The test and return each take one transition when the body is executed; a false
test halts immediately. In particular, this construction does not rewind an
output tape or scan a binary limit between iterations.

The potential rule charges the actual body runtime plus both control steps.
It supports variable-cost iterations without replacing them by their maximum.
-/

namespace IntegerMultBounds.Machine

variable {t q a : ℕ}

def Tapes.reads (v : Tapes t a) : Fin t → Fin (a + 4) :=
  fun i => v.tape i (v.head i)

/-- A local-symbol test and a fixed body, compiled into `q + 1` states. -/
def whileLoop (M : Program t q a) (test : (Fin t → Fin (a + 4)) → Bool) :
    Program t (q + 1) a where
  tapes_pos := M.tapes_pos
  start := Fin.natAdd q 0
  transition := fun s symbols => Fin.addCases
    (fun u => match M.transition u symbols with
      | none => some (Fin.natAdd q 0, fun i => (symbols i, .stay))
      | some (v, action) => some (Fin.castAdd 1 v, action))
    (fun _ => if test symbols then
      some (Fin.castAdd 1 M.start, fun i => (symbols i, .stay)) else none) s

theorem while_step_body (M : Program t q a) (test)
    {c d : Config t q a} (h : step M c = some d) :
    step (whileLoop M test) (c.mapState (Fin.castAdd 1)) =
      some (d.mapState (Fin.castAdd 1)) := by
  unfold step at h ⊢
  simp only [whileLoop, Config.mapState, Fin.addCases_left]
  cases ht : M.transition c.state (fun i => c.tape i (c.head i)) with
  | none => simp [ht] at h
  | some v =>
    rcases v with ⟨s, action⟩
    simp only [ht] at h ⊢
    cases h
    rfl

theorem while_step_enter (M : Program t q a) (test) (v : Tapes t a)
    (h : test v.reads = true) :
    step (whileLoop M test) (v.start (whileLoop M test)) =
      some ((v.start M).mapState (Fin.castAdd 1)) := by
  unfold Tapes.reads at h
  simp only [step, Tapes.start, whileLoop, Fin.addCases_right, h,
    ↓reduceIte, Config.mapState, Move.offset, add_zero]
  congr 1
  congr 1
  funext i j
  by_cases hj : j = v.head i
  · subst j; simp
  · simp [hj]

theorem while_step_exit (M : Program t q a) (test) (v : Tapes t a)
    (h : test v.reads = false) :
    step (whileLoop M test) (v.start (whileLoop M test)) = none := by
  unfold Tapes.reads at h
  simp [step, Tapes.start, whileLoop, h]

theorem while_step_return (M : Program t q a) (test)
    {c : Config t q a} (h : step M c = none) :
    step (whileLoop M test) (c.mapState (Fin.castAdd 1)) =
      some (c.tapes.start (whileLoop M test)) := by
  unfold step at h ⊢
  simp only [whileLoop, Config.mapState, Fin.addCases_left]
  cases ht : M.transition c.state (fun i => c.tape i (c.head i)) with
  | none =>
    simp only [Move.offset, add_zero, Config.tapes, Tapes.start]
    congr 1
    congr 1
    funext i j
    by_cases hj : j = c.head i
    · subst j; simp
    · simp [hj]
  | some v => simp [ht] at h

/-- A complete iteration includes the test and return transitions. -/
theorem while_run_iteration (M : Program t q a) (test) (v : Tapes t a)
    {c : Config t q a} {k : ℕ} (htest : test v.reads = true)
    (hrun : run M k (v.start M) = some c) (hhalt : step M c = none) :
    run (whileLoop M test) (k + 2) (v.start (whileLoop M test)) =
      some (c.tapes.start (whileLoop M test)) := by
  rw [show k + 2 = 1 + k + 1 by omega, run_add, run_add]
  simp only [run_one, while_step_enter M test v htest, Option.bind_some]
  rw [run_simulation M (whileLoop M test) _
    (fun _ _ h => while_step_body M test h) hrun]
  simp only [Option.bind_some, while_step_return M test hhalt]

/-- Every iteration pays for its actual runtime from a natural-valued budget.
The remaining budget is retained in the conclusion, giving a telescoping bound.
The premise is a proof of the concrete body's execution, not an oracle cost. -/
theorem while_run_potential (M : Program t q a) (test)
    (inv : TapePred t a) (potential : Tapes t a → ℕ)
    (hbody : ∀ v, inv v → test v.reads = true →
      ∃ k c, run M k (v.start M) = some c ∧ step M c = none ∧
        inv c.tapes ∧ k + 2 + potential c.tapes ≤ potential v)
    (v : Tapes t a) (hv : inv v) :
    ∃ k c, run (whileLoop M test) k (v.start (whileLoop M test)) = some c ∧
      step (whileLoop M test) c = none ∧ inv c.tapes ∧
      test c.tapes.reads = false ∧ k + potential c.tapes ≤ potential v := by
  suffices ∀ fuel, ∀ v : Tapes t a, potential v ≤ fuel → inv v →
      ∃ k c, run (whileLoop M test) k (v.start (whileLoop M test)) = some c ∧
        step (whileLoop M test) c = none ∧ inv c.tapes ∧
        test c.tapes.reads = false ∧ k + potential c.tapes ≤ potential v from
    this (potential v) v le_rfl hv
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro v hfuel hv
    cases ht : test v.reads with
    | false =>
      exact ⟨0, v.start (whileLoop M test), rfl,
        while_step_exit M test v ht, hv, ht, by simp [Config.tapes, Tapes.start]⟩
    | true =>
      obtain ⟨k, c, hr, hh, hc, hp⟩ := hbody v hv ht
      obtain ⟨l, d, hs, hd, hi, hx, hl⟩ :=
        ih (potential c.tapes) (by omega) c.tapes le_rfl hc
      refine ⟨k + 2 + l, d, ?_, hd, hi, hx, by omega⟩
      rw [run_add, while_run_iteration M test v ht hr hh]
      exact hs

theorem while_hoare_potential (M : Program t q a) (test)
    (inv : TapePred t a) (potential : Tapes t a → ℕ) (bound : ℕ)
    (hbody : ∀ v, inv v → test v.reads = true →
      ∃ k c, run M k (v.start M) = some c ∧ step M c = none ∧
        inv c.tapes ∧ k + 2 + potential c.tapes ≤ potential v) :
    HoareTime (whileLoop M test) (fun v => inv v ∧ potential v ≤ bound)
      (fun v => inv v ∧ test v.reads = false) bound := by
  intro v ⟨hv, hb⟩
  obtain ⟨k, c, hr, hh, hi, ht, hp⟩ := while_run_potential M test inv potential hbody v hv
  exact ⟨k, c, by omega, hr, hh, hi, ht⟩

end IntegerMultBounds.Machine
