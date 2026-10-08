import IntegerMultBounds.Machine.Execution

/-!
Finite-state sequential composition in the project's literal machine model.
The connection between programs takes one actual transition, preserving every
tape and head. No runtime or implementation assumption is added to `Program`.

The design follows the exact-cost composition approach of complexitylib
(SamuelSchlesinger/complexitylib, commit 3f4b5fe, Apache 2.0); definitions and
proofs here are for our two-sided, writable-tape model.
-/

namespace IntegerMultBounds.Machine

variable {t q r a : ℕ}

/-- Relabel a configuration's finite control, leaving all tape data intact. -/
def Config.mapState {r : ℕ} (f : Fin q → Fin r) (c : Config t q a) : Config t r a :=
  { state := f c.state, head := c.head, tape := c.tape }

/-- Transport a successful run along a simulation of each actual step. -/
theorem run_simulation {t' q' a' : ℕ}
    (M : Program t q a) (N : Program t' q' a')
    (f : Config t q a → Config t' q' a')
    (hs : ∀ c d, step M c = some d → step N (f c) = some (f d))
    {k : ℕ} {c d : Config t q a} (h : run M k c = some d) :
    run N k (f c) = some (f d) := by
  induction k generalizing c with
  | zero => simpa only [run, Option.some.injEq] using congrArg f (Option.some.inj h)
  | succ k ih =>
    obtain ⟨e, he, hd⟩ := Option.bind_eq_some_iff.mp h
    simp only [run, hs c e he, Option.bind_some]
    exact ih hd

/-- Run the first finite control, then the second. On the first halt, a
single read-back/stay transition enters the second program's start state. -/
def seq (M : Program t q a) (N : Program t r a) : Program t (q + r) a where
  tapes_pos := M.tapes_pos
  start := Fin.castAdd r M.start
  transition := fun s symbols => Fin.addCases
    (fun u => match M.transition u symbols with
      | none => some (Fin.natAdd q N.start, fun i => (symbols i, .stay))
      | some (v, action) => some (Fin.castAdd r v, action))
    (fun u => (N.transition u symbols).map (fun (v, action) =>
      (Fin.natAdd q v, action))) s

theorem seq_step_left (M : Program t q a) (N : Program t r a)
    {c d : Config t q a} (h : step M c = some d) :
    step (seq M N) (c.mapState (Fin.castAdd r)) =
      some (d.mapState (Fin.castAdd r)) := by
  unfold step at h ⊢
  simp only [seq, Config.mapState, Fin.addCases_left]
  cases ht : M.transition c.state (fun i => c.tape i (c.head i)) with
  | none => simp [ht] at h
  | some v =>
    rcases v with ⟨s, action⟩
    simp only [ht] at h ⊢
    cases h
    rfl

/-- The composition boundary preserves entire tapes, including blank tails. -/
theorem seq_step_boundary (M : Program t q a) (N : Program t r a)
    {c : Config t q a} (h : step M c = none) :
    step (seq M N) (c.mapState (Fin.castAdd r)) =
      some { state := Fin.natAdd q N.start, head := c.head, tape := c.tape } := by
  unfold step at h ⊢
  simp only [seq, Config.mapState, Fin.addCases_left]
  cases ht : M.transition c.state (fun i => c.tape i (c.head i)) with
  | none =>
    simp only [Move.offset, add_zero]
    congr 1
    congr 1
    funext i j
    by_cases hj : j = c.head i
    · subst j; simp
    · simp [hj]
  | some v => simp [ht] at h

theorem seq_step_right (M : Program t q a) (N : Program t r a)
    (c : Config t r a) :
    step (seq M N) (c.mapState (Fin.natAdd q)) =
      (step N c).map (Config.mapState (Fin.natAdd q)) := by
  unfold step
  simp only [seq, Config.mapState, Fin.addCases_right]
  cases ht : N.transition c.state (fun i => c.tape i (c.head i)) with
  | none => rfl
  | some v => rcases v with ⟨s, action⟩; rfl

/-- Exact sequential execution, including the one-step connection. -/
theorem seq_run (M : Program t q a) (N : Program t r a)
    {c d : Config t q a} {e : Config t r a} {k l : ℕ}
    (hM : run M k c = some d) (hhalt : step M d = none)
    (hN : run N l { state := N.start, head := d.head, tape := d.tape } = some e) :
    run (seq M N) (k + 1 + l) (c.mapState (Fin.castAdd r)) =
      some (e.mapState (Fin.natAdd q)) := by
  rw [run_add, run_add]
  rw [run_simulation M (seq M N) _ (fun _ _ h => seq_step_left M N h) hM]
  simp only [Option.bind_some, run_one, seq_step_boundary M N hhalt]
  apply run_simulation N (seq M N) (Config.mapState (Fin.natAdd q)) _ hN
  intro c d h
  rw [seq_step_right, h]
  rfl

theorem seq_halt_right (M : Program t q a) (N : Program t r a)
    {c : Config t r a} (h : step N c = none) :
    step (seq M N) (c.mapState (Fin.natAdd q)) = none := by
  rw [seq_step_right, h]
  rfl

end IntegerMultBounds.Machine
