import IntegerMultBounds.Machine.Loop

/-!
A finite-state conditional whose test reads only the currently scanned
symbols. One transition enters the selected branch, preserving every tape and
head; the branch then runs to its own halt, which halts the whole machine.
The contract charges the larger branch bound plus the one control step.
-/

namespace IntegerMultBounds.Machine

variable {t q r a : ℕ}

/-- The selected branch is entered in one transition; `q + r + 1` states. -/
def branch (test : (Fin t → Fin (a + 4)) → Bool) (M : Program t q a) (N : Program t r a) :
    Program t (q + r + 1) a where
  tapes_pos := M.tapes_pos
  start := Fin.natAdd (q + r) 0
  transition := fun s symbols => Fin.addCases
    (fun u => Fin.addCases
      (fun u => (M.transition u symbols).map fun (v, action) =>
        (Fin.castAdd 1 (Fin.castAdd r v), action))
      (fun u => (N.transition u symbols).map fun (v, action) =>
        (Fin.castAdd 1 (Fin.natAdd q v), action)) u)
    (fun _ => if test symbols then
        some (Fin.castAdd 1 (Fin.castAdd r M.start), fun i => (symbols i, .stay))
      else some (Fin.castAdd 1 (Fin.natAdd q N.start), fun i => (symbols i, .stay))) s

/-- The states of the first branch inside the conditional. -/
def leftState (q r : ℕ) : Fin q → Fin (q + r + 1) := fun v => Fin.castAdd 1 (Fin.castAdd r v)

/-- The states of the second branch inside the conditional. -/
def rightState (q r : ℕ) : Fin r → Fin (q + r + 1) := fun v => Fin.castAdd 1 (Fin.natAdd q v)

theorem branch_step_left (test) (M : Program t q a) (N : Program t r a) (c : Config t q a) :
    step (branch test M N) (c.mapState (leftState q r)) =
      (step M c).map (Config.mapState (leftState q r)) := by
  unfold step
  simp only [branch, Config.mapState, leftState, Fin.addCases_left]
  cases ht : M.transition c.state (fun i => c.tape i (c.head i)) with
  | none => rfl
  | some v => rcases v with ⟨s, action⟩; rfl

theorem branch_step_right (test) (M : Program t q a) (N : Program t r a) (c : Config t r a) :
    step (branch test M N) (c.mapState (rightState q r)) =
      (step N c).map (Config.mapState (rightState q r)) := by
  unfold step
  simp only [branch, Config.mapState, rightState, Fin.addCases_left, Fin.addCases_right]
  cases ht : N.transition c.state (fun i => c.tape i (c.head i)) with
  | none => rfl
  | some v => rcases v with ⟨s, action⟩; rfl

theorem branch_step_enter_true (test) (M : Program t q a) (N : Program t r a) (v : Tapes t a)
    (h : test v.reads = true) :
    step (branch test M N) (v.start (branch test M N)) =
      some ((v.start M).mapState (leftState q r)) := by
  unfold Tapes.reads at h
  simp only [step, Tapes.start, branch, Fin.addCases_right, h, ↓reduceIte, Config.mapState,
    leftState, Move.offset, add_zero]
  congr 1
  congr 1
  funext i j
  by_cases hj : j = v.head i
  · subst j; simp
  · simp [hj]

theorem branch_step_enter_false (test) (M : Program t q a) (N : Program t r a) (v : Tapes t a)
    (h : test v.reads = false) :
    step (branch test M N) (v.start (branch test M N)) =
      some ((v.start N).mapState (rightState q r)) := by
  unfold Tapes.reads at h
  simp only [step, Tapes.start, branch, Fin.addCases_right, h, Bool.false_eq_true, ↓reduceIte,
    Config.mapState, rightState, Move.offset, add_zero]
  congr 1
  congr 1
  funext i j
  by_cases hj : j = v.head i
  · subst j; simp
  · simp [hj]

/-- Each branch is proved under the precondition strengthened by its test
outcome; the conditional meets the common postcondition. -/
theorem branch_hoare (test) {M : Program t q a} {N : Program t r a}
    {pre post : TapePred t a} {bM bN : ℕ}
    (hM : HoareTime M (fun v => pre v ∧ test v.reads = true) post bM)
    (hN : HoareTime N (fun v => pre v ∧ test v.reads = false) post bN) :
    HoareTime (branch test M N) pre post (max bM bN + 1) := by
  intro v hv
  cases h : test v.reads with
  | true =>
    obtain ⟨k, c, hk, hr, hh, hp⟩ := hM v ⟨hv, h⟩
    refine ⟨1 + k, c.mapState (leftState q r), by omega, ?_, ?_, hp⟩
    · rw [run_add, run_one, branch_step_enter_true test M N v h]
      simp only [Option.bind_some]
      exact run_simulation M (branch test M N) (Config.mapState (leftState q r))
        (fun c d h => by rw [branch_step_left, h]; rfl) hr
    · rw [branch_step_left, hh]; rfl
  | false =>
    obtain ⟨k, c, hk, hr, hh, hp⟩ := hN v ⟨hv, h⟩
    refine ⟨1 + k, c.mapState (rightState q r), by omega, ?_, ?_, hp⟩
    · rw [run_add, run_one, branch_step_enter_false test M N v h]
      simp only [Option.bind_some]
      exact run_simulation N (branch test M N) (Config.mapState (rightState q r))
        (fun c d h => by rw [branch_step_right, h]; rfl) hr
    · rw [branch_step_right, hh]; rfl

end IntegerMultBounds.Machine
