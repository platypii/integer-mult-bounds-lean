import IntegerMultBounds.Machine.Hoare

/-! Embed a program in a larger fixed tape bank. Extra tapes are preserved
literally, including their heads and arbitrary contents, at no runtime cost.
Unlike a one-sided marked-tape model, idle tapes need no parking invariant. -/

namespace IntegerMultBounds.Machine

variable {t q a s : ℕ}

def Tapes.append (v : Tapes t a) (extra : Tapes s a) : Tapes (t + s) a where
  head := Fin.addCases v.head extra.head
  tape := Fin.addCases v.tape extra.tape

def Config.extend (c : Config t q a) (extra : Tapes s a) : Config (t + s) q a :=
  ⟨c.state, (c.tapes.append extra).head, (c.tapes.append extra).tape⟩

/-- Extra tapes are read back and kept stationary in each real transition. -/
def extend (M : Program t q a) (s : ℕ) : Program (t + s) q a where
  tapes_pos := by have := M.tapes_pos; omega
  start := M.start
  transition := fun state symbols =>
    (M.transition state (fun i => symbols (Fin.castAdd s i))).map
      (fun (state', action) =>
        (state', Fin.addCases action (fun i => (symbols (Fin.natAdd t i), .stay))))

/-- A step on the larger bank is exactly the smaller step with its frame. -/
theorem extend_step (M : Program t q a) (c : Config t q a) (extra : Tapes s a) :
    step (extend M s) (c.extend extra) = (step M c).map (fun d => d.extend extra) := by
  unfold step
  simp only [extend, Config.extend, Config.tapes, Tapes.append, Fin.addCases_left]
  cases ht : M.transition c.state (fun i => c.tape i (c.head i)) with
  | none => rfl
  | some v =>
    rcases v with ⟨state', action⟩
    simp only [Option.map_some]
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
        by_cases hj : j = extra.head i
        · subst j; simp
        · simp [hj]

/-- An arbitrary extra tape bank survives the entire run at unchanged cost. -/
theorem extend_run (M : Program t q a) (extra : Tapes s a)
    {c d : Config t q a} {k : ℕ} (h : run M k c = some d) :
    run (extend M s) k (c.extend extra) = some (d.extend extra) := by
  apply run_simulation M (extend M s) (fun c => c.extend extra) _ h
  intro c d hs
  rw [extend_step, hs]
  rfl

theorem extend_halt (M : Program t q a) (extra : Tapes s a)
    {c : Config t q a} (h : step M c = none) :
    step (extend M s) (c.extend extra) = none := by
  rw [extend_step, h]
  rfl

/-- Preserve arbitrary extra tapes as a frame around a time contract. -/
theorem HoareTime.extend {M : Program t q a} {pre post : TapePred t a} {b : ℕ}
    (h : HoareTime M pre post b) (extra : Tapes s a) :
    HoareTime (extend M s)
      (fun v => ∃ small, pre small ∧ v = small.append extra)
      (fun v => ∃ small, post small ∧ v = small.append extra) b := by
  rintro v ⟨small, hp, rfl⟩
  obtain ⟨k, c, hk, hr, hh, hpost⟩ := h small hp
  exact ⟨k, c.extend extra, hk, extend_run M extra hr, extend_halt M extra hh,
    c.tapes, hpost, rfl⟩

variable {u : ℕ}

def Tapes.reindex (e : Fin t ≃ Fin u) (v : Tapes t a) : Tapes u a :=
  ⟨fun i => v.head (e.symm i), fun i => v.tape (e.symm i)⟩

def Config.reindex (e : Fin t ≃ Fin u) (c : Config t q a) : Config u q a :=
  ⟨c.state, fun i => c.head (e.symm i), fun i => c.tape (e.symm i)⟩

/-- Relabel physical tapes in the finite transition table. Combined with
`extend`, this places a fixed subroutine in any chosen tape slots. -/
def reindex (M : Program t q a) (e : Fin t ≃ Fin u) : Program u q a where
  tapes_pos := lt_of_le_of_lt (Nat.zero_le _) (e ⟨0, M.tapes_pos⟩).isLt
  start := M.start
  transition := fun state symbols =>
    (M.transition state (fun i => symbols (e i))).map
      (fun (state', action) => (state', fun i => action (e.symm i)))

theorem reindex_step (M : Program t q a) (e : Fin t ≃ Fin u) (c : Config t q a) :
    step (reindex M e) (c.reindex e) = (step M c).map (Config.reindex e) := by
  unfold step
  simp only [reindex, Config.reindex, Equiv.symm_apply_apply]
  cases ht : M.transition c.state (fun i => c.tape i (c.head i)) with
  | none => rfl
  | some v => rcases v with ⟨state', action⟩; rfl

theorem reindex_run (M : Program t q a) (e : Fin t ≃ Fin u)
    {c d : Config t q a} {k : ℕ} (h : run M k c = some d) :
    run (reindex M e) k (c.reindex e) = some (d.reindex e) := by
  apply run_simulation M (reindex M e) (Config.reindex e) _ h
  intro c d hs
  rw [reindex_step, hs]
  rfl

theorem reindex_halt (M : Program t q a) (e : Fin t ≃ Fin u)
    {c : Config t q a} (h : step M c = none) :
    step (reindex M e) (c.reindex e) = none := by
  rw [reindex_step, h]
  rfl

theorem HoareTime.reindex {M : Program t q a} {pre post : TapePred t a} {b : ℕ}
    (h : HoareTime M pre post b) (e : Fin t ≃ Fin u) :
    HoareTime (reindex M e)
      (fun v => ∃ original, pre original ∧ v = original.reindex e)
      (fun v => ∃ original, post original ∧ v = original.reindex e) b := by
  rintro v ⟨original, hp, rfl⟩
  obtain ⟨k, c, hk, hr, hh, hpost⟩ := h original hp
  exact ⟨k, c.reindex e, hk, reindex_run M e hr, reindex_halt M e hh,
    c.tapes, hpost, rfl⟩

end IntegerMultBounds.Machine
