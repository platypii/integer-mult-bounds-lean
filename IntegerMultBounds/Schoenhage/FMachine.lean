import IntegerMultBounds.Machine.Hoare

/-! Machines whose finite control is an arbitrary finite type. A machine over
a `Fintype` of states compiles to a literal `Program` by numbering its states;
runs correspond step for step, so contracts proved for the finite-type
machine hold for the program with the same bound. -/

namespace IntegerMultBounds.Schoenhage

open Machine

/-- A multitape machine with a finite type of control states. -/
structure FMachine (t a : ℕ) where
  S : Type
  [fin : Fintype S]
  [dec : DecidableEq S]
  start : S
  δ : S → (Fin t → Fin (a + 4)) → Option (S × (Fin t → Fin (a + 4) × Move))

attribute [instance] FMachine.fin FMachine.dec

namespace FMachine

variable {t a : ℕ} (M : FMachine t a)

/-- A configuration: control state and complete tapes. -/
structure Cfg where
  state : M.S
  tapes : Tapes t a

/-- One transition, with the same tape update as `Machine.step`. -/
def fstep (c : M.Cfg) : Option M.Cfg :=
  match M.δ c.state (fun i => c.tapes.tape i (c.tapes.head i)) with
  | none => none
  | some (s, act) => some ⟨s, ⟨fun i => c.tapes.head i + (act i).2.offset,
      fun i j => if j = c.tapes.head i then (act i).1 else c.tapes.tape i j⟩⟩

/-- Exactly `k` transitions. -/
def frun : ℕ → M.Cfg → Option M.Cfg
  | 0, c => some c
  | k + 1, c => (M.fstep c).bind (frun k)

theorem frun_add (k l : ℕ) (c : M.Cfg) :
    M.frun (k + l) c = (M.frun k c).bind (M.frun l) := by
  induction k generalizing c with
  | zero => simp [frun]
  | succ k ih =>
    rw [show k + 1 + l = (k + l) + 1 by omega]
    simp only [frun]
    cases M.fstep c with
    | none => rfl
    | some d => simp [ih]

theorem frun_one (c : M.Cfg) : M.frun 1 c = M.fstep c := by
  simp only [frun]; cases M.fstep c <;> rfl

/-- Number the states. -/
noncomputable def toProgram (ht : 0 < t) : Program t (Fintype.card M.S) a where
  tapes_pos := ht
  start := Fintype.equivFin M.S M.start
  transition s syms := (M.δ ((Fintype.equivFin M.S).symm s) syms).map
    fun p => (Fintype.equivFin M.S p.1, p.2)

/-- The numbered configuration. -/
noncomputable def Cfg.toConfig {M : FMachine t a} (c : M.Cfg) : Config t (Fintype.card M.S) a :=
  ⟨Fintype.equivFin M.S c.state, c.tapes.head, c.tapes.tape⟩

theorem step_toProgram (ht : 0 < t) (c : M.Cfg) :
    step (M.toProgram ht) c.toConfig = (M.fstep c).map Cfg.toConfig := by
  unfold step fstep toProgram Cfg.toConfig
  simp only [Equiv.symm_apply_apply]
  cases M.δ c.state (fun i => c.tapes.tape i (c.tapes.head i)) with
  | none => rfl
  | some p => rfl

theorem run_toProgram (ht : 0 < t) (k : ℕ) (c : M.Cfg) :
    run (M.toProgram ht) k c.toConfig = (M.frun k c).map Cfg.toConfig := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    simp only [run, frun, step_toProgram]
    cases M.fstep c with
    | none => rfl
    | some d => simp [ih]

/-- A contract for the finite-type machine is a contract for its program. -/
theorem hoare (ht : 0 < t) {pre post : TapePred t a} {bound : ℕ}
    (h : ∀ v, pre v → ∃ k c, k ≤ bound ∧ M.frun k ⟨M.start, v⟩ = some c ∧
      M.fstep c = none ∧ post c.tapes) :
    HoareTime (M.toProgram ht) pre post bound := by
  intro v hv
  obtain ⟨k, c, hk, hr, hh, hp⟩ := h v hv
  refine ⟨k, c.toConfig, hk, ?_, ?_, hp⟩
  · have := M.run_toProgram ht k ⟨M.start, v⟩
    rw [hr] at this
    exact this
  · rw [step_toProgram, hh]; rfl

end FMachine

end IntegerMultBounds.Schoenhage
