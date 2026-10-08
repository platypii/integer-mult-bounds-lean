import IntegerMultBounds.Machine.Frame
import Mathlib.Logic.Equiv.Fintype

/-! A fixed finite dispatcher: a genuine halt of the front program selects a
fixed continuation from its decoded finite state. One actual stay transition
enters that continuation; no tape operation or dynamic machine construction is
hidden in the branch. -/
namespace IntegerMultBounds.Machine.FiniteDispatch
noncomputable section
variable {t q a N : ℕ}

abbrev Control (q N : ℕ) (states : Fin N → ℕ) := Fin q ⊕ (Σ pc : Fin N, Fin (states pc))
def encoding (q N : ℕ) (states : Fin N → ℕ) := Fintype.equivFin (Control q N states)

def left (states : Fin N → ℕ) (st : Fin q) := encoding q N states (.inl st)
def right (states : Fin N → ℕ) (pc : Fin N) (st : Fin (states pc)) :=
  encoding q N states (.inr ⟨pc,st⟩)

def program (M : Program t q a) (states : Fin N → ℕ)
    (family : ∀ pc, Program t (states pc) a) (select : Fin q → Option (Fin N)) :
    Program t (Fintype.card (Control q N states)) a where
  tapes_pos := M.tapes_pos
  start := left states M.start
  transition := fun st sy => match (encoding q N states).symm st with
    | .inl st => match M.transition st sy with
      | some (next,act) => some (left states next,act)
      | none => (select st).map (fun pc => (right states pc (family pc).start,fun i => (sy i,Move.stay)))
    | .inr ⟨pc,st⟩ => ((family pc).transition st sy).map (fun (next,act) => (right states pc next,act))

private theorem step_left (M : Program t q a) (states : Fin N → ℕ)
    (family : ∀ pc, Program t (states pc) a) (select : Fin q → Option (Fin N))
    (c d : Config t q a) (h : step M c = some d) :
    step (program M states family select) (c.mapState (left states)) = some (d.mapState (left states)) := by
  unfold step at h ⊢
  simp only [program,Config.mapState,left,Equiv.symm_apply_apply]
  cases he : M.transition c.state (fun i => c.tape i (c.head i)) with
  | none => simp only [he] at h; cases h
  | some act => simp only [he,Option.some.injEq] at h; subst d; rfl

private theorem boundary (M : Program t q a) (states : Fin N → ℕ)
    (family : ∀ pc, Program t (states pc) a) (select : Fin q → Option (Fin N))
    (c : Config t q a) (pc : Fin N) (hh : step M c = none) (hs : select c.state = some pc) :
    step (program M states family select) (c.mapState (left states)) =
      some ((c.tapes.start (family pc)).mapState (right states pc)) := by
  unfold step at hh ⊢
  simp only [program,Config.mapState,left,Equiv.symm_apply_apply]
  cases he : M.transition c.state (fun i => c.tape i (c.head i)) with
  | some act => simp [he] at hh
  | none =>
    simp only [hs,Option.map_some,Move.offset,add_zero,Config.tapes,Tapes.start]
    congr 1
    congr 1
    funext i z
    by_cases hz : z = c.head i <;> simp [hz]

private theorem step_right (M : Program t q a) (states : Fin N → ℕ)
    (family : ∀ pc, Program t (states pc) a) (select : Fin q → Option (Fin N))
    (pc : Fin N) (c : Config t (states pc) a) :
    step (program M states family select) (c.mapState (right states pc)) =
      (step (family pc) c).map (Config.mapState (right states pc)) := by
  unfold step
  simp only [program,Config.mapState,right,Equiv.symm_apply_apply]
  cases he : (family pc).transition c.state (fun i => c.tape i (c.head i)) <;> rfl

/-- Exact selected-continuation execution, charging the real branch transition. -/
theorem run_selected (M : Program t q a) (states : Fin N → ℕ)
    (family : ∀ pc, Program t (states pc) a) (select : Fin q → Option (Fin N))
    (v : Tapes t a) (c : Config t q a) (pc : Fin N) (d : Config t (states pc) a)
    (n m : ℕ) (hr : run M n (v.start M) = some c) (hh : step M c = none)
    (hs : select c.state = some pc) (hc : run (family pc) m (c.tapes.start (family pc)) = some d) :
    run (program M states family select) (n+1+m) (v.start (program M states family select)) =
      some (d.mapState (right states pc)) := by
  have hleft := run_simulation M (program M states family select) (Config.mapState (left states))
    (fun c d h => step_left M states family select c d h) hr
  change run (program M states family select) n (v.start (program M states family select)) = _ at hleft
  rw [run_add,run_add,hleft]
  simp only [Option.bind_some,run_one,boundary M states family select c pc hh hs]
  apply run_simulation (family pc) (program M states family select) (Config.mapState (right states pc)) _ hc
  intro x y hy
  rw [step_right,hy]
  rfl

theorem halt_selected (M : Program t q a) (states : Fin N → ℕ)
    (family : ∀ pc, Program t (states pc) a) (select : Fin q → Option (Fin N))
    (pc : Fin N) (c : Config t (states pc) a) (hh : step (family pc) c = none) :
    step (program M states family select) (c.mapState (right states pc)) = none := by
  rw [step_right,hh]
  rfl

/-- A concrete front run followed by any verified fixed continuation. -/
theorem hoare_selected (M : Program t q a) (states : Fin N → ℕ)
    (family : ∀ pc, Program t (states pc) a) (select : Fin q → Option (Fin N))
    (v : Tapes t a) (c : Config t q a) (pc : Fin N) (n B : ℕ) (post : TapePred t a)
    (hr : run M n (v.start M) = some c) (hh : step M c = none) (hs : select c.state = some pc)
    (hc : HoareTime (family pc) (fun w => w = c.tapes) post B) :
    HoareTime (program M states family select) (fun w => w = v) post (n+1+B) := by
  intro w hw
  subst w
  obtain ⟨m,d,hm,hrun,hhalt,hpost⟩ := hc c.tapes rfl
  exact ⟨n+1+m,d.mapState (right states pc),by omega,
    run_selected M states family select v c pc d n m hr hh hs hrun,
    halt_selected M states family select pc d hhalt,hpost⟩

end
end IntegerMultBounds.Machine.FiniteDispatch
