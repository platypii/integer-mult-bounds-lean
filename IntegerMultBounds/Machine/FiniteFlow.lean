import IntegerMultBounds.Machine.Frame
import Mathlib.Logic.Equiv.Fintype

/-! Fixed cyclic finite block control. Every block is a concrete same-bank
machine. Its actual terminal finite state selects the next block, including
back-edges and self-calls; a join costs one physical tape-preserving transition.
No control state or tape count depends on runtime recursion depth. -/
namespace IntegerMultBounds.Machine.FiniteFlow
noncomputable section
variable {N t a : ℕ} {states : Fin N → ℕ}

abbrev Control (states : Fin N → ℕ) := Σ pc : Fin N, Fin (states pc)
theorem control_card (states : Fin N → ℕ) : Fintype.card (Control states) = ∑ pc, states pc := by
  simp [Control,Fintype.card_sigma]

def encoding (states : Fin N → ℕ) := Fintype.equivFin (Control states)
def embed (states : Fin N → ℕ) (pc : Fin N) (st : Fin (states pc)) := encoding states ⟨pc,st⟩

/-- A finite table of terminal-state-dependent edges. `none` is a genuine halt. -/
abbrev Next (states : Fin N → ℕ) := ∀ pc : Fin N, Fin (states pc) → Option (Fin N)

def program (family : ∀ pc, Program t (states pc) a) (next : Next states) (entry : Fin N) :
    Program t (Fintype.card (Control states)) a where
  tapes_pos := (family entry).tapes_pos
  start := embed states entry (family entry).start
  transition := fun st sy => match (encoding states).symm st with
    | ⟨pc,st⟩ => match (family pc).transition st sy with
      | some (st',act) => some (embed states pc st',act)
      | none => (next pc st).map (fun pc' => (embed states pc' (family pc').start,fun i => (sy i,Move.stay)))

/-- Entry changes only the start state; all cyclic transitions are fixed. -/
theorem transition_independent (family : ∀ pc, Program t (states pc) a) (next : Next states)
    (entry entry' : Fin N) :
    (program family next entry).transition = (program family next entry').transition := rfl

private theorem transition_embed (family : ∀ pc, Program t (states pc) a) (next : Next states)
    (entry pc : Fin N) (st : Fin (states pc)) (sy : Fin t → Fin (a+4)) :
    (program family next entry).transition (embed states pc st) sy =
      match (family pc).transition st sy with
      | some (st',act) => some (embed states pc st',act)
      | none => (next pc st).map (fun pc' => (embed states pc' (family pc').start,fun i => (sy i,Move.stay))) := by
  unfold program
  dsimp only
  have he : (encoding states).symm (embed states pc st) = ⟨pc,st⟩ := (encoding states).symm_apply_apply _
  rw [he]

private theorem block_step (family : ∀ pc, Program t (states pc) a) (next : Next states)
    (entry pc : Fin N) (c d : Config t (states pc) a) (h : step (family pc) c = some d) :
    step (program family next entry) (c.mapState (embed states pc)) =
      some (d.mapState (embed states pc)) := by
  unfold step at h ⊢
  simp only [Config.mapState,transition_embed]
  cases he : (family pc).transition c.state (fun i => c.tape i (c.head i)) with
  | none => simp only [he] at h; cases h
  | some act => simp only [he,Option.some.injEq] at h; subst d; rfl

theorem block_run (family : ∀ pc, Program t (states pc) a) (next : Next states)
    (entry pc : Fin N) (n : ℕ) (c d : Config t (states pc) a)
    (h : run (family pc) n c = some d) :
    run (program family next entry) n (c.mapState (embed states pc)) =
      some (d.mapState (embed states pc)) :=
  run_simulation (family pc) (program family next entry) (Config.mapState (embed states pc))
    (fun c d h => block_step family next entry pc c d h) h

/-- Every forward edge, back-edge, and self-edge is one actual transition. -/
theorem jump (family : ∀ pc, Program t (states pc) a) (next : Next states)
    (entry pc pc' : Fin N) (c : Config t (states pc) a)
    (hh : step (family pc) c = none) (hn : next pc c.state = some pc') :
    step (program family next entry) (c.mapState (embed states pc)) =
      some ((c.tapes.start (family pc')).mapState (embed states pc')) := by
  unfold step at hh ⊢
  simp only [Config.mapState,transition_embed]
  cases he : (family pc).transition c.state (fun i => c.tape i (c.head i)) with
  | some act => simp [he] at hh
  | none =>
    simp only [hn,Option.map_some,Move.offset,add_zero,Config.tapes,Tapes.start]
    congr 1
    congr 1
    funext i z
    by_cases hz : z = c.head i <;> simp [hz]

theorem halt (family : ∀ pc, Program t (states pc) a) (next : Next states)
    (entry pc : Fin N) (c : Config t (states pc) a)
    (hh : step (family pc) c = none) (hn : next pc c.state = none) :
    step (program family next entry) (c.mapState (embed states pc)) = none := by
  unfold step at hh ⊢
  simp only [Config.mapState,transition_embed]
  cases he : (family pc).transition c.state (fun i => c.tape i (c.head i)) with
  | some act => simp [he] at hh
  | none => simp [hn]

/-- Finite trace of actual block runs. PCs may repeat without restriction.
Only the final block may halt the enclosing controller. -/
inductive Trace (family : ∀ pc, Program t (states pc) a) (next : Next states) :
    (pc : Fin N) → Tapes t a → ℕ → (last : Fin N) → Config t (states last) a → Prop where
  | stop (pc : Fin N) (v : Tapes t a) (n : ℕ) (c : Config t (states pc) a)
      (run : Machine.run (family pc) n (v.start (family pc)) = some c)
      (halt : step (family pc) c = none) (exit : next pc c.state = none) :
      Trace family next pc v n pc c
  | join (pc pc' last : Fin N) (v : Tapes t a) (n m : ℕ)
      (c : Config t (states pc) a) (d : Config t (states last) a)
      (run : Machine.run (family pc) n (v.start (family pc)) = some c)
      (halt : step (family pc) c = none) (edge : next pc c.state = some pc')
      (tail : Trace family next pc' c.tapes m last d) :
      Trace family next pc v (n+1+m) last d

/-- Exact physical realization of every finite trace in this one fixed machine. -/
theorem trace_run (family : ∀ pc, Program t (states pc) a) (next : Next states) (entry : Fin N)
    {pc last : Fin N} {v : Tapes t a} {n : ℕ} {c : Config t (states last) a}
    (h : Trace family next pc v n last c) :
    run (program family next entry) n ((v.start (family pc)).mapState (embed states pc)) =
      some (c.mapState (embed states last)) ∧
    step (program family next entry) (c.mapState (embed states last)) = none := by
  induction h with
  | stop pc v n c hr hh he => exact ⟨block_run family next entry pc n _ _ hr,halt family next entry pc c hh he⟩
  | join pc pc' last v n m c d hr hh he tail ih =>
    refine ⟨?_,ih.2⟩
    rw [run_add,run_add,block_run family next entry pc n _ _ hr]
    simp only [Option.bind_some,run_one,jump family next entry pc pc' c hh he]
    exact ih.1

/-- The trace carries a concrete runtime including all actual cyclic joins. -/
theorem trace_hoare (family : ∀ pc, Program t (states pc) a) (next : Next states)
    {entry last : Fin N} {v : Tapes t a} {n : ℕ} {c : Config t (states last) a}
    (h : Trace family next entry v n last c) :
    HoareTime (program family next entry) (fun w => w = v) (fun w => w = c.tapes) n := by
  obtain ⟨hr,hh⟩ := trace_run family next entry h
  intro w hw
  subst w
  exact ⟨n,c.mapState (embed states last),le_rfl,hr,hh,rfl⟩

/-- A fixed return-address block can jump back to any entry, including itself;
this theorem exposes the literal shared tape bank at that boundary. -/
theorem block_then_jump (family : ∀ pc, Program t (states pc) a) (next : Next states)
    (entry pc pc' : Fin N) (v : Tapes t a) (n : ℕ) (c : Config t (states pc) a)
    (hr : run (family pc) n (v.start (family pc)) = some c)
    (hh : step (family pc) c = none) (he : next pc c.state = some pc') :
    run (program family next entry) (n+1) ((v.start (family pc)).mapState (embed states pc)) =
      some ((c.tapes.start (family pc')).mapState (embed states pc')) := by
  rw [run_add,block_run family next entry pc n _ _ hr]
  simp only [Option.bind_some,run_one,jump family next entry pc pc' c hh he]

end
end IntegerMultBounds.Machine.FiniteFlow
