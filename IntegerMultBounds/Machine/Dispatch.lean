import IntegerMultBounds.Machine.Loop

/-! Finite local-symbol dispatch. One literal stationary transition selects a
member of a fixed finite program family. Its chosen tag is retained in finite
control throughout execution, and the family's true halt is the dispatch halt.
The selector reads only the currently scanned symbols, not remote tape cells. -/

namespace IntegerMultBounds.Machine.Dispatch

variable {c t q a : ℕ}

/-- A family index and body state, with the final state slot reserved for entry. -/
def tag (j : Fin c) (s : Fin q) : Fin (c*q+1) := Fin.castAdd 1 (finProdFinEquiv (j,s))

/-- Both the family and selection table are fixed, independently of input size. -/
def program (hc : 0 < c) (family : Fin c → Program t q a)
    (selector : (Fin t → Fin (a+4)) → Fin c) : Program t (c*q+1) a where
  tapes_pos := (family ⟨0,hc⟩).tapes_pos
  start := Fin.natAdd (c*q) 0
  transition := fun state symbols => Fin.addCases
    (fun encoded =>
      let selected := finProdFinEquiv.symm encoded
      ((family selected.1).transition selected.2 symbols).map
        (fun (s,action) => (tag selected.1 s,action)))
    (fun _ =>
      let j := selector symbols
      some (tag j (family j).start,fun i => (symbols i,.stay))) state

/-- Dispatch itself takes exactly one transition and preserves every tape and head. -/
theorem enter (hc : 0 < c) (family : Fin c → Program t q a)
    (selector : (Fin t → Fin (a+4)) → Fin c) (v : Tapes t a)
    (j : Fin c) (hj : selector v.reads = j) :
    step (program hc family selector) (v.start (program hc family selector)) =
      some ((v.start (family j)).mapState (tag j)) := by
  unfold Tapes.reads at hj
  simp only [step,program,Tapes.start,Fin.addCases_right,hj,Config.mapState,Move.offset,add_zero]
  congr 1
  congr 1
  funext i k
  by_cases hk : k = v.head i
  · subst k; simp
  · simp [hk]

/-- Every chosen body step is an exact tagged copy of the original step. -/
theorem step_selected (hc : 0 < c) (family : Fin c → Program t q a)
    (selector : (Fin t → Fin (a+4)) → Fin c) (j : Fin c) (v : Config t q a) :
    step (program hc family selector) (v.mapState (tag j)) =
      (step (family j) v).map (fun w => w.mapState (tag j)) := by
  unfold step
  simp only [program,Config.mapState,tag,Fin.addCases_left,Equiv.symm_apply_apply]
  cases h : (family j).transition v.state (fun i => v.tape i (v.head i)) with
  | none => rfl
  | some result => rcases result with ⟨s,action⟩; rfl

theorem run_tagged (hc : 0 < c) (family : Fin c → Program t q a)
    (selector : (Fin t → Fin (a+4)) → Fin c) (j : Fin c)
    {n : ℕ} {v w : Config t q a} (h : run (family j) n v = some w) :
    run (program hc family selector) n (v.mapState (tag j)) = some (w.mapState (tag j)) := by
  apply run_simulation (family j) (program hc family selector) (fun v => v.mapState (tag j)) _ h
  intro v w hs
  rw [step_selected,hs]
  rfl

/-- Actual family execution plus the single tape-preserving selection transition. -/
theorem run_selected (hc : 0 < c) (family : Fin c → Program t q a)
    (selector : (Fin t → Fin (a+4)) → Fin c) (v : Tapes t a)
    (j : Fin c) (hj : selector v.reads = j) {n : ℕ} {w : Config t q a}
    (h : run (family j) n (v.start (family j)) = some w) :
    run (program hc family selector) (1+n) (v.start (program hc family selector)) =
      some (w.mapState (tag j)) := by
  rw [run_add,run_one,enter hc family selector v j hj]
  simp only [Option.bind_some]
  exact run_tagged hc family selector j h

theorem halt_selected (hc : 0 < c) (family : Fin c → Program t q a)
    (selector : (Fin t → Fin (a+4)) → Fin c) (j : Fin c) {w : Config t q a}
    (h : step (family j) w = none) :
    step (program hc family selector) (w.mapState (tag j)) = none := by
  rw [step_selected,h]
  rfl

theorem exact_selected (hc : 0 < c) (family : Fin c → Program t q a)
    (selector : (Fin t → Fin (a+4)) → Fin c) (v : Tapes t a)
    (j : Fin c) (hj : selector v.reads = j) {n : ℕ} {w : Config t q a}
    (hr : run (family j) n (v.start (family j)) = some w) (hh : step (family j) w = none) :
    run (program hc family selector) (1+n) (v.start (program hc family selector)) =
      some (w.mapState (tag j)) ∧
    step (program hc family selector) (w.mapState (tag j)) = none :=
  ⟨run_selected hc family selector v j hj hr,halt_selected hc family selector j hh⟩

/-- A selected family's actual Hoare contract lifts with exactly one extra step. -/
theorem hoare_selected (hc : 0 < c) (family : Fin c → Program t q a)
    (selector : (Fin t → Fin (a+4)) → Fin c) (j : Fin c)
    {pre post : TapePred t a} {bound : ℕ} (h : HoareTime (family j) pre post bound) :
    HoareTime (program hc family selector)
      (fun v => pre v ∧ selector v.reads = j) post (bound+1) := by
  rintro v ⟨hp,hj⟩
  obtain ⟨n,w,hn,hr,hh,hpost⟩ := h v hp
  exact ⟨1+n,w.mapState (tag j),by omega,run_selected hc family selector v j hj hr,
    halt_selected hc family selector j hh,hpost⟩

/-- Concrete-input specialization without changing the selected subroutine's postcondition. -/
theorem hoare_at (hc : 0 < c) (family : Fin c → Program t q a)
    (selector : (Fin t → Fin (a+4)) → Fin c) (v : Tapes t a) (j : Fin c)
    {pre post : TapePred t a} {bound : ℕ} (h : HoareTime (family j) pre post bound)
    (hp : pre v) (hj : selector v.reads = j) :
    HoareTime (program hc family selector) (fun input => input = v) post (bound+1) := by
  apply (hoare_selected hc family selector j h).consequence
  · intro input hi
    subst input
    exact ⟨hp,hj⟩
  · intro output ho
    exact ho
  · exact le_rfl

end IntegerMultBounds.Machine.Dispatch
