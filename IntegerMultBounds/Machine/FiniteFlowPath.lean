import IntegerMultBounds.Machine.FiniteFlow

/-! Nonhalting paths between block entries in one fixed cyclic controller.
A recursive child returns to its caller continuation, rather than halting the
whole machine. Paths compose across nesting and can precede the root's genuine
halting trace. Every physical block join is included in the runtime. -/
namespace IntegerMultBounds.Machine.FiniteFlowPath
noncomputable section
open FiniteFlow
variable {N t a : ℕ} {states : Fin N → ℕ}
variable {family : ∀ pc,Program t (states pc) a} {next : Next states}

inductive Path (family : ∀ pc,Program t (states pc) a) (next : Next states) :
    Fin N → Tapes t a → ℕ → Fin N → Tapes t a → Prop where
  | nil (pc : Fin N) (v : Tapes t a) : Path family next pc v 0 pc v
  | join (pc pc' last : Fin N) (v w : Tapes t a) (n m : ℕ)
      (c : Config t (states pc) a)
      (run : Machine.run (family pc) n (v.start (family pc))=some c)
      (halt : step (family pc) c=none) (edge : next pc c.state=some pc')
      (tail : Path family next pc' c.tapes m last w) :
      Path family next pc v (n+1+m) last w

/-- A nonhalting child/caller path uses the unchanged fixed transition table. -/
theorem path_run (entry : Fin N) {pc last : Fin N} {v w : Tapes t a} {n : ℕ}
    (h : Path family next pc v n last w) :
    run (program family next entry) n ((v.start (family pc)).mapState (embed states pc))=
      some ((w.start (family last)).mapState (embed states last)) := by
  induction h with
  | nil pc v => rfl
  | join pc pc' last v w n m c hr hh he tail ih =>
    rw [run_add,run_add,block_run family next entry pc n _ _ hr]
    simp only [Option.bind_some,run_one,FiniteFlow.jump family next entry pc pc' c hh he]
    exact ih

/-- Nested calls and returns concatenate without a new machine or an extra
unaccounted join: both paths already end/start at the same block entry. -/
theorem append {pc mid last : Fin N} {v w z : Tapes t a} {n m : ℕ}
    (h : Path family next pc v n mid w) (tail : Path family next mid w m last z) :
    Path family next pc v (n+m) last z := by
  induction h with
  | nil pc v => simpa only [Nat.zero_add] using tail
  | join pc pc' mid v w n k c hr hh he rest ih =>
    have hp := Path.join pc pc' last v z n (k+m) c hr hh he (ih tail)
    simpa only [Nat.add_assoc] using hp

/-- A concrete halted block and its real finite-control edge give a single
nonhalting path step, including the one physical jump transition. -/
theorem block_path (pc pc' : Fin N) (v : Tapes t a) (n : ℕ)
    (c : Config t (states pc) a)
    (hr : run (family pc) n (v.start (family pc))=some c)
    (hh : step (family pc) c=none) (he : next pc c.state=some pc') :
    Path family next pc v (n+1) pc' c.tapes := by
  simpa only [Nat.add_zero] using
    Path.join pc pc' pc' v c.tapes n 0 c hr hh he (Path.nil pc' c.tapes)

/-- Child return paths precede a genuine root halting trace. This is structural
composition of local execution evidence, not a supplied complete run. -/
theorem append_trace {pc mid last : Fin N} {v w : Tapes t a} {n m : ℕ}
    {c : Config t (states last) a}
    (h : Path family next pc v n mid w) (tail : Trace family next mid w m last c) :
    Trace family next pc v (n+m) last c := by
  induction h with
  | nil pc v => simpa only [Nat.zero_add] using tail
  | join pc pc' mid v w n k d hr hh he rest ih =>
    have ht := Trace.join pc pc' last v n (k+m) d c hr hh he (ih tail)
    simpa only [Nat.add_assoc] using ht

/-- The final root proof obtains real halting and the sum of path and terminal
costs on this one fixed controller. -/
theorem path_then_trace_hoare {pc mid last : Fin N} {v w : Tapes t a} {n m : ℕ}
    {c : Config t (states last) a}
    (h : Path family next pc v n mid w) (tail : Trace family next mid w m last c) :
    HoareTime (program family next pc) (fun z => z=v) (fun z => z=c.tapes) (n+m) :=
  trace_hoare family next (append_trace h tail)

end
end IntegerMultBounds.Machine.FiniteFlowPath
