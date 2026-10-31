module

public import IntegerMultBounds.Machine.FiniteFlow
public import IntegerMultBounds.Machine.RunWithin

/-! Bounded runs lift through finite block control and its tape-preserving
jumps. This lets recursive execution proofs reuse their existing block decomposition. -/
@[expose] public section
namespace IntegerMultBounds.Machine.FiniteFlow
noncomputable section
variable {N t a : ℕ} {states : Fin N → ℕ}
  (family : ∀ pc, Program t (states pc) a) (next : Next states) (entry : Fin N)

theorem block_within (pc : Fin N) {H : TapePred t a} {n : ℕ}
    {c d : Config t (states pc) a} (h : RunWithin (family pc) H n c d) :
    RunWithin (program family next entry) H n
      (c.mapState (embed states pc)) (d.mapState (embed states pc)) := by
  apply h.simulation (fun c => c.mapState (embed states pc)) ?_ (fun _ h => h)
  intro x y hs
  have h := block_run family next entry pc 1 x y (by simpa only [run_one] using hs)
  simpa only [run_one] using h

theorem block_then_jump_within (pc pc' : Fin N) {H : TapePred t a} {n : ℕ}
    {v : Tapes t a} {c : Config t (states pc) a}
    (hr : RunWithin (family pc) H n (v.start (family pc)) c)
    (hh : Machine.step (family pc) c = none) (he : next pc c.state = some pc') :
    RunWithin (program family next entry) H (n+1)
      ((v.start (family pc)).mapState (embed states pc))
      ((c.tapes.start (family pc')).mapState (embed states pc')) := by
  apply (block_within family next entry pc hr).trans
  exact RunWithin.single (jump family next entry pc pc' c hh he) hr.finish hr.finish

end
end IntegerMultBounds.Machine.FiniteFlow
