module

public import IntegerMultBounds.Machine.RunWithin

/-! Sequential composition preserves one prefix predicate, including the
physical tape-preserving join between the two programs. -/
@[expose] public section
namespace IntegerMultBounds.Machine.RunWithin
variable {t q r a k l : ℕ} {M : Program t q a} {N : Program t r a}
  {H : TapePred t a} {c d : Config t q a} {e : Config t r a}

theorem seq (hM : RunWithin M H k c d) (hh : step M d = none)
    (hN : RunWithin N H l (d.tapes.start N) e) :
    RunWithin (Machine.seq M N) H (k+1+l)
      (c.mapState (Fin.castAdd r)) (e.mapState (Fin.natAdd q)) := by
  have hleft := hM.simulation (fun c => c.mapState (Fin.castAdd r))
    (fun _ _ hs => seq_step_left M N hs) (fun _ h => h)
  have hjoin := RunWithin.single (seq_step_boundary M N hh) hM.finish hM.finish
  have hright := hN.simulation (N := Machine.seq M N) (fun c => c.mapState (Fin.natAdd q))
    (by intro x y hs; rw [seq_step_right,hs,Option.map_some]) (fun _ h => h)
  exact (hleft.trans hjoin).trans hright

end IntegerMultBounds.Machine.RunWithin
