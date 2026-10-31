module

public import IntegerMultBounds.Machine.RunWithin
public import IntegerMultBounds.Machine.Frame

/-! The existing frame simulations also preserve every bounded prefix. -/
@[expose] public section
namespace IntegerMultBounds.Machine.RunWithin
variable {t s u q a n : ℕ} {M : Program t q a} {c d : Config t q a}

theorem extend (extra : Tapes s a) {H : TapePred (t+s) a}
    (h : RunWithin M (fun v => H (v.append extra)) n c d) :
    RunWithin (Machine.extend M s) H n (c.extend extra) (d.extend extra) := by
  apply h.simulation (fun c => c.extend extra) ?_ (fun _ h => h)
  intro x y hs
  simp only [extend_step,hs,Option.map_some]

theorem reindex (e : Fin t ≃ Fin u) {H : TapePred u a}
    (h : RunWithin M (fun v => H (v.reindex e)) n c d) :
    RunWithin (Machine.reindex M e) H n (c.reindex e) (d.reindex e) := by
  apply h.simulation (fun c => c.reindex e) ?_ (fun _ h => h)
  intro x y hs
  simp only [reindex_step,hs,Option.map_some]

end IntegerMultBounds.Machine.RunWithin
