module

public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
variable {T T' A : ℕ}

/-- Perform a list of right-bank writes in program order. -/
def rightUpdates : List (Fin T × List (Fin (A+4))) → Stacks T A → Stacks T A
  | [], S => S
  | (i,xs)::writes, S => rightUpdates writes {S with R := Function.update S.R i xs}

/-- Transport an arbitrary write sequence without expanding its concrete bank. -/
theorem embOvr_rightUpdates {e : Fin T → Fin T'} (he : Function.Injective e)
    (writes : List (Fin T × List (Fin (A+4)))) (S : Stacks T A) (B : Stacks T' A) :
    embOvr e (rightUpdates writes S).get B =
      rightUpdates (writes.map (fun (i,xs) => (e i,xs))) (embOvr e S.get B) := by
  induction writes generalizing S with
  | nil => rfl
  | cons write writes ih =>
    rcases write with ⟨i,xs⟩
    rw [rightUpdates, ih, embOvr_updR he]
    rfl

end IntegerMultBounds.MathlibTM2.Host
