module

public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
variable {T T' A : ℕ}

/-- Perform a list of right-bank writes in program order. -/
def rightUpdates : List (Fin T × List (Fin (A+4))) → Stacks T A → Stacks T A
  | [], S => S
  | (i,xs)::writes, S => rightUpdates writes {S with R := Function.update S.R i xs}

/-- An unrelated retained write commutes with an entire generated write list. -/
theorem rightUpdates_updateR (writes : List (Fin T × List (Fin (A+4))))
    (S : Stacks T A) (i : Fin T) (xs : List (Fin (A+4)))
    (hoff : ∀ w ∈ writes, w.1 ≠ i) :
    rightUpdates writes {S with R := Function.update S.R i xs} =
      {rightUpdates writes S with R := Function.update (rightUpdates writes S).R i xs} := by
  induction writes generalizing S with
  | nil => rfl
  | cons write writes ih =>
    rcases write with ⟨j,ys⟩
    have hji : j ≠ i := hoff (j,ys) (by simp)
    have hcomm : ({S with R := Function.update (Function.update S.R i xs) j ys} : Stacks T A) =
        {S with R := Function.update (Function.update S.R j ys) i xs} := by
      congr 1
      exact Function.update_comm hji.symm xs ys S.R
    simp only [rightUpdates]
    rw [hcomm]
    exact ih {S with R := Function.update S.R j ys}
      (by intro w hw; exact hoff w (by simp [hw]))

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
