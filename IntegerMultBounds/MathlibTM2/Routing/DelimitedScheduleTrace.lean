module

public import IntegerMultBounds.MathlibTM2.Routing.DelimitedCallLoop

/-! Closed input, archive, output and spectator contents after a framed call loop. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
variable {T A : ℕ} {I : Type}

def delimitedScheduleEffect (effect : I → List (Fin (A + 4)) → List (Fin (A + 4))) :
    List I → List (Fin (A + 4)) → List (Fin (A + 4))
  | [], w => w
  | i :: is, w => delimitedScheduleEffect effect is (effect i w)

theorem delimitedScheduleBank_keep (src saved str j : Fin T)
    (frame : I → List (Fin (A + 4)))
    (effect : I → List (Fin (A + 4)) → List (Fin (A + 4))) (stages : List I)
    (hsrc : j ≠ src) (hsaved : j ≠ saved) (hstr : j ≠ str)
    (R : Fin T → List (Fin (A + 4))) :
    delimitedScheduleBank src saved str frame effect stages R j = R j := by
  induction stages generalizing R with
  | nil => rfl
  | cons i is ih =>
    rw [delimitedScheduleBank, ih]
    simp only [delimitedCallAdvanced, Function.update_of_ne hsrc,
      Function.update_of_ne hsaved, Function.update_of_ne hstr]

theorem delimitedScheduleBank_src (src saved str : Fin T) (hsa : src ≠ saved) (hss : src ≠ str)
    (frame : I → List (Fin (A + 4)))
    (effect : I → List (Fin (A + 4)) → List (Fin (A + 4))) (stages : List I)
    (R : Fin T → List (Fin (A + 4))) (hsrc : R src = delimitedScheduleInput frame stages) :
    delimitedScheduleBank src saved str frame effect stages R src = [] := by
  induction stages generalizing R with
  | nil => exact hsrc
  | cons i is ih =>
    rw [delimitedScheduleBank]
    apply ih
    simp [delimitedCallAdvanced, hsa, hss]

theorem delimitedScheduleBank_archive (src saved str : Fin T) (has : saved ≠ str)
    (frame : I → List (Fin (A + 4)))
    (effect : I → List (Fin (A + 4)) → List (Fin (A + 4))) (stages : List I)
    (R : Fin T → List (Fin (A + 4))) :
    delimitedScheduleBank src saved str frame effect stages R saved =
      (delimitedScheduleInput frame stages).reverse ++ R saved := by
  induction stages generalizing R with
  | nil => rfl
  | cons i is ih =>
    rw [delimitedScheduleBank, ih]
    simp [delimitedCallAdvanced, has, delimitedScheduleInput, List.reverse_append, List.append_assoc]

theorem delimitedScheduleBank_stream (src saved str : Fin T)
    (frame : I → List (Fin (A + 4)))
    (effect : I → List (Fin (A + 4)) → List (Fin (A + 4))) (stages : List I)
    (R : Fin T → List (Fin (A + 4))) :
    delimitedScheduleBank src saved str frame effect stages R str =
      delimitedScheduleEffect effect stages (R str) := by
  induction stages generalizing R with
  | nil => rfl
  | cons i is ih =>
    rw [delimitedScheduleBank, ih]
    simp [delimitedCallAdvanced, delimitedScheduleEffect]

end IntegerMultBounds.MathlibTM2.Routing
