module

public import IntegerMultBounds.MathlibTM2.Routing.DelimitedCallLoop

/-! Closed input, archive, output and spectator contents after a framed call loop. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
variable {T A : ℕ} {I : Type}

/-- Consecutive restoring calls have one compact cursor/archive boundary.
Intermediate cursor contents and stream outputs do not survive the second call. -/
theorem delimitedCallAdvanced_comp (src saved str : Fin T)
    (hsa : src ≠ saved) (hss : src ≠ str) (has : saved ≠ str)
    (R : Fin T → List (Fin (A + 4)))
    (frame₁ rest₁ output₁ frame₂ rest₂ output₂ : List (Fin (A + 4))) :
    delimitedCallAdvanced (delimitedCallAdvanced R src saved str frame₁ rest₁ output₁)
      src saved str frame₂ rest₂ output₂ =
      delimitedCallAdvanced R src saved str (frame₁ ++ frame₂) rest₂ output₂ := by
  funext j
  by_cases hj : j = str
  · subst j
    simp only [delimitedCallAdvanced, Function.update_self]
  · by_cases ha : j = saved
    · subst j
      simp [delimitedCallAdvanced, has, List.reverse_append, List.append_assoc]
    · by_cases hs : j = src
      · subst j
        simp [delimitedCallAdvanced, hsa, hss]
      · simp [delimitedCallAdvanced, hj, ha, hs]

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

/-- A restoring scanner may accumulate a different output word per input frame.
This closed bank is shared by coordinate generation and residue filtering. -/
theorem delimitedScheduleBank_prepend (src saved dst : Fin T)
    (hsa : src ≠ saved) (hsd : src ≠ dst) (had : saved ≠ dst)
    (frame output : I → List (Fin (A + 4))) (stages : List I)
    (R : Fin T → List (Fin (A + 4))) (hsrc : R src = delimitedScheduleInput frame stages) :
    delimitedScheduleBank src saved dst frame (fun i w => (output i).reverse ++ w) stages R =
      Function.update (Function.update (Function.update R src []) saved
        ((delimitedScheduleInput frame stages).reverse ++ R saved)) dst
        ((stages.flatMap output).reverse ++ R dst) := by
  induction stages generalizing R with
  | nil =>
    simp only [delimitedScheduleBank, delimitedScheduleInput, List.flatMap_nil, List.reverse_nil, List.nil_append] at hsrc ⊢
    rw [← hsrc, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self]
  | cons i stages ih =>
    rw [delimitedScheduleBank, ih _ (by simp [delimitedCallAdvanced, hsa, hsd])]
    funext j
    by_cases hd : j = dst
    · subst j
      simp [delimitedCallAdvanced, delimitedScheduleInput, List.reverse_append, List.append_assoc]
    by_cases ha : j = saved
    · subst j
      simp [delimitedCallAdvanced, delimitedScheduleInput, List.reverse_append, List.append_assoc, had]
    by_cases hs : j = src
    · subst j
      simp [delimitedCallAdvanced, delimitedScheduleInput, hsa, hsd]
    · simp [delimitedCallAdvanced, hd, ha, hs]

end IntegerMultBounds.MathlibTM2.Routing
