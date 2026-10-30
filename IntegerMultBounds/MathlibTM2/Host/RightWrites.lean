module

public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Transport a structural sequence of right-stack writes through an embedding. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Stack

variable {T T' A : ℕ}

def writeRight (writes : List (Fin T × List (Fin (A+4)))) (S : Stacks T A) : Stacks T A :=
  match writes with
  | [] => S
  | (i,xs)::writes => writeRight writes {S with R := Function.update S.R i xs}


/-- Writes to other right stacks preserve a spectator stack. -/
theorem writeRight_R_off (writes : List (Fin T × List (Fin (A+4))))
    (S : Stacks T A) (k : Fin T) (hk : ∀ w ∈ writes, w.1 ≠ k) :
    (writeRight writes S).R k = S.R k := by
  induction writes generalizing S with
  | nil => rfl
  | cons w writes ih =>
    obtain ⟨i,xs⟩ := w
    rw [writeRight,ih _ (fun w hw => hk w (List.mem_cons_of_mem _ hw))]
    exact Function.update_of_ne (hk (i,xs) (by simp)).symm _ _

theorem embOvr_writeRight {e : Fin T → Fin T'} (he : Function.Injective e)
    (writes : List (Fin T × List (Fin (A+4)))) (B : Stacks T A) (S : Stacks T' A) :
    embOvr e (writeRight writes B).get S =
      writeRight (writes.map (fun (i,xs) => (e i,xs))) (embOvr e B.get S) := by
  induction writes generalizing B with
  | nil => rfl
  | cons w writes ih =>
    obtain ⟨i,xs⟩ := w
    simp only [writeRight,List.map_cons,ih,embOvr_updR he]

theorem embOvr_writeRight_view {e : Fin T → Fin T'} (he : Function.Injective e)
    (writes : List (Fin T × List (Fin (A+4)))) (S : Stacks T' A) :
    embOvr e (writeRight writes (embStk e S)).get S =
      writeRight (writes.map (fun (i,xs) => (e i,xs))) S := by
  rw [embOvr_writeRight he,embOvr_stk]

end IntegerMultBounds.MathlibTM2.Host
