module

public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Lift exact single-output executions through arbitrary register embeddings. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host

variable {T T' Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem embeddedOutput_project (e : Fin T → Fin T') (he : Function.Injective e)
    (S : Stacks T' A) (k : Fin T) (output : List (Fin (A+4))) :
    embStk e {S with R := Function.update S.R (e k) output} =
      {(embStk e S) with R := Function.update (embStk e S).R k output} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi : i = k
  · subst i; simp [embStk]
  · have hne : e i ≠ e k := fun h => hi (he h)
    simp [embStk,Function.comp_def,hi,hne]

theorem embeddedOutput_exec (e : Fin T → Fin T') (he : Function.Injective e)
    (p : Pr P T Q A U) (v : HS T' Q A U) (S : Stacks T' A)
    (vi : HS T Q A U) (m : ℕ) (k : Fin T) (output : List (Fin (A+4)))
    (hex : Exec body p (mk (embDn e v) (embStk e S)) m
      (mk vi {(embStk e S) with R := Function.update (embStk e S).R k output})) :
    ∃ vf, vf.user = vi.user ∧ Exec (embTab e body) (embProg e id p) (mk v S) m
      (mk vf {S with R := Function.update S.R (e k) output}) := by
  obtain ⟨vf,_,hu,hf⟩ := exec_emb_ovr (ι := id) (body' := embTab e body)
    he (fun _ => rfl) hex v rfl S rfl
  refine ⟨vf,hu,hf.cast rfl ?_⟩
  apply congrArg (mk vf)
  rw [embOvr_updR he (embStk e S) S k output,embOvr_stk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
