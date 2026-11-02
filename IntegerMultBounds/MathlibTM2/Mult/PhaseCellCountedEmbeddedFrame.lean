module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop
public import IntegerMultBounds.MathlibTM2.Host.RegisterFrame

/-! Structural ownership for a consuming loop around a closed embedded worker.
Both stacks of every external register are preserved. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
variable {T T' Q A : ℕ} {P U : Type}

theorem countedLoop_on_registers (count : Fin T) (p : Pr P T Q A U)
    (allowed : Fin T → Prop) (hc : allowed count) (hp : programOn (registersOn allowed) p) :
    programOn (registersOn allowed) (countedLoop count p) := by
  simp only [countedLoop,countedLoopBody,programOn]
  refine ⟨?_,?_,hp,?_⟩ <;> simp [peekR,actionOn,registersOn,hc]

theorem countedEmbedded_preserves_external (e : Fin T → Fin T') (count outside : Fin T')
    (p : Pr Empty T Q A U) (hc : count ≠ outside) (hoff : ∀ i, e i ≠ outside)
    {body : P → Pr P T' Q A U} {v v' : HS T' Q A U} {S F : Stacks T' A} {n : ℕ}
    (hex : Exec body (countedLoop count (embProg e Empty.elim p)) (mk v S) n (mk v' F)) :
    F.L outside = S.L outside ∧ F.R outside = S.R outside := by
  have hp := countedLoop_on_registers count (embProg e (Empty.elim : Empty → P) p) (fun i => i ≠ outside) hc
    (embProg_empty_on_registers e Empty.elim _ hoff p)
  exact ⟨hex.preserves_stack (HK.lt outside) (registersOn_avoids_left hp outside (by simp)),
    hex.preserves_stack (HK.rt outside) (registersOn_avoids_right hp outside (by simp))⟩

/-- The consuming counter touches only its right stack. -/
theorem countedEmbedded_preserves_external_left (e : Fin T → Fin T') (count outside : Fin T')
    (p : Pr Empty T Q A U) (hoff : ∀ i, e i ≠ outside)
    {body : P → Pr P T' Q A U} {v v' : HS T' Q A U} {S F : Stacks T' A} {n : ℕ}
    (hex : Exec body (countedLoop count (embProg e Empty.elim p)) (mk v S) n (mk v' F)) :
    F.L outside = S.L outside := by
  have hp := embProg_empty_on e (Empty.elim : Empty → P) (fun k => k ≠ HK.lt outside)
    (by intro k; cases k <;> simp [embK,hoff]) p
  apply hex.preserves_stack (HK.lt outside)
  simp only [countedLoop,countedLoopBody,programOn]
  refine ⟨?_,?_,hp,?_⟩ <;> simp [peekR,actionOn]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
