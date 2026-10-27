module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConstructedBoundaryUnscaledSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedSchurResidual

/-! Lift the retained residual's two-output execution into the physical boundary bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host

/-- Lift two output updates with an exact frame on every other physical tape. -/
theorem exec_emb_two_outputs {T T' Q A : ℕ} {U P : Type}
    (e : Fin T → Fin T') (he : Function.Injective e) (body : P → Pr P T Q A U)
    (p : Pr P T Q A U) (v : HS T' Q A U) (S : Stacks T' A)
    (v₁ : HS T Q A U) (n : ℕ) (i j : Fin T) (xs ys : List (Fin (A+4)))
    (hu : v₁.user = v.user)
    (hrun : Exec body p (mk (embDn e v) (embStk e S)) n
      (mk v₁ {(embStk e S) with R := Function.update (Function.update (embStk e S).R i xs) j ys})) :
    ∃ v', v'.user = v.user ∧ Exec (embTab e body) (embProg e id p) (mk v S) n
      (mk v' {S with R := Function.update (Function.update S.R (e i) xs) (e j) ys}) := by
  obtain ⟨v',hv',hu',hrun'⟩ := exec_emb_ovr (ι := id) (body' := embTab e body)
    he (fun _ => rfl) hrun v rfl S rfl
  refine ⟨v',hu'.trans hu,hrun'.cast rfl ?_⟩
  apply congrArg (mk v')
  let S₁ : Stacks T A := {embStk e S with R := Function.update (embStk e S).R i xs}
  change embOvr e ({S₁ with R := Function.update S₁.R j ys} : Stacks T A).get S = _
  rw [embOvr_updR he]
  dsimp only [S₁]
  rw [embOvr_updR he,embOvr_stk]

/-- The retained residual uses physical tapes 110/132 in the full solver bank. -/
theorem boundary_retained_residual_lift {Q A : ℕ} {U P : Type}
    (body : P → Pr P 148 Q A U) (p : Pr P 148 Q A U)
    (v : HS 224 Q A U) (S : Stacks 224 A) (v₁ : HS 148 Q A U) (n : ℕ)
    (xs ys : List (Fin (A+4))) (hu : v₁.user = v.user)
    (hrun : Exec body p
      (mk (embDn boundaryArithmeticReg (embDn tableReg (embDn boundaryFactorLegacyReg v)))
        (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))) n
      (mk v₁ {embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)) with
        R := Function.update (Function.update
          (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S))).R 110 xs) 132 ys})) :
    ∃ v', v'.user = v.user ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg body)))
        (embProg boundaryFactorLegacyReg id (embProg tableReg id (embProg boundaryArithmeticReg id p)))
        (mk v S) n (mk v' {S with R := Function.update (Function.update S.R 110 xs) 132 ys}) := by
  obtain ⟨v₂,hu₂,he₂⟩ := exec_emb_two_outputs boundaryArithmeticReg boundaryArithmeticReg_injective
    body p (embDn tableReg (embDn boundaryFactorLegacyReg v))
    (embStk tableReg (embStk boundaryFactorLegacyReg S)) v₁ n 110 132 xs ys hu hrun
  have he₂' : Exec (embTab boundaryArithmeticReg body) (embProg boundaryArithmeticReg id p)
      (mk (embDn tableReg (embDn boundaryFactorLegacyReg v))
        (embStk tableReg (embStk boundaryFactorLegacyReg S))) n
      (mk v₂ {embStk tableReg (embStk boundaryFactorLegacyReg S) with R := (Function.update
        (Function.update (embStk tableReg (embStk boundaryFactorLegacyReg S)).R 110 xs) 132 ys)}) := by
    simpa [boundaryArithmeticReg] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := exec_emb_two_outputs tableReg tableReg_injective
    (embTab boundaryArithmeticReg body) (embProg boundaryArithmeticReg id p)
    (embDn boundaryFactorLegacyReg v) (embStk boundaryFactorLegacyReg S) v₂ n 110 132 xs ys hu₂ he₂'
  obtain ⟨v₄,hu₄,he₄⟩ := exec_emb_two_outputs boundaryFactorLegacyReg boundaryFactorLegacyReg_injective
    (embTab tableReg (embTab boundaryArithmeticReg body))
    (embProg tableReg id (embProg boundaryArithmeticReg id p)) v S v₃ n 110 132 xs ys hu₃ he₃
  exact ⟨v₄,hu₄,he₄⟩

/-- Project an owned physical update back to its logical tape. -/
theorem embStk_updateR_inner {T T' A : ℕ} (e : Fin T → Fin T')
    (he : Function.Injective e) (S : Stacks T' A) (i : Fin T) (xs : List (Fin (A+4))) :
    embStk e {S with R := Function.update S.R (e i) xs} =
      {embStk e S with R := Function.update (embStk e S).R i xs} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext j
  by_cases h : j = i
  · subst j; simp [embStk,Function.comp_def]
  · have he' : e j ≠ e i := fun h' => h (he h')
    simp [embStk,Function.comp_def,h,he']

/-- The lifted residual's physical updates project to exactly its native poststate. -/
theorem boundary_retained_project_outputs {A : ℕ} (S : Stacks 224 A)
    (xs ys : List (Fin (A+4))) :
    embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg
      {S with R := Function.update (Function.update S.R 110 xs) 132 ys})) =
    {embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)) with
      R := Function.update (Function.update
        (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S))).R 110 xs) 132 ys} := by
  let e : Fin 148 → Fin 224 := fun i => boundaryFactorLegacyReg (tableReg (boundaryArithmeticReg i))
  have he : Function.Injective e := boundaryFactorLegacyReg_injective.comp
    (tableReg_injective.comp boundaryArithmeticReg_injective)
  have h110 : e 110 = 110 := rfl
  have h132 : e 132 = 132 := rfl
  change embStk e {S with R := Function.update (Function.update S.R 110 xs) 132 ys} =
    {embStk e S with R := Function.update (Function.update (embStk e S).R 110 xs) 132 ys}
  rw [← h110,← h132]
  let S₁ : Stacks 224 A := {S with R := Function.update S.R (e 110) xs}
  change embStk e {S₁ with R := Function.update S₁.R (e 132) ys} = _
  rw [embStk_updateR_inner e he]
  dsimp only [S₁]
  rw [embStk_updateR_inner e he]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
