module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryUnfold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedResidualLift

/-! Reuse inverse folding for coordinates while protecting boundary solution words. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

def boundaryCoordinatePerm : Fin 224 ≃ Fin 224 :=
  (Equiv.swap 109 217).trans ((Equiv.swap 204 206).trans (Equiv.swap 160 115))

theorem boundaryCoordinatePerm_mul (i : Fin 64) :
    boundaryCoordinatePerm (boundaryFactorMulReg i) = boundaryFactorMulReg i := by
  have ho (j : Fin 224) (hj : 64 ≤ j.val) : boundaryFactorMulReg i ≠ j := by
    intro h
    have hv := congrArg (fun k : Fin 224 => k.val) h
    change i.val = j.val at hv
    have hi := i.isLt
    omega
  simp [boundaryCoordinatePerm,Equiv.swap_apply_def,
    ho 109 (by decide),ho 217 (by decide),ho 204 (by decide),ho 206 (by decide),ho 160 (by decide),ho 115 (by decide)]

theorem embOvr_equiv_project {T T' A : ℕ} (e : Fin T ≃ Fin T') (S : Stacks T' A) (B : Stacks T' A) :
    embOvr e (embStk e S).get B = S := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext j
    obtain ⟨i,rfl⟩ := e.surjective j
    exact embExt_apply e.injective _ _ i
  · funext j
    obtain ⟨i,rfl⟩ := e.surjective j
    exact embExt_apply e.injective _ _ i

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def boundaryCoordinateUnfold : Pr P 224 Q A U :=
  embProg boundaryCoordinatePerm Empty.elim (preparedBoundaryUnfold (P := Empty))

/-- Coordinate inverse folding leaves arithmetic width 160 and solution tape 204 untouched. -/
theorem boundaryCoordinateUnfold_exec (V : ℕ) (coordinates : List GaussianInt)
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hleft : ∀ i, S.L i = []) (hmul : ∀ i : Fin 64, S.R (boundaryFactorMulReg i) = [])
    (hcount : (S.R 116).length = coordinates.length)
    (hsrc : S.R 109 = cstream A V coordinates) (hwidth : (S.R 115).length = V)
    (hclean : ∀ i ∈ ([184,223,208,211,201,215] : List (Fin 224)), S.R i = []) :
    let retired : List (Fin 224) := [189,191,198]
    let S₀ : Stacks 224 A := {S with R := fun i => if i ∈ retired then [] else S.R i}
    ∃ v' n, v'.user = v.user ∧
      n ≤ (2*(([189,191,198,206] : List (Fin 224)).map fun i => (S.R i).length).sum+9)+
        generatedBoundaryUnfoldCost coordinates.length V ∧
      Exec body boundaryCoordinateUnfold (mk v S) n
        (mk v' {S₀ with R := (Function.update (Function.update S₀.R 109 []) 206
          (cstream A V (unfoldList coordinates)))}) := by
  dsimp only
  let e := boundaryCoordinatePerm
  let B := embStk e S
  have hc : ∀ i ∈ ([184,223,208,211,201,215] : List (Fin 224)), B.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [B,e,embStk,boundaryCoordinatePerm,Equiv.swap_apply_def] using hclean _ (by simp)
  have hm : ∀ i : Fin 64, B.R (boundaryFactorMulReg i) = [] := by
    intro i
    simpa only [B,embStk,Function.comp_apply,e,boundaryCoordinatePerm_mul] using hmul i
  obtain ⟨v₁,n,hu,hn,he⟩ := preparedBoundaryUnfold_exec (body := fun p : Empty => nomatch p)
    V coordinates (embDn e v) B (fun i => hleft _) hm
    (by simpa [B,e,embStk,boundaryCoordinatePerm,Equiv.swap_apply_def] using hcount)
    (by simpa [B,e,embStk,boundaryCoordinatePerm,Equiv.swap_apply_def] using hsrc)
    (by simpa [B,e,embStk,boundaryCoordinatePerm,Equiv.swap_apply_def] using hwidth) hc
  let retired : List (Fin 224) := [189,191,198]
  let S₀ : Stacks 224 A := {S with R := fun i => if i ∈ retired then [] else S.R i}
  let S' : Stacks 224 A := {S₀ with R := (Function.update (Function.update S₀.R 109 []) 206
    (cstream A V (unfoldList coordinates)))}
  have hproject : embStk e S' =
      {{B with R := fun i => if i ∈ ([189,191,198,204] : List (Fin 224)) then [] else B.R i} with
        R := (Function.update (Function.update
          (fun i => if i ∈ ([189,191,198,204] : List (Fin 224)) then [] else B.R i) 217 []) 204
          (cstream A V (unfoldList coordinates)))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    have heq (j k : Fin 224) (hk : e k = j) : e i = j ↔ i = k := by
      rw [← hk]
      exact e.injective.eq_iff
    have h109 := heq 109 217 (by rfl)
    have h206 := heq 206 204 (by rfl)
    have h189 := heq 189 189 (by rfl)
    have h191 := heq 191 191 (by rfl)
    have h198 := heq 198 198 (by rfl)
    by_cases hi217 : i = 217
    · subst i
      simp [S',S₀,B,embStk,Function.comp_def,retired,Function.update_apply,
        e,boundaryCoordinatePerm,Equiv.swap_apply_def]
    · by_cases hi204 : i = 204
      · subst i
        simp [S',S₀,B,embStk,Function.comp_def,retired,Function.update_apply,
          e,boundaryCoordinatePerm,Equiv.swap_apply_def]
      · simp [S',S₀,B,embStk,Function.comp_def,retired,Function.update_apply,
          h109,h206,h189,h191,h198,hi217,hi204]
  rw [← hproject] at he
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body) e.injective
    (fun p : Empty => nomatch p) he v rfl S rfl
  rw [embOvr_equiv_project] at he₂
  refine ⟨v₂,n,hu₂.trans hu,?_,he₂⟩
  simpa [B,e,embStk,boundaryCoordinatePerm,Equiv.swap_apply_def] using hn

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
