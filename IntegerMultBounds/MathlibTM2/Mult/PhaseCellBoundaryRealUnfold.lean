module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRealProjection

/-! Inverse fold and real-project the computed boundary solution for publication. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def boundaryRealUnfold : Pr P 224 Q A U := .seq preparedBoundaryUnfold boundaryRealProjection

theorem boundaryRealUnfold_exec {s : ℕ} [NeZero s] (hA : 4 ≤ A) (w : ℕ)
    (B : Finset (ZMod s)) (solution : List GaussianInt) (hlen : solution.length = B.card)
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hleft : ∀ i, S.L i = []) (hmul : ∀ i : Fin 64, S.R (boundaryFactorMulReg i) = [])
    (hcount : (S.R 116).length = B.card) (hsrc : S.R 217 = cstream A w solution)
    (hw : (S.R 160).length = w)
    (hclean : ∀ i ∈ ([184,223,208,211,201,215] : List (Fin 224)), S.R i = []) :
    let retired : List (Fin 224) := [189,191,198,204]
    let S₀ : Stacks 224 A := {S with R := fun i => if i ∈ retired then [] else S.R i}
    ∃ v' n, v'.user = v.user ∧
      n ≤ (2*(retired.map fun i => (S.R i).length).sum+9)+generatedBoundaryUnfoldCost B.card w+
        (B.card*(12*w+9)+12) ∧
      Exec body boundaryRealUnfold (mk v S) n
        (mk v' {S₀ with R := (Function.update (Function.update S₀.R 217 []) 204
          (cstream A w ((bOrder s B).map (boundarySolutionField B solution))))}) := by
  dsimp only
  let retired : List (Fin 224) := [189,191,198,204]
  let S₀ : Stacks 224 A := {S with R := fun i => if i ∈ retired then [] else S.R i}
  let S₁ : Stacks 224 A := {S₀ with R := (Function.update (Function.update S₀.R 217 []) 204
    (cstream A w (unfoldList solution)))}
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := preparedBoundaryUnfold_exec (body := body) w solution v S hleft hmul
    (by rw [hlen]; exact hcount) hsrc hw hclean
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := boundaryRealProjection_exec (body := body) hA w (unfoldList solution)
    [] v₁ S₁ (by simpa [S₁,S₀,retired,length_unfoldList,hlen] using hcount)
    (by simpa [S₁,S₀,retired] using hw) (by simp [S₁])
    (by simpa [S₁,S₀,retired] using hclean 184 (by simp)) (by simp [S₁])
    (by simpa [S₁,S₀,retired] using hclean 223 (by simp))
  have hn₁' : n₁ ≤ (2*(retired.map fun i => (S.R i).length).sum+9)+generatedBoundaryUnfoldCost B.card w := by
    simpa only [hlen] using hn₁
  have hn₂' : n₂ ≤ B.card*(12*w+9)+12 := by simpa only [length_unfoldList,hlen] using hn₂
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁' hn₂',(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  rw [boundary_unfold_field B solution hlen]
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases h204 : i = 204 <;> by_cases h217 : i = 217 <;>
    simp [S₁,S₀,retired,h204,h217]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
