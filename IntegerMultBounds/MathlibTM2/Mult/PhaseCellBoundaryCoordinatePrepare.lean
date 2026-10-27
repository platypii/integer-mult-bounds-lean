module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryCoordinateUnfold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryCoordinateData

/-! Put retained coordinates in ascending order for runtime publication controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def prepareBoundaryCoordinates : Pr P 224 Q A U :=
  .seq boundaryCoordinateUnfold (.seq (moveR 206 217 id) (moveR 217 109 id))

theorem prepareBoundaryCoordinates_exec (s : ℕ) [NeZero s] (B : Finset (ZMod s)) (V : ℕ)
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hleft : ∀ i, S.L i = []) (hmul : ∀ i : Fin 64, S.R (boundaryFactorMulReg i) = [])
    (hcount : (S.R 116).length = B.card)
    (hsrc : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))))
    (hwidth : (S.R 115).length = V) (h217 : S.R 217 = [])
    (hclean : ∀ i ∈ ([184,223,208,211,201,215] : List (Fin 224)), S.R i = []) :
    let S₀ : Stacks 224 A := {S with R := fun i => if i ∈ ([189,191,198] : List (Fin 224)) then [] else S.R i}
    ∃ v' n, v'.user = v.user ∧
      n ≤ (2*(([189,191,198,206] : List (Fin 224)).map fun i => (S.R i).length).sum+9)+
        generatedBoundaryUnfoldCost B.card V+(4*(B.card*V)+4) ∧
      Exec body prepareBoundaryCoordinates (mk v S) n
        (mk v' {S₀ with R := (Function.update (Function.update S₀.R 206 []) 109
          (cstream A V ((bOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))))}) := by
  dsimp only
  let coordinates := (bFoldOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))
  let output := cstream A V ((bOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))
  let S₀ : Stacks 224 A := {S with R := fun i => if i ∈ ([189,191,198] : List (Fin 224)) then [] else S.R i}
  let S₁ : Stacks 224 A := {S₀ with R := Function.update (Function.update S₀.R 109 []) 206 output}
  have hlen : coordinates.length = B.card := by simp [coordinates,bFoldOrder]
  have houtlen : output.length = B.card*V := by simp [output,bOrder_length]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := boundaryCoordinateUnfold_exec (body := body) V coordinates v S hleft hmul
    (by rw [hlen]; exact hcount) hsrc hwidth hclean
  have he₁' : Exec body boundaryCoordinateUnfold (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [coordinates,boundary_unfold_coordinates] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body 206 217 (by decide) id v₁ S₁
  let S₂ : Stacks 224 A := {S₁ with R := Function.update (Function.update S₁.R 206 []) 217 output.reverse}
  have he₂' : Exec body (moveR 206 217 id) (mk v₁ S₁) (2*(B.card*V)+2) (mk v₂ S₂) := by
    simpa [S₂,S₁,S₀,movedR,output,h217,bOrder_length] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body 217 109 (by decide) id v₂ S₂
  have he₃' : Exec body (moveR 217 109 id) (mk v₂ S₂) (2*(B.card*V)+2)
      (mk v₃ {S₂ with R := Function.update (Function.update S₂.R 217 []) 109 output}) := by
    simpa [S₂,S₁,movedR,houtlen] using he₃
  rw [hlen] at hn₁
  refine ⟨v₃,n₁+((2*(B.card*V)+2)+(2*(B.card*V)+2)),hu₃.trans (hu₂.trans hu₁),
    by omega,(Exec.seq he₁' (Exec.seq he₂' he₃')).cast rfl ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases h109 : i = 109 <;> by_cases h206 : i = 206 <;> by_cases h217' : i = 217 <;>
    simp [S₂,S₁,S₀,output,h109,h206,h217',h217]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
