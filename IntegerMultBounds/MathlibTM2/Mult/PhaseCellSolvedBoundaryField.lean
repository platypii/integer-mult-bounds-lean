module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolvedBoundaryUnfold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolvedBoundaryPublish

/-! Consume the computed folded solution and page to publish its ambient real field. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def solvedBoundaryField : Pr P 224 Q A U :=
  .seq solvedBoundaryUnfold solvedBoundaryPublish

def solvedBoundaryFieldCost (R : Regs 224 A) (s N V q : ℕ) : ℕ :=
  solvedBoundaryUnfoldCost R N (2*q+8)+
    (9+generatedBoundaryUnfoldCost N V+(4*(N*V)+4)+
      (generateBoundaryAdvancesCost N V (2*q+8) s+93*s*(2*q+8)+45))

theorem solvedBoundaryField_exec (hA : 4 ≤ A) (s : ℕ) [NeZero s]
    (B : Finset (ZMod s)) (V q : ℕ) (hsV : s ≤ 2^V)
    (solution : List GaussianInt) (hlen : solution.length = B.card)
    (v : HS 224 Q A U) (S : Stacks 224 A) (h : BoundaryUnscaleReady q S)
    (hs : (S.R 121).length = s) (hV : (S.R 115).length = V)
    (hN : S.R 116 = List.replicate B.card tick)
    (hcoords : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))))
    (hsource : S.R 217 = cstream A (2*q+8) solution) :
    let retired : List (Fin 224) := [189,191,198,204,217,206,109]
    let S₀ : Stacks 224 A := {S with R := fun i => if i ∈ retired then [] else S.R i}
    ∃ v' m, v'.user = v.user ∧ m ≤ solvedBoundaryFieldCost S.R s B.card V q ∧
      Exec body solvedBoundaryField (mk v S) m
        (mk v' {S₀ with R := (Function.update S₀.R 132
          (cstream A (2*q+8) (chirpLine s (boundarySolutionField B solution))++S.R 132))}) := by
  dsimp only
  let w := 2*q+8
  let G := boundarySolutionField B solution
  let S₀ : Stacks 224 A := {S with R := fun i => if i ∈ ([189,191,198,204] : List (Fin 224)) then [] else S.R i}
  let S₁ : Stacks 224 A := {S₀ with R := (Function.update (Function.update S₀.R 217 []) 204
    (cstream A w ((bOrder s B).map G)))}
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁⟩ := solvedBoundaryUnfold_exec hA q B solution hlen v S h
    (by simp only [hN,List.length_replicate]) hsource
  have hpub : BoundaryPublicationReady S₁ s B.card V w :=
    solvedBoundaryUnfold_publicationReady S h hs hV hN _
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := solvedBoundaryPublish_exec hA s B V w (by dsimp [w]; omega)
    hsV G (boundarySolutionField_off B solution) v₁ S₁ hpub
    (by simpa [S₁,S₀] using hcoords) (by simp [S₁])
  have hcost : solvedBoundaryPublishCost S₁.R s B.card V w =
      9+generatedBoundaryUnfoldCost B.card V+(4*(B.card*V)+4)+
        (generateBoundaryAdvancesCost B.card V w s+93*s*w+45) := by
    simp [solvedBoundaryPublishCost,S₁,S₀,h.clean 206 (by simp)]
  rw [hcost] at hm₂
  refine ⟨v₂,m₁+m₂,hv₂.trans hv₁,Nat.add_le_add hm₁ hm₂,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases h132 : i = 132 <;> by_cases h109 : i = 109 <;>
    by_cases h206 : i = 206 <;> by_cases h204 : i = 204 <;> by_cases h217 : i = 217 <;>
    simp [S₁,S₀,w,G,h132,h109,h206,h204,h217]
  all_goals tauto

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
