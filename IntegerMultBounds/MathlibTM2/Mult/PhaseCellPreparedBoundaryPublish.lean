module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryPublish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryCoordinatePrepare

/-! Publish directly from the retained folded coordinate page and solved boundary words. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def preparedBoundaryPublish : Pr P 224 Q A U := .seq prepareBoundaryCoordinates generatedBoundaryPublish

theorem preparedBoundaryPublish_exec (hA : 4 ≤ A) (s : ℕ) [NeZero s] (B : Finset (ZMod s))
    (V w : ℕ) (hw : 1 ≤ w) (hsV : s ≤ 2^V)
    (G : ZMod s → GaussianInt) (hoff : ∀ i ∉ B, G i = 0)
    (sourceTail : List (Fin (A+4))) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hleft : ∀ i, S.L i = []) (hmul : ∀ i : Fin 64, S.R (boundaryFactorMulReg i) = [])
    (hs : (S.R 97).length = s) (hwidth : (S.R 160).length = w) (hV : (S.R 115).length = V)
    (hc : S.R 116 = List.replicate B.card tick)
    (hcoords : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))))
    (hsrc : S.R 204 = cstream A w ((bOrder s B).map G)++sourceTail)
    (hclean : ∀ i ∈ ([0,1,2,3,4,5,6,7,8,9,184,217,223,201,208,211,215,220,206] : List (Fin 224)), S.R i = []) :
    let S₀ : Stacks 224 A := {S with R := fun i => if i ∈ ([189,191,198] : List (Fin 224)) then [] else S.R i}
    ∃ v' n, v'.user = v.user ∧
      n ≤ (2*(([189,191,198,206] : List (Fin 224)).map fun i => (S.R i).length).sum+9)+
        generatedBoundaryUnfoldCost B.card V+(4*(B.card*V)+4)+
        generateBoundaryAdvancesCost B.card V w s+93*s*w+45 ∧
      Exec body preparedBoundaryPublish (mk v S) n
        (mk v' {S₀ with R := (Function.update (Function.update (Function.update (Function.update S₀.R
          109 []) 206 []) 204 sourceTail) 132 (cstream A w (chirpLine s G)++S.R 132))}) := by
  dsimp only
  let S₀ : Stacks 224 A := {S with R := fun i => if i ∈ ([189,191,198] : List (Fin 224)) then [] else S.R i}
  let S₁ : Stacks 224 A := {S₀ with R := (Function.update (Function.update S₀.R 206 []) 109
    (cstream A V ((bOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))))}
  have hsmall : ∀ i ∈ ([184,223,208,211,201,215] : List (Fin 224)), S.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hclean _ (by simp)
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := prepareBoundaryCoordinates_exec (body := body) s B V v S hleft hmul
    (by rw [hc]; simp) hcoords hV (hclean 217 (by simp)) hsmall
  have hz : ∀ i ∈ ([0,1,2,3,4,5,6,7,8,9,184,217,223,201,208,211,215,220,206] : List (Fin 224)), S₁.R i = [] := by
    intro i hi
    by_cases h206 : i = 206
    · subst i; simp [S₁]
    · have h109 : i ≠ 109 := by intro h; subst i; norm_num at hi
      dsimp only [S₁]
      rw [Function.update_of_ne h109,Function.update_of_ne h206]
      change (if i ∈ ([189,191,198] : List (Fin 224)) then [] else S.R i) = []
      split_ifs
      · rfl
      · exact hclean i hi
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := generatedBoundaryPublish_exec (body := body) hA s B V w hw hsV G hoff
    [] sourceTail v₁ S₁ (by simpa [S₁,S₀] using hs) (by simpa [S₁,S₀] using hwidth)
    (by simpa [S₁,S₀] using hV) (by simpa [S₁,S₀] using hc) (by simp [S₁])
    (by simpa [S₁,S₀] using hsrc) hz
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · simpa only [Nat.add_assoc] using Nat.add_le_add hn₁ hn₂
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h109 : i = 109 <;> by_cases h206 : i = 206 <;> by_cases h204 : i = 204 <;>
      by_cases h132 : i = 132 <;> simp [S₁,S₀,h109,h206,h204,h132]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
