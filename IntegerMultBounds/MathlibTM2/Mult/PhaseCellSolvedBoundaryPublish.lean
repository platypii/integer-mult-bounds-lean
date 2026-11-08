module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryCoordinatePrepare
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryPublish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryPublicationReady

/-! Publish the solved field using its retained folded coordinate page. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def solvedBoundaryPublish : Pr P 224 Q A U :=
  .seq prepareBoundaryCoordinates generatedBoundaryPublish

def solvedBoundaryPublishCost (R : Regs 224 A) (s N V w : ℕ) : ℕ :=
  (2*([189,191,198,206].map (fun i => (R i).length)).sum+9)+
    generatedBoundaryUnfoldCost N V+(4*(N*V)+4)+
    (generateBoundaryAdvancesCost N V w s+93*s*w+45)

theorem solvedBoundaryPublish_exec (hA : 4 ≤ A) (s : ℕ) [NeZero s]
    (B : Finset (ZMod s)) (V w : ℕ) (hw : 1 ≤ w) (hsV : s ≤ 2^V)
    (G : ZMod s → GaussianInt) (hoff : ∀ i ∉ B, G i = 0)
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (h : BoundaryPublicationReady S s B.card V w)
    (hcoords : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))))
    (hsource : S.R 204 = cstream A w ((bOrder s B).map G)) :
    let S₀ : Stacks 224 A := {S with R := fun i => if i ∈ ([189,191,198] : List (Fin 224)) then [] else S.R i}
    ∃ v' m, v'.user = v.user ∧ m ≤ solvedBoundaryPublishCost S.R s B.card V w ∧
      Exec body solvedBoundaryPublish (mk v S) m
        (mk v' {S₀ with R := (Function.update (Function.update (Function.update (Function.update S₀.R
          206 []) 109 []) 204 []) 132 (cstream A w (chirpLine s G)++S.R 132))}) := by
  dsimp only
  let S₀ : Stacks 224 A := {S with R := fun i => if i ∈ ([189,191,198] : List (Fin 224)) then [] else S.R i}
  let S₁ : Stacks 224 A := {S₀ with R := (Function.update (Function.update S₀.R 206 []) 109
    (cstream A V ((bOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))))}
  have hclean : ∀ i ∈ ([184,223,208,211,201,215] : List (Fin 224)), S.R i = [] := by
    intro i hi
    apply h.scratch i
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    tauto
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁⟩ := prepareBoundaryCoordinates_exec s B V v S h.left h.mul
    (by simp only [h.count,List.length_replicate]) hcoords h.geometry (h.scratch 217 (by simp)) hclean
  have hscratch : ∀ i ∈ ([0,1,2,3,4,5,6,7,8,9,184,217,223,201,208,211,215,220,206] : List (Fin 224)), S₁.R i = [] := by
    intro i hi
    by_cases hi206 : i = 206
    · subst i; simp [S₁]
    · have hoff : i ≠ 109 ∧ i ≠ 189 ∧ i ≠ 191 ∧ i ≠ 198 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [S₁,S₀,hi206,hoff.1,hoff.2.1,hoff.2.2.1,hoff.2.2.2] using h.scratch i hi
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := generatedBoundaryPublish_exec hA s B V w hw hsV G hoff [] [] v₁ S₁
    (by simpa [S₁,S₀] using h.ambient) (by simpa [S₁,S₀] using h.width)
    (by simpa [S₁,S₀] using h.geometry) (by simpa [S₁,S₀] using h.count)
    (by simp [S₁]) (by simpa [S₁,S₀] using hsource) hscratch
  refine ⟨v₂,m₁+m₂,hv₂.trans hv₁,Nat.add_le_add hm₁ hm₂,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases h109 : i = 109 <;> by_cases h206 : i = 206 <;>
    by_cases h204 : i = 204 <;> by_cases h132 : i = 132 <;>
    simp [S₁,S₀,h109,h206,h204,h132]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
