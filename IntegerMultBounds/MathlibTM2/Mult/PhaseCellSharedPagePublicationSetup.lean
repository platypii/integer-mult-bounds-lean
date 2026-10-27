module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageBoundaryCoordinates
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPagePublicationControls

/-! Prepare reusable publication advances from the actual retained folded coordinate page once per key. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

def sharedPagePublicationSetup : Pr P 240 Q A U :=
  .seq sharedPageBoundaryCoordinates sharedPagePublicationControls

def sharedPagePublicationSetupCost (N V w s : ℕ) : ℕ :=
  sharedPageBoundaryCoordinatesCost N V+generateBoundaryAdvancesCost N V w s

theorem sharedPagePublicationSetup_exec (hA : 4 ≤ A) (s : ℕ) [NeZero s]
    (B : Finset (ZMod s)) (V w : ℕ) (hsV : s ≤ 2^V)
    (v : HS 240 Q A U) (S : Stacks 240 A)
    (hleft : ∀ i, S.L i = [])
    (hmul : ∀ i : Fin 64, (embStk sharedPageCoordinateReg S).R (boundaryFactorMulReg i) = [])
    (hc : S.R 116 = List.replicate B.card tick)
    (hV : (S.R 115).length = V) (hw : (S.R 160).length = w)
    (hcoords : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))))
    (hclean : ∀ i ∈ ([0,1,2,3,4,5,6,7,8,9,234,235,184,223,238,208,211,236,201,215,239,231,232,233] : List (Fin 240)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ sharedPagePublicationSetupCost B.card V w s ∧
      Exec body sharedPagePublicationSetup (mk v S) n
        (mk v' {S with R := (Function.update S.R 239
          (gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0])))}) := by
  have hz : ∀ i ∈ ([234,235,184,223,238,208,211,236,201,215] : List (Fin 240)), S.R i = [] := by
    intro i hi
    apply hclean
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    tauto
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := sharedPageBoundaryCoordinates_exec (body := body) s B V v S hleft hmul
    (by rw [hc]; simp) hV hcoords (hclean _ (by simp)) (hclean _ (by simp))
    (hclean _ (by simp)) (hclean _ (by simp)) hz
  let coordinates := cstream A V ((bOrder s B).map
    (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))
  let S₁ : Stacks 240 A := {S with R := Function.update S.R 238 coordinates}
  have hz₁ : ∀ i ∈ ([0,1,2,3,4,5,6,7,8,9] : List (Fin 240)), S₁.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [S₁] using hclean _ (by simp)
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := sharedPagePublicationControls_exec (body := body) hA s B V w hsV [] v₁ S₁
    (by simpa [S₁] using hc) (by simpa [S₁] using hV) (by simpa [S₁] using hw)
    (by simp [S₁,coordinates]) hz₁
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  have h238 := hclean 238 (by simp)
  have h239 := hclean 239 (by simp)
  by_cases hi238 : i = 238 <;> by_cases hi239 : i = 239 <;>
    simp [S₁,hi238,hi239,h238,h239]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
