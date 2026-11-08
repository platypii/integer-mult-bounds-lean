module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedResidualLift
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishArchivedInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicPublicationField

/-! Consume both archived interiors and emit one real cyclic recovery stream. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def physicalCyclicPublication : Pr P 224 Q A U :=
  embProg boundaryFactorLegacyReg id (embProg tableReg id (embProg boundaryArithmeticReg id cyclicPublication))

theorem physicalCyclicPublication_exec {P₀ N q l s t u band a n : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hst : s < t) (ha : a < s) (hn : n ≤ s) (hband : band ≤ s)
    (D E Y : ZMod s → GaussianInt) (tail archiveTail input : List (Fin (A+4)))
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hready : LengthKeyReady P₀ N q l s t u band 0 0 input (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))))
    (haSrc : (S.R 144).length = a) (hleftEnd : (S.R 145).length = a+min n (s-a))
    (hrightEnd : (S.R 146).length = n-min n (s-a))
    (hfresh : ∀ k ∈ ([(138 : Fin 224),141,142,143]), S.R k = [])
    (harchive : S.R 147 = cstream A (2*q+8) (chirpLine s E)++
      (cstream A (2*q+8) (chirpLine s D)++archiveTail))
    (hsource : S.R 132 = cstream A (2*q+8) (chirpLine s Y)++tail) :
    let F : Stacks 224 A := {S with R := (Function.update (Function.update S.R 147 archiveTail) 132
      (cstream A (2*q+8) (chirpLine s (cyclicPublicationField t band a n D E Y))++tail))}
    ∃ v' m, v'.user = v.user ∧ m ≤ cyclicPublicationCost P₀ q s t u band a n ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) physicalCyclicPublication (mk v S) m (mk v' F) ∧
      LengthKeyReady P₀ N q l s t u band 0 0 input (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg F)))) := by
  dsimp only
  let S₀ := embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S))
  let output := cstream A (2*q+8) (chirpLine s (cyclicPublicationField t band a n D E Y))++tail
  obtain ⟨v₁,m,hv₁,hm,he,hready₁⟩ := cyclicPublication_exec (body := body)
    hA hst ha hn hband D E Y tail archiveTail input
    (embDn boundaryArithmeticReg (embDn tableReg (embDn boundaryFactorLegacyReg v))) S₀
    hready haSrc hleftEnd hrightEnd
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;>
        simpa [S₀,embStk,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hfresh _ (by simp))
    harchive hsource
  obtain ⟨v₂,hv₂,he₂⟩ := exec_emb_two_outputs boundaryArithmeticReg boundaryArithmeticReg_injective
    (embTab componentReg (embTab groupReg body)) cyclicPublication
    (embDn tableReg (embDn boundaryFactorLegacyReg v)) (embStk tableReg (embStk boundaryFactorLegacyReg S))
    v₁ m 147 132 archiveTail output hv₁ he
  obtain ⟨v₃,hv₃,he₃⟩ := exec_emb_two_outputs tableReg tableReg_injective
    (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))
    (embProg boundaryArithmeticReg id cyclicPublication)
    (embDn boundaryFactorLegacyReg v) (embStk boundaryFactorLegacyReg S) v₂ m 147 132 archiveTail output hv₂ he₂
  obtain ⟨v₄,hv₄,he₄⟩ := exec_emb_two_outputs boundaryFactorLegacyReg boundaryFactorLegacyReg_injective
    (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
    (embProg tableReg id (embProg boundaryArithmeticReg id cyclicPublication))
    v S v₃ m 147 132 archiveTail output hv₃ he₃
  refine ⟨v₄,m,hv₄,hm,?_,?_⟩
  · simpa [physicalCyclicPublication,boundaryFactorLegacyReg,output] using he₄
  · let e : Fin 148 → Fin 224 := fun i => boundaryFactorLegacyReg (tableReg (boundaryArithmeticReg i))
    have he : Function.Injective e := boundaryFactorLegacyReg_injective.comp
      (tableReg_injective.comp boundaryArithmeticReg_injective)
    have h147 : e 147 = 147 := rfl
    have h132 : e 132 = 132 := rfl
    let F : Stacks 224 A := {S with R := Function.update S.R 147 archiveTail}
    have hproject : embStk e {F with R := Function.update F.R 132 output} =
        {embStk e S with R := (Function.update (Function.update (embStk e S).R 147 archiveTail) 132 output)} := by
      rw [← h132,embStk_updateR_inner e he]
      dsimp only [F]
      rw [← h147,embStk_updateR_inner e he]
    change LengthKeyReady P₀ N q l s t u band 0 0 input
      (embStk componentReg (embStk e {F with R := Function.update F.R 132 output}))
    rw [hproject]
    exact hready₁

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
