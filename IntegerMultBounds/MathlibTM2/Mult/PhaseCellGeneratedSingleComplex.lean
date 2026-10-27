module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedClosedComplexBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFactorBatchReleaseCost

/-! Construct, reuse and fully release one boundary page around the complete complex-input inverse. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 256 Q A U}

noncomputable def generatedSingleComplex (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 256 Q A U :=
  .seq (.act ((.push (.rt 246) (fun _ => tick) .done))) (.seq (generatedClosedComplexBatch recovery hR hQ) (uclear 246))

theorem generatedSingleComplex_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let band := PhaseCellBand.width p u
    let solveTarget := boundaryRecoveryTarget p (target+1)
    let bits := boundaryTableBits p solveTarget 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∀ (F : ZMod s → GaussianInt), (∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2) →
    ∀ (v : HS 256 Q A U) (S : Stacks 256 A) (tail : List (Fin (A+4))),
    LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 (cstream A w (chirpLine s F)++tail)
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg (embStk couplingBoundaryReg S)))))) →
    S.R (couplingCachePort recovery 0) = [] →
    S.R (couplingCachePort recovery 2) = [] →
    S.R (couplingCachePort recovery 3) = [] →
    (∀ i, (embStk couplingBoundaryReg S).L i = []) → ((embStk couplingBoundaryReg S).R 141).length = a → ((embStk couplingBoundaryReg S).R 142).length = b →
    (∀ i ∈ ([109,115,116,0,106,139,127,138,143,147,151,153,152,94,131,134,135,136,140] : List (Fin 240)), (embStk couplingBoundaryReg S).R i = []) →
    (∀ i : Fin 240, 154 ≤ i.val → (embStk couplingBoundaryReg S).R i = []) →
    (∀ i ∈ ([240,241,242,243,244,245,246] : List (Fin 256)), S.R i = []) →
    (embStk couplingBoundaryReg S).R 137 = [] →
    ∀ (x y : ZMod s → ℝ),
    (Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (F i)).re)) →
    (Solves (realMatrix s t p u) (haloVertices s a b) y (fun i => (value q (F i)).im)) →
    ∃ v' n, ∃ Z : ZMod s → GaussianInt,
      v'.user = v.user ∧ n ≤ generatedClosedComplexBatchCost p u l s t a b target 1+5 ∧
      Exec body (generatedSingleComplex recovery hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update S.R 132
          (cstream A w (chirpLine s Z)++S.R 132))}) ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b)
        (pairedCellRead q w (cstream A w (chirpLine s Z)++S.R 132))
          (fun i => (⟨x i,y i⟩ : ℂ)) (1/(2 : ℝ)^target) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let band := PhaseCellBand.width p u
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  intro F hF v S tail hready hguard hwords hrowsKey hleft ha hb hclean hnew hfresh h137 x y hx hy
  let S₁ : Stacks 256 A := {S with R := Function.update S.R 246 [tick]}
  have he₁ : Exec body (.act ((.push (.rt 246) (fun _ => tick) .done))) (mk v S) 1 (mk v S₁) := by
    simpa [Action.run,update_rt,S₁,hfresh 246 (by simp)] using Exec.act (body := body) ((.push (.rt 246) (fun _ => tick) .done)) (mk v S)
  have hboundary : embStk couplingBoundaryReg S₁ = embStk couplingBoundaryReg S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    have hne := cachedBoundaryReg_off i 246 (by decide)
    simp [S₁,embStk,Function.comp_def,hne]
  have hproj : embStk couplingSourceReg S₁ = embStk couplingSourceReg S :=
    couplingSource_high_update S 246 (by decide) _
  have hkey (i : Fin 4) : S₁.R (couplingCachePort recovery i) = S.R (couplingCachePort recovery i) := by
    have hi := couplingCachePort_ge recovery i
    have hne : couplingCachePort recovery i ≠ (246 : Fin 256) := by
      intro h; have := congrArg Fin.val h; omega
    simp [S₁,hne]
  obtain ⟨v₂,n,Zs,hu₂,hn₂,he₂,hgood⟩ := generatedClosedComplexBatch_spec (body := body)
    recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
    [F] (by intro G hG i; rcases List.mem_singleton.mp hG with rfl; exact hF i) v S₁ tail
    (by change LengthKeyReady _ _ _ _ _ _ _ _ _ _ _ (embStk couplingSourceReg S₁)
        rw [hproj]
        have hv : embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
          (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg (embStk couplingBoundaryReg S))))) =
            embStk couplingSourceReg S := by
          refine Stacks.ext rfl rfl ?_ ?_ <;> funext i <;> rfl
        rw [← hv]
        simpa only [List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil] using hready)
    ((hkey 0).trans hguard) ((hkey 2).trans hwords) ((hkey 3).trans hrowsKey)
    (by rw [hboundary]; exact hleft) (by rw [hboundary]; exact ha) (by rw [hboundary]; exact hb)
    (by intro i hi; rw [hboundary]; exact hclean i hi)
    (by intro i hi; rw [hboundary]; exact hnew i hi)
    (by simp [S₁])
    (by intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simpa [S₁] using hfresh _ (by simp))
    (by rw [hboundary]; exact h137) (fun _ => x) (fun _ => y)
    (by intro G hG; rcases List.mem_singleton.mp hG with rfl; exact hx)
    (by intro G hG; rcases List.mem_singleton.mp hG with rfl; exact hy)
  simp only [List.length_cons,List.length_nil,Nat.zero_add] at hn₂
  cases hgood with
  | cons hZ hnil =>
    cases hnil
    rename_i Z
    let output := cstream A w (chirpLine s Z)++S.R 132
    let S₂ : Stacks 256 A := {S₁ with R := Function.update S₁.R 132 output}
    have he₂' : Exec body (generatedClosedComplexBatch recovery hR hQ) (mk v S₁) n (mk v₂ S₂) := by
      simpa [S₂,output,S₁] using he₂
    obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 246 v₂ S₂
    have he₃' : Exec body (uclear 246) (mk v₂ S₂) 4
        (mk v₃ {S with R := Function.update S.R 132 output}) := by
      convert he₃ using 1
      · simp [S₂,S₁]
      · apply congrArg (mk v₃)
        refine Stacks.ext rfl rfl rfl ?_
        funext i
        by_cases h246 : i = 246 <;> by_cases h132 : i = 132 <;>
          simp [S₂,S₁,h246,h132,hfresh 246 (by simp)]
    refine ⟨v₃,1+(n+4),Z,hu₃.trans hu₂,?_,Exec.seq he₁ (Exec.seq he₂' he₃'),?_⟩
    · simpa using (by omega : 1+(n+4) ≤ generatedClosedComplexBatchCost p u l s t a b target 1+5)
    · simpa [S₁] using hZ

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
