module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedFactoryFactorExec

/-! Construct the full-line endpoint key from ordinary headers, retaining the
completed metadata for coefficient-page generation. No local separation is used. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

theorem periodicFactorSetup_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t)
    (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (hbudget : α^2*d ≤ p) (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (v : HS 242 Q A U) (H : Stacks 242 A) :
    let band := PhaseCellBand.width p u
    let V := publicationGeometryWidth t band
    let B := haloBoundary s t band 0 s
    let bits := boundaryTableBits p target 2 B.card
    let setupTarget := initialSchurTarget p u bits 2
    let stage := executionStagePrecision p l setupTarget 2+1
    let q := executionPrecision p l setupTarget 2
    let w := executionWidth p l setupTarget 2
    let W := 12*band+1
    let S := packedFactoryInputBank H (2^15*p) stage q l s t u band 0 s V
    ∃ v' F n, ∃ columns : List (ZMod s → GaussianInt),
      v'.user = v.user ∧
      n ≤ constructedBoundaryFactorCost p u l s t 0 s target 2+
        (2*(B.card*publicationGeometryWidth t band+publicationGeometryWidth t band+B.card)+7)+
        ((s+t+band+0+s)*(4*V+10)+56*V+77) ∧
      Exec body (packedBoundaryFactoryGeometry hR hQ)
        (mk v S) n (mk v' F) ∧
      PreparedBoundaryColumns A p bits q w W B columns ∧
      PackedPreparedBank q w W B.card F ∧
      PackedBoundaryFactorPages
        (cstream A w ((naturalLineLc q (factorNewtonSteps p q) W B.card (factorRankIntegerMatrix B W columns)).map colC).flatten)
        (cstream A w ((naturalLineUc q (factorNewtonSteps p q) W B.card (factorRankIntegerMatrix B W columns)).map colC).flatten)
        (cstream A w ((naturalLineRcs q (factorNewtonSteps p q) W B.card (factorRankIntegerMatrix B W columns)).map fun z => (⟨z,0⟩ : GaussianInt)))
        F ∧
      PackedHaloBetweenInputs (2^15*p) stage q l s t u band 0 s V w W B.card
        (extendStacks (by decide) F) ∧
      CouplingIntervalMetadata V s t band 0 s 0 s
        (embStk (Fin.castLE (by decide : 168 ≤ 242)) F) := by
  dsimp only
  obtain ⟨v₁,F,n,columns,hu₁,hn,he₁,_,_,_,_,hcolumns,_,hpages,hbetween,_,_⟩ :=
    packedFactoryInputBank_factor_exec (body := body) (target := target) (rhsExp := 2) (a := 0) (b := s)
      hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband (by omega) (by omega) hpad v H
  have hview : embStk packedRecoveryRuntimeReg (extendStacks (by decide : 242 ≤ 248) F) =
      embStk (Fin.castLE (by decide : 168 ≤ 242)) F := by
    refine Stacks.ext rfl rfl ?_ ?_
    all_goals
      funext i
      have hi := i.isLt
      simp [embStk,packedRecoveryRuntimeReg,extendStacks,show i.val < 242 by omega]; rfl
  have hmeta := hbetween.headers.geometry
  rw [hview] at hmeta
  simp only [Nat.sub_zero] at hmeta
  have hbank := hbetween.bank
  simp only [packedBoundaryRecoveryBase,embStk_extendStacks] at hbank
  exact ⟨v₁,F,n,columns,hu₁,hn,he₁,hcolumns,hbank,hpages,hbetween,hmeta⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
