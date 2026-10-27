module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageInverseSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCacheComplexBatch

/-! Execute factor construction and reusable publication-control setup once for a shared inverse key. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 256 Q A U}

noncomputable def placedFactorBatchSetup (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 256 Q A U :=
  embProg couplingBoundaryReg Empty.elim (sharedPageInverseSetup (P := Empty) hR hQ)

theorem placedFactorBatchSetup_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (v : HS 256 Q A U) (S : Stacks 256 A) (tail : List (Fin (A+4)))
    (h109 : (embStk couplingBoundaryReg S).R 109 = []) (h115 : (embStk couplingBoundaryReg S).R 115 = []) (h116 : (embStk couplingBoundaryReg S).R 116 = [])
    (hleft : ∀ i : Fin 240, (embStk couplingBoundaryReg S).L i = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u
      (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u
        (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
      l s t u (PhaseCellBand.width p u) 0 0 tail
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg (embStk couplingBoundaryReg S)))))))
    (haMaster : ((embStk couplingBoundaryReg S).R 141).length = a) (hbMaster : ((embStk couplingBoundaryReg S).R 142).length = b)
    (h0 : (embStk couplingBoundaryReg S).R 0 = []) (h139 : (embStk couplingBoundaryReg S).R 139 = []) (h127 : (embStk couplingBoundaryReg S).R 127 = []) (h138 : (embStk couplingBoundaryReg S).R 138 = [])
    (h143 : (embStk couplingBoundaryReg S).R 143 = []) (h147 : (embStk couplingBoundaryReg S).R 147 = []) (h151 : (embStk couplingBoundaryReg S).R 151 = []) (h153 : (embStk couplingBoundaryReg S).R 153 = [])
    (h152 : (embStk couplingBoundaryReg S).R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → (embStk couplingBoundaryReg S).R (sharedPageRecoveryReg i) = []) (hprivateFresh : ∀ i : Fin 240, 224 ≤ i.val → (embStk couplingBoundaryReg S).R i = []) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p target rhsExp B.card
    let band := PhaseCellBand.width p u
    let W := 12*band+1
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    ∃ v' S' n, ∃ columns : List (ZMod s → GaussianInt),
      let σ := boundaryFactorState (embStk sharedPageRecoveryReg (embStk couplingBoundaryReg S'))
      let AZ := factorRankIntegerMatrix B W columns
      v'.user = v.user ∧ n ≤ constructedBoundaryFactorCost p u l s t a b target rhsExp+
        sharedPagePublicationSetupCost B.card (publicationGeometryWidth t band) w s ∧
      Exec body (placedFactorBatchSetup hR hQ) (mk v S) n (mk v' S') ∧
      (∀ i : Fin 256, 240 ≤ i.val → S'.R i = S.R i) ∧
      (∀ i : Fin 256, 240 ≤ i.val → S'.L i = S.L i) ∧
      columns.length = B.card ∧ ColumnFamilyFormat w columns ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (haloVertices s a b) (haloInterior s t band a b).toList).1
        (1/(2 : ℝ)^bits) columns ∧
      SchurDominance.StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
        (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits)) (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) ∧
      BoundarySolveReady σ q w W B.card ∧
      σ .bo = cstream A w ((naturalLineLc q K W B.card AZ).map colC).flatten ∧
      σ .hf = cstream A w ((naturalLineUc q K W B.card AZ).map colC).flatten ∧
      σ .df = cstream A w ((naturalLineRcs q K W B.card AZ).map fun x => (⟨x,0⟩ : GaussianInt)) ∧
      (embStk couplingBoundaryReg S').R 206 = [] ∧ (embStk couplingBoundaryReg S').R 224 = (embStk couplingBoundaryReg S).R 224 ∧ (embStk couplingBoundaryReg S').R 225 = (embStk couplingBoundaryReg S).R 225 ∧
      (∀ i : Fin 224, (embStk couplingBoundaryReg S').L (sharedPageRecoveryReg i) = []) ∧
      (∀ i : Fin 64, (embStk couplingBoundaryReg S').R (sharedPageRecoveryReg (boundaryFactorMulReg i)) = []) ∧
      ((embStk couplingBoundaryReg S').R 119).length = q ∧ (embStk couplingBoundaryReg S').R 223 = [] ∧ (embStk couplingBoundaryReg S').R 184 = [] ∧ (embStk couplingBoundaryReg S').R 220 = [] ∧ (embStk couplingBoundaryReg S').R 221 = [] ∧
      (∀ i ∈ B, ∀ j ∈ B,
        |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
          (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
            (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^bits) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
        q l s t u band 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
          (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg (embStk couplingBoundaryReg S')))))) ∧
      (embStk couplingBoundaryReg S').R 109 = cstream A (publicationGeometryWidth t band) ((bFoldOrder s B).map
        (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))) ∧
      (embStk couplingBoundaryReg S').R 115 = List.replicate (publicationGeometryWidth t band) tick ∧
      (embStk couplingBoundaryReg S').R 116 = List.replicate B.card tick ∧ (embStk couplingBoundaryReg S').R 132 = bandTableWords A w B W columns 0++(embStk couplingBoundaryReg S).R 132 ∧
      (embStk couplingBoundaryReg S').inp = (embStk couplingBoundaryReg S).inp ∧ (embStk couplingBoundaryReg S').out = (embStk couplingBoundaryReg S).out ∧ (embStk couplingBoundaryReg S').L = (embStk couplingBoundaryReg S).L ∧
      (∀ i : Fin 154, i ≠ 109 → i ≠ 115 → i ≠ 116 → i ≠ 132 →
        (embStk couplingBoundaryReg S').R (sharedPageRecoveryReg (boundaryFactorLegacyReg i)) = (embStk couplingBoundaryReg S).R (sharedPageRecoveryReg (boundaryFactorLegacyReg i))) ∧
      (∀ i : Fin 240, 224 ≤ i.val → i ≠ 239 → (embStk couplingBoundaryReg S').R i = (embStk couplingBoundaryReg S).R i) ∧
      (bandTableWords A w B W columns 0).length ≤ B.card*(2*W+1)*w ∧
      boundaryUnfoldHeaderVolume σ ≤ 12*band*w+B.card*W ∧
      BoundaryPermanentBound σ (boundaryPermanentSizeBound q band B.card) ∧
      (embStk couplingBoundaryReg S').R 239 = gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0]) := by
  intro B bits band W q w K
  obtain ⟨v₁,page,n,columns,hu₁,hn,he,hrest⟩ := sharedPageInverseSetup_spec
    (body := fun p : Empty => nomatch p) hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget
    hband has hbs hpad (embDn couplingBoundaryReg v) (embStk couplingBoundaryReg S)
    tail h109 h115 h116 hleft hready haMaster hbMaster h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew hprivateFresh
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    couplingBoundaryReg_injective (fun p => nomatch p) he v rfl S rfl
  let page' := embOvr couplingBoundaryReg page.get S
  have hproject : embStk couplingBoundaryReg page' = page :=
    embStk_ovr couplingBoundaryReg_injective page S
  refine ⟨v₂,page',n,columns,hu₂.trans hu₁,hn,he₂,?_⟩
  have hoff : ∀ i : Fin 256, 240 ≤ i.val → page'.R i = S.R i := by
    intro i hi
    exact (embOvr_off (e := couplingBoundaryReg) page.get S
      (fun k => cachedBoundaryReg_off k i hi)).2
  refine ⟨hoff,?_,?_⟩
  · intro i hi
    exact (embOvr_off (e := couplingBoundaryReg) page.get S
      (fun k => cachedBoundaryReg_off k i hi)).1
  simpa only [hproject] using hrest

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
