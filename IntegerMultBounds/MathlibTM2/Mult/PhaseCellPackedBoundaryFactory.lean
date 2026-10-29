module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFactorWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryFactory

/-! Execute the Schur/factor supplier in the same workspace as the packed solve. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

noncomputable def packedBoundaryFactory (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 242 Q A U :=
  embProg packedBoundaryFactorReg Empty.elim (preparedBoundaryFactory hR hQ)

theorem packedBoundaryFactory_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (v : HS 242 Q A U) (S : Stacks 242 A) (tail : List (Fin (A+4)))
    (h109 : (embStk packedBoundaryFactorReg S).R 109 = []) (h115 : (embStk packedBoundaryFactorReg S).R 115 = []) (h116 : (embStk packedBoundaryFactorReg S).R 116 = [])
    (hleft : ∀ i : Fin 224, (embStk packedBoundaryFactorReg S).L (preparedBoundaryCoreReg i) = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u
      (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u
        (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
      l s t u (PhaseCellBand.width p u) 0 0 tail
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S)))))))
    (haMaster : ((embStk packedBoundaryFactorReg S).R 141).length = a) (hbMaster : ((embStk packedBoundaryFactorReg S).R 142).length = b)
    (h0 : (embStk packedBoundaryFactorReg S).R 0 = []) (h139 : (embStk packedBoundaryFactorReg S).R 139 = []) (h127 : (embStk packedBoundaryFactorReg S).R 127 = []) (h138 : (embStk packedBoundaryFactorReg S).R 138 = [])
    (h143 : (embStk packedBoundaryFactorReg S).R 143 = []) (h147 : (embStk packedBoundaryFactorReg S).R 147 = []) (h151 : (embStk packedBoundaryFactorReg S).R 151 = []) (h153 : (embStk packedBoundaryFactorReg S).R 153 = [])
    (h152 : (embStk packedBoundaryFactorReg S).R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → (embStk packedBoundaryFactorReg S).R (preparedBoundaryCoreReg i) = []) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p target rhsExp B.card
    let band := PhaseCellBand.width p u
    let W := 12*band+1
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    ∃ v' S' n, ∃ columns : List (ZMod s → GaussianInt),
      let σ := boundaryFactorState (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S'))
      let AZ := factorRankIntegerMatrix B W columns
      v'.user = v.user ∧ n ≤ constructedBoundaryFactorCost p u l s t a b target rhsExp ∧
      Exec body (packedBoundaryFactory hR hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧
      S'.R 132 = bandTableWords A w B W columns 0++S.R 132 ∧
      BoundaryFactorStock (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S')) (boundaryFactorStockBound q w band B.card) ∧
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
      (embStk packedBoundaryFactorReg S').R 206 = [] ∧ (embStk packedBoundaryFactorReg S').R 224 = (embStk packedBoundaryFactorReg S).R 224 ∧ (embStk packedBoundaryFactorReg S').R 225 = (embStk packedBoundaryFactorReg S).R 225 ∧
      (∀ i : Fin 224, (embStk packedBoundaryFactorReg S').L (preparedBoundaryCoreReg i) = []) ∧
      (∀ i : Fin 64, (embStk packedBoundaryFactorReg S').R (preparedBoundaryCoreReg (boundaryFactorMulReg i)) = []) ∧
      ((embStk packedBoundaryFactorReg S').R 119).length = q ∧ (embStk packedBoundaryFactorReg S').R 223 = [] ∧ (embStk packedBoundaryFactorReg S').R 184 = [] ∧ (embStk packedBoundaryFactorReg S').R 220 = [] ∧ (embStk packedBoundaryFactorReg S').R 221 = [] ∧
      (∀ i ∈ B, ∀ j ∈ B,
        |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
          (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
            (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^bits) ∧
      (LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
        q l s t u band 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
          (embStk boundaryFactorLegacyReg (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S')))))) ∧
        ((embStk packedBoundaryFactorReg S').R 109).length = B.card*publicationGeometryWidth t band ∧
        ((embStk packedBoundaryFactorReg S').R 115).length = publicationGeometryWidth t band ∧
        ((embStk packedBoundaryFactorReg S').R 116).length = B.card ∧
        ∀ i : Fin 154, i ≠ 109 → i ≠ 115 → i ≠ 116 → i ≠ 132 →
          (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S')).R (boundaryFactorLegacyReg i) =
            (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S)).R (boundaryFactorLegacyReg i)) ∧
      ∀ k : Fin 242, (∀ i, packedBoundaryFactorReg i ≠ k) →
        S'.L k = S.L k ∧ S'.R k = S.R k := by
  dsimp only
  obtain ⟨v₁,T₁,n,columns,hu₁,hn,he,hinputFrame,houtputFrame,hrawTable,hstock,hrest⟩ := preparedBoundaryFactory_spec
    (body := fun p : Empty => nomatch p) hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget
    hband has hbs hpad (embDn packedBoundaryFactorReg v) (embStk packedBoundaryFactorReg S)
    tail h109 h115 h116 hleft hready haMaster hbMaster h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    packedBoundaryFactorReg_injective (fun p => nomatch p) he v rfl S rfl
  let S₁ := embOvr packedBoundaryFactorReg T₁.get S
  have hproj : embStk packedBoundaryFactorReg S₁ = T₁ :=
    embStk_ovr packedBoundaryFactorReg_injective T₁ S
  refine ⟨v₂,S₁,n,columns,hu₂.trans hu₁,hn,he₂,(by simpa [S₁,embOvr,embStk] using hinputFrame),
    (by simpa [S₁,embOvr,embStk] using houtputFrame),?_,?_,?_⟩
  · have hp := congrArg (fun G : Stacks 226 A => G.R 132) hproj
    exact hp.trans hrawTable
  · rw [hproj]; exact hstock
  rw [hproj]
  rcases hrest with ⟨hlen,hformat,hcolumns,hstage,hsolve,hbo,hhf,hdf,hvk,h224,h225,
    hleft',hmul,hmaster,h223,h184,h220,h221,herror,hruntime⟩
  exact ⟨hlen,hformat,hcolumns,hstage,hsolve,hbo,hhf,hdf,hvk,h224,h225,
    hleft',hmul,hmaster,h223,h184,h220,h221,herror,hruntime,fun k hk => embOvr_off T₁.get S hk⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
