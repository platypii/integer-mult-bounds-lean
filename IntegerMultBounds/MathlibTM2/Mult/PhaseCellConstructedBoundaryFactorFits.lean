module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConstructedBoundaryFactorPage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorAllocatedFits


/-! The constructed boundary factor page satisfies every factor-state fit condition at canonical precision. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem constructedBoundaryFactorPage_allocated_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (v : HS 154 Q A U) (S : Stacks 154 A) (tail : List (Fin (A+4)))
    (h109 : S.R 109 = []) (h115 : S.R 115 = []) (h116 : S.R 116 = [])
    (hleft : ∀ r : Fin 148, S.L (tableFoldReg r) = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) l s t u (PhaseCellBand.width p u) 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S))))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (h0 : S.R 0 = [])
    (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = []) 
    (h151 : S.R 151 = []) (h153 : S.R 153 = [])
    (h152 : S.R 152 = []) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let entryBits := boundaryTableBits p target rhsExp B.card
    let W := 12*PhaseCellBand.width p u+1
    let q := executionPrecision p l (initialSchurTarget p u entryBits 2) 2
    let w := executionWidth p l (initialSchurTarget p u entryBits 2) 2
    let V := publicationGeometryWidth t (PhaseCellBand.width p u)
    let page := cstream A V ((bFoldOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))
    ∃ v' m, ∃ columns : List (ZMod s → GaussianInt),
      let output := bandTableWords A w B W columns 0++S.R 132
      let inputPage := cstream A w ((factorWindowValues B W columns).flatten++
        (factorInputValues B W B.card columns).flatten)
      let S' : Stacks 154 A := {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update S.R
        115 (List.replicate V tick)) 116 (List.replicate B.card tick)) 109 page) 132 output) 140 (inputPage++S.R 140))}
      v'.user = v.user ∧ m ≤ constructedBoundaryFactorPageCost p u l s t a b entryBits ∧
      Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
        (constructedBoundaryFactorPage hR hQ) (mk v S) m (mk v' S') ∧ columns.length = B.card ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
          (haloInterior s t (PhaseCellBand.width p u) a b).toList).1 (1/(2 : ℝ)^entryBits) columns ∧ ColumnFamilyFormat w columns ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u entryBits 2) 2+1)
        q l s t u (PhaseCellBand.width p u) 0 0 tail
        (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg {S' with R := Function.update S'.R 140 []}))) ∧
      (bandTableWords A w B W columns 0).length ≤ B.card*(2*W+1)*w ∧
      (∀ i ∈ B, ∀ j ∈ B,
        |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
          (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
            (haloInterior s t (PhaseCellBand.width p u) a b).toList).1 i j| ≤ 1/(2 : ℝ)^entryBits) ∧
      SchurDominance.StageInv (bandBoundaryTable B W (computedBoundaryTable A q w B columns)) B
        (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^entryBits))
        (2+(B.card : ℝ)*(1/(2 : ℝ)^entryBits)) ∧
      SchurDominance.StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
        (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^entryBits))
        (2+(B.card : ℝ)*(1/(2 : ℝ)^entryBits)) ∧
      ∀ k < B.card, FacFits w q (factorNewtonSteps p q)
        (facState q (factorNewtonSteps p q) (factorIntegerRows (factorWindowValues B W columns))
          (factorIntegerRows (factorInputValues B W B.card columns)) k) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let W := 12*PhaseCellBand.width p u+1
  let bits := boundaryTableBits p target rhsExp B.card
  obtain ⟨v',m,columns,hu',hm,he,hlen,hcolumns,hformat,hready',hstorage,herror,hstable,hrank⟩ :=
    constructedBoundaryFactorPage_spec (body := body) (target := bits)
      hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad v S tail
      h109 h115 h116 hleft hready haMaster hbMaster h0 h139 h127 h138 h143 h147 h151 h153 h152
  have hfit := factorIntegerState_allocated_fits A p u l target rhsExp B W columns (by omega) hp hlen hformat hrank
  exact ⟨v',m,columns,hu',hm,he,hlen,hcolumns,hformat,hready',hstorage,herror,hstable,hrank,hfit⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
