module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorPageReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorRankStability
public import IntegerMultBounds.NLogN.PhaseCellHaloSchurStability

/-! Construct the accurate Schur table and full factor input page from ordinary retained masters. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def constructedBoundaryFactorPage (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 154 Q A U :=
  .seq (constructedBoundaryTable hR hQ) generatedFactorPage

noncomputable def constructedBoundaryFactorPageCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  constructedBoundaryTableCost p u l s t a b target+
    generatedFactorPageCost (executionPrecision p l (initialSchurTarget p u target 2) 2)
      (PhaseCellBand.width p u) (haloBoundary s t (PhaseCellBand.width p u) a b).card

theorem constructedBoundaryFactorPage_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (v : HS 154 Q A U) (S : Stacks 154 A) (tail : List (Fin (A+4)))
    (h109 : S.R 109 = []) (h115 : S.R 115 = []) (h116 : S.R 116 = [])
    (hleft : ∀ r : Fin 148, S.L (tableFoldReg r) = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u target 2) 2) l s t u (PhaseCellBand.width p u) 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S))))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (h0 : S.R 0 = [])
    (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = []) 
    (h151 : S.R 151 = []) (h153 : S.R 153 = [])
    (h152 : S.R 152 = []) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let W := 12*PhaseCellBand.width p u+1
    let q := executionPrecision p l (initialSchurTarget p u target 2) 2
    let w := executionWidth p l (initialSchurTarget p u target 2) 2
    let V := publicationGeometryWidth t (PhaseCellBand.width p u)
    let page := cstream A V ((bFoldOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))
    ∃ v' m, ∃ columns : List (ZMod s → GaussianInt),
      let output := bandTableWords A w B W columns 0++S.R 132
      let inputPage := cstream A w ((factorWindowValues B W columns).flatten++
        (factorInputValues B W B.card columns).flatten)
      let S' : Stacks 154 A := {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update S.R
        115 (List.replicate V tick)) 116 (List.replicate B.card tick)) 109 page) 132 output) 140 (inputPage++S.R 140))}
      v'.user = v.user ∧ m ≤ constructedBoundaryFactorPageCost p u l s t a b target ∧
      Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
        (constructedBoundaryFactorPage hR hQ) (mk v S) m (mk v' S') ∧ columns.length = B.card ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
          (haloInterior s t (PhaseCellBand.width p u) a b).toList).1 (1/(2 : ℝ)^target) columns ∧ ColumnFamilyFormat w columns ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
        q l s t u (PhaseCellBand.width p u) 0 0 tail
        (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg {S' with R := Function.update S'.R 140 []}))) ∧
      (bandTableWords A w B W columns 0).length ≤ B.card*(2*W+1)*w ∧
      (∀ i ∈ B, ∀ j ∈ B,
        |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
          (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
            (haloInterior s t (PhaseCellBand.width p u) a b).toList).1 i j| ≤ 1/(2 : ℝ)^target) ∧
      SchurDominance.StageInv (bandBoundaryTable B W (computedBoundaryTable A q w B columns)) B
        (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^target))
        (2+(B.card : ℝ)*(1/(2 : ℝ)^target)) ∧
      SchurDominance.StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
        (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^target))
        (2+(B.card : ℝ)*(1/(2 : ℝ)^target)) := by
  dsimp only
  let band := PhaseCellBand.width p u
  let B := haloBoundary s t band a b
  let W := 12*band+1
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let w := executionWidth p l (initialSchurTarget p u target 2) 2
  let V := publicationGeometryWidth t band
  let page := cstream A V ((bFoldOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))
  have hwq : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  obtain ⟨v₁,m₁,columns,hu₁,hm₁,he₁,hlen,hcolumns,hformat,hready₁,hstorage,herror⟩ := constructedBoundaryTable_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad v S tail
    h109 h115 h116 hleft hready haMaster hbMaster h0 h139 h127 h138 h143 h147 h151 h153 h152
  let output := bandTableWords A w B W columns 0++S.R 132
  let S₁ : Stacks 154 A := {S with R := (Function.update (Function.update (Function.update (Function.update S.R
    115 (List.replicate V tick)) 116 (List.replicate B.card tick)) 109 page) 132 output)}
  have hreadyTable : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      q l s t u band 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S₁))) := hready₁
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := generatedFactorPage_ready_exec
    (body := embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
    B (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1) q l t u band 0 0 tail (S.R 132)
    columns hlen (by simpa [← hwq] using hformat) (by omega) v₁ S₁ hreadyTable
    (by simp [S₁]) (by simp [S₁,output,W,hwq])
    (by simpa [S₁] using h138) (by simpa [S₁] using h151)
    (by simpa [S₁] using h152) (by simpa [S₁] using h153)
  let inputPage := cstream A w ((factorWindowValues B W columns).flatten++(factorInputValues B W B.card columns).flatten)
  let S₂ : Stacks 154 A := {S₁ with R := Function.update S₁.R 140 (inputPage++S.R 140)}
  have he₂' : Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
      generatedFactorPage (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂,inputPage,S₁,W,hwq] using he₂
  have h140 : S₁.R 140 = [] := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hreadyTable.fresh 140 (by simp)
  have hclear : {S₂ with R := Function.update S₂.R 140 []} = S₁ := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk140 : k = 140 <;> simp [S₂,hk140,h140]
  have hinv : SchurDominance.StageInv
      (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
        (haloInterior s t band a b).toList).1 B (1/(8*(p : ℝ))) 2 := by
    simpa only [haloInterior_union_boundary] using
      halo_schur_stageInv hst hα p u a b hp hwidth hαu hθ hgap hbudget
  have hstable := boundaryTable_stageInv B W (computedBoundaryTable A q w B columns) _
    (1/(8*(p : ℝ))) 2 (1/(2 : ℝ)^target) hinv herror
  have hrank := factorRankMatrix_stageInv A q w B W columns _ _ hstable
  refine ⟨v₂,m₁+m₂,columns,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,?_,hlen,hcolumns,hformat,?_,hstorage,herror,hstable,hrank⟩
  · simpa [constructedBoundaryFactorPage,S₂,S₁,output,inputPage,page,V,w,q,W,B,band] using Exec.seq he₁ he₂'
  · change LengthKeyReady _ _ _ _ _ _ _ _ _ _ _ (embStk componentReg (embStk boundaryArithmeticReg
      (embStk tableReg {S₂ with R := Function.update S₂.R 140 []})))
    rw [hclear]
    exact hreadyTable

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
