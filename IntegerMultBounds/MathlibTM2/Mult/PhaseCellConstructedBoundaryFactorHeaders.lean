module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConstructedBoundaryFactorFits
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorHeaderHandoff


/-! Construct the boundary factor page and generate its physical readiness and dimension headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def constructedBoundaryFactorHeaders (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq (embProg boundaryFactorLegacyReg id (constructedBoundaryFactorPage hR hQ)) boundaryFactorHeaderSetup

theorem constructedBoundaryFactorHeaders_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (v : HS 224 Q A U) (S : Stacks 224 A) (tail : List (Fin (A+4)))
    (h109 : S.R 109 = []) (h115 : S.R 115 = []) (h116 : S.R 116 = [])
    (hleft : ∀ i : Fin 224, S.L i = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) l s t u (PhaseCellBand.width p u) 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (h0 : S.R 0 = [])
    (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = []) 
    (h151 : S.R 151 = []) (h153 : S.R 153 = [])
    (h152 : S.R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R i = []) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p target rhsExp B.card
    let W := 12*PhaseCellBand.width p u+1
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let V := publicationGeometryWidth t (PhaseCellBand.width p u)
    ∃ v' n, ∃ columns : List (ZMod s → GaussianInt),
      let E := embStk boundaryFactorLegacyReg S
      let coordinatePage := cstream A V ((bFoldOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))
      let inputPage := cstream A w ((factorWindowValues B W columns).flatten++(factorInputValues B W B.card columns).flatten)
      let E₁ : Stacks 154 A := {E with R := (Function.update (Function.update (Function.update (Function.update (Function.update E.R
        115 (List.replicate V tick)) 116 (List.replicate B.card tick)) 109 coordinatePage)
          132 (bandTableWords A w B W columns 0++E.R 132)) 140 (inputPage++E.R 140))}
      let S₁ := embOvr boundaryFactorLegacyReg E₁.get S
      let S' : Stacks 224 A := {S₁ with R := boundaryFactorHeaderR q S₁.R}
      v'.user = v.user ∧
      n ≤ constructedBoundaryFactorPageCost p u l s t a b bits+boundaryFactorHeaderSetupCost q (PhaseCellBand.width p u) B.card ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
        (constructedBoundaryFactorHeaders hR hQ) (mk v S) n (mk v' S') ∧
      columns.length = B.card ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
          (haloInterior s t (PhaseCellBand.width p u) a b).toList).1 (1/(2 : ℝ)^bits) columns ∧
      ColumnFamilyFormat w columns ∧
      RsbReady (boundaryFactorState S') w q ∧ S'.R 140 = inputPage++S.R 140 ∧
      (bandTableWords A w B W columns 0).length ≤ B.card*(2*W+1)*w ∧
      (∀ i ∈ B, ∀ j ∈ B,
        |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
          (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
            (haloInterior s t (PhaseCellBand.width p u) a b).toList).1 i j| ≤ 1/(2 : ℝ)^bits) ∧
      SchurDominance.StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
        (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits)) (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) ∧
      ∀ k < B.card, FacFits w q (factorNewtonSteps p q)
        (facState q (factorNewtonSteps p q) (factorIntegerRows (factorWindowValues B W columns))
          (factorIntegerRows (factorInputValues B W B.card columns)) k) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p target rhsExp B.card
  let W := 12*PhaseCellBand.width p u+1
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let V := publicationGeometryWidth t (PhaseCellBand.width p u)
  let E := embStk boundaryFactorLegacyReg S
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  obtain ⟨v₁,n₁,columns,hu₁,hn₁,he₁,hlen,hcolumns,hformat,hready₁,hstorage,herror,hstable,hrank,hfit⟩ :=
    constructedBoundaryFactorPage_allocated_spec (body := body) (target := target) (rhsExp := rhsExp)
      hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
      (embDn boundaryFactorLegacyReg v) E tail h109 h115 h116 (fun _ => hleft _) hready
      haMaster hbMaster h0 h139 h127 h138 h143 h147 h151 h153 h152
  let coordinatePage := cstream A V ((bFoldOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))
  let inputPage := cstream A w ((factorWindowValues B W columns).flatten++(factorInputValues B W B.card columns).flatten)
  let E₁ : Stacks 154 A := {E with R := (Function.update (Function.update (Function.update (Function.update (Function.update E.R
    115 (List.replicate V tick)) 116 (List.replicate B.card tick)) 109 coordinatePage)
      132 (bandTableWords A w B W columns 0++E.R 132)) 140 (inputPage++E.R 140))}
  let S₁ := embOvr boundaryFactorLegacyReg E₁.get S
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := id)
    (body' := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
    boundaryFactorLegacyReg_injective (fun _ => rfl) he₁ v rfl S rfl
  have hproj : embStk boundaryFactorLegacyReg S₁ = E₁ := embStk_ovr boundaryFactorLegacyReg_injective E₁ S
  have he₂' : Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
      (embProg boundaryFactorLegacyReg id (constructedBoundaryFactorPage hR hQ)) (mk v S) n₁ (mk v₂ S₁) := he₂
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃,hrdy₃⟩ := boundaryFactorHeaderHandoff_exec
    (body := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
    (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1) q l s t u
    (PhaseCellBand.width p u) 0 0 B.card tail v₂ S E₁ hready
    (by intro i h109 h115 h116 h132 h140; simp [E₁,E,embStk,h109,h115,h116,h132,h140])
    (by simp [E₁]) hnew
  have hsrc : boundaryFactorHeaderR q S₁.R 140 = inputPage++S.R 140 := by
    rw [show boundaryFactorHeaderR q S₁.R 140 = S₁.R 140 from boundaryFactorHeaderR_legacy q S₁.R 140]
    have hh := congrArg (fun X : Stacks 154 A => X.R 140) hproj
    simpa [E₁,E,embStk,boundaryFactorLegacyReg] using hh
  have hrdy : RsbReady (boundaryFactorState {S₁ with R := boundaryFactorHeaderR q S₁.R}) w q := by
    exact Eq.mpr (congrArg (fun z => RsbReady (boundaryFactorState {S₁ with R := boundaryFactorHeaderR q S₁.R}) z q) hw) hrdy₃
  exact ⟨v₃,n₁+n₃,columns,hu₃.trans (hu₂.trans hu₁),Nat.add_le_add hn₁ hn₃,
    Exec.seq he₂' he₃,hlen,hcolumns,hformat,hrdy,hsrc,hstorage,herror,hrank,hfit⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
