module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundarySolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConstructedBoundaryFactor
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorSolveTables
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRecoveryReady

/-! Generate the reusable prepared page with the executed Schur/factor factory, rather than supplying factors. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def preparedBoundaryFactory (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 226 Q A U :=
  embProg preparedBoundaryCoreReg id (constructedBoundaryFactor hR hQ)

theorem preparedBoundaryFactory_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (v : HS 226 Q A U) (S : Stacks 226 A) (tail : List (Fin (A+4)))
    (h109 : S.R 109 = []) (h115 : S.R 115 = []) (h116 : S.R 116 = [])
    (hleft : ∀ i : Fin 224, S.L (preparedBoundaryCoreReg i) = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u
      (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u
        (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
      l s t u (PhaseCellBand.width p u) 0 0 tail
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk preparedBoundaryCoreReg S))))))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (h0 : S.R 0 = []) (h139 : S.R 139 = []) (h127 : S.R 127 = []) (h138 : S.R 138 = [])
    (h143 : S.R 143 = []) (h147 : S.R 147 = []) (h151 : S.R 151 = []) (h153 : S.R 153 = [])
    (h152 : S.R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R (preparedBoundaryCoreReg i) = []) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p target rhsExp B.card
    let band := PhaseCellBand.width p u
    let W := 12*band+1
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    ∃ v' S' n, ∃ columns : List (ZMod s → GaussianInt),
      let σ := boundaryFactorState (embStk preparedBoundaryCoreReg S')
      let AZ := factorRankIntegerMatrix B W columns
      v'.user = v.user ∧ n ≤ constructedBoundaryFactorCost p u l s t a b target rhsExp ∧
      Exec (embTab preparedBoundaryCoreReg (embTab boundaryFactorLegacyReg (embTab tableReg
        (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))))
        (preparedBoundaryFactory hR hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧
      S'.R 132 = bandTableWords A w B W columns 0++S.R 132 ∧
      BoundaryFactorStock (embStk preparedBoundaryCoreReg S') (boundaryFactorStockBound q w band B.card) ∧
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
      S'.R 206 = [] ∧ S'.R 224 = S.R 224 ∧ S'.R 225 = S.R 225 ∧
      (∀ i : Fin 224, S'.L (preparedBoundaryCoreReg i) = []) ∧
      (∀ i : Fin 64, S'.R (preparedBoundaryCoreReg (boundaryFactorMulReg i)) = []) ∧
      (S'.R 119).length = q ∧ S'.R 223 = [] ∧ S'.R 184 = [] ∧ S'.R 220 = [] ∧ S'.R 221 = [] ∧
      (∀ i ∈ B, ∀ j ∈ B,
        |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
          (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
            (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^bits) ∧
      (LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
        q l s t u band 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
          (embStk boundaryFactorLegacyReg (embStk preparedBoundaryCoreReg S'))))) ∧
        (S'.R 109).length = B.card*publicationGeometryWidth t band ∧
        (S'.R 115).length = publicationGeometryWidth t band ∧ (S'.R 116).length = B.card ∧
        ∀ i : Fin 154, i ≠ 109 → i ≠ 115 → i ≠ 116 → i ≠ 132 →
          (embStk preparedBoundaryCoreReg S').R (boundaryFactorLegacyReg i) =
            (embStk preparedBoundaryCoreReg S).R (boundaryFactorLegacyReg i)) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p target rhsExp B.card
  let W := 12*PhaseCellBand.width p u+1
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  let T := embStk preparedBoundaryCoreReg S
  let coreBody := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
    (embTab componentReg (embTab groupReg body))))
  obtain ⟨v₁,T₁,n,columns,hu₁,hn,he,hlen,hcolumns,hformat,hstorage,herror,hstage,hinp,hout,hL,hlegacy,
    hmul,h106,h139',h184,h223,h220,h221,h119,hsolve,hbo,hhf,hdf,hsrc,hm2n,hmwn,hsn,hdout,hvk,hrest⟩ :=
    constructedBoundaryFactor_spec (body := body) hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
      (embDn preparedBoundaryCoreReg v) T tail h109 h115 h116 hleft hready haMaster hbMaster
      h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew
  rcases hrest with ⟨hef,hxs,hkn,hms,hm2n',hkn',hmwn',hrdy,hheaders,hperm,hfactorFrame⟩
  have hstock : BoundaryFactorStock T₁ (boundaryFactorStockBound q w (PhaseCellBand.width p u) B.card) := by
    have hh := boundaryFactorStock_of_bounds T₁ hperm hheaders hdout h184 h223
    simpa only [boundaryFactorStockBound,Nat.add_assoc] using hh
  have hframe : ∀ i : Fin 154, i ≠ 109 → i ≠ 115 → i ≠ 116 → i ≠ 132 →
      T₁.R (boundaryFactorLegacyReg i) = T.R (boundaryFactorLegacyReg i) := by
    intro i hi109 hi115 hi116 hi132
    by_cases hi140 : i = 140
    · subst i; exact hsrc
    simpa only [Function.update_of_ne hi140,Function.update_of_ne hi132,
      Function.update_of_ne hi109,Function.update_of_ne hi116,Function.update_of_ne hi115,
      embStk,Function.comp_def] using hlegacy i hi140
  have hruntime := boundaryRecoveryReady_of_frame hready hinp hout hL
    (fun i hi109 hi110 hi115 hi116 hi132 => hframe i hi109 hi115 hi116 hi132)
  have hsource : T₁.R 110 = tail :=
    (hframe 110 (by decide) (by decide) (by decide) (by decide)).trans hready.source
  have hruntime' : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u (PhaseCellBand.width p u) 0 0 tail
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg T₁)))) := by
    simpa only [hsource] using hruntime
  have h109len : (T₁.R 109).length = B.card*publicationGeometryWidth t (PhaseCellBand.width p u) := by
    have hh := hlegacy 109 (by decide)
    simpa [boundaryFactorLegacyReg,embStk,length_cstream,bFoldOrder_length] using congrArg List.length hh
  have h115len : (T₁.R 115).length = publicationGeometryWidth t (PhaseCellBand.width p u) := by
    have hh := hlegacy 115 (by decide)
    simpa [boundaryFactorLegacyReg] using congrArg List.length hh
  have h116len : (T₁.R 116).length = B.card := by
    have hh := hlegacy 116 (by decide)
    simpa [boundaryFactorLegacyReg] using congrArg List.length hh
  obtain ⟨hbo',hhf',hdf'⟩ := boundaryFactor_solve_tables q w K B W columns (boundaryFactorState T₁) hbo hhf hdf
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := id) (body' := embTab preparedBoundaryCoreReg coreBody)
    preparedBoundaryCoreReg_injective (fun _ => rfl) he v rfl S rfl
  let S₁ := embOvr preparedBoundaryCoreReg T₁.get S
  have hproj : embStk preparedBoundaryCoreReg S₁ = T₁ := embStk_ovr preparedBoundaryCoreReg_injective T₁ S
  refine ⟨v₂,S₁,n,columns,hu₂.trans hu₁,hn,he₂,(by simpa [S₁,embOvr,T,embStk] using hinp),
    (by simpa [S₁,embOvr,T,embStk] using hout),?_,?_,hlen,hformat,hcolumns,hstage,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,herror,?_⟩
  · have hh := hlegacy 132 (by decide)
    have hp := congrArg (fun G : Stacks 224 A => G.R 132) hproj
    exact hp.trans (by simpa [boundaryFactorLegacyReg,preparedBoundaryCoreReg,T,embStk] using hh)
  · rw [hproj]; exact hstock
  · rw [hproj]; exact hsolve
  · rw [hproj]; exact hbo'
  · rw [hproj]; exact hhf'
  · rw [hproj]; exact hdf'
  · have hh := congrArg (fun R : Stacks 224 A => R.R 206) hproj
    exact hh.trans hvk
  · exact (embOvr_off (e := preparedBoundaryCoreReg) T₁.get S (fun i => (preparedBoundaryCoreReg_private i).1)).2
  · exact (embOvr_off (e := preparedBoundaryCoreReg) T₁.get S (fun i => (preparedBoundaryCoreReg_private i).2)).2
  · intro i
    have hh := congrArg (fun R : Stacks 224 A => R.L i) hproj
    exact hh.trans (by rw [hL]; exact hleft i)
  · intro i
    have hh := congrArg (fun R : Stacks 224 A => R.R (boundaryFactorMulReg i)) hproj
    exact hh.trans (hmul i)
  · have hh := congrArg (fun R : Stacks 224 A => (R.R 119).length) hproj
    exact hh.trans h119
  · exact (congrArg (fun R : Stacks 224 A => R.R 223) hproj).trans h223
  · exact (congrArg (fun R : Stacks 224 A => R.R 184) hproj).trans h184
  · exact (congrArg (fun R : Stacks 224 A => R.R 220) hproj).trans h220
  · exact (congrArg (fun R : Stacks 224 A => R.R 221) hproj).trans h221

  · refine ⟨?_,?_,?_,?_,?_⟩
    · rw [hproj]; exact hruntime'
    · exact (congrArg (fun R : Stacks 224 A => (R.R 109).length) hproj).trans h109len
    · exact (congrArg (fun R : Stacks 224 A => (R.R 115).length) hproj).trans h115len
    · exact (congrArg (fun R : Stacks 224 A => (R.R 116).length) hproj).trans h116len
    · rw [hproj]; exact hframe

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
