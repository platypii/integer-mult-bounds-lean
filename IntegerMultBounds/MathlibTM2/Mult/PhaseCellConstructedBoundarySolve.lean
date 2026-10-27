module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConstructedBoundaryFactor
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryGatherSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorSolveTables

/-! Construct the boundary matrix and factors, then gather, normalize and solve the retained residual. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def constructedBoundarySolve (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq (constructedBoundaryFactor hR hQ) (generatedBoundaryGatherSolve hQ)

noncomputable def constructedBoundarySolveCost (p u l s t a b target rhsExp : ℕ) [NeZero s] : ℕ :=
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p target rhsExp B.card
  let band := PhaseCellBand.width p u
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let W := 12*band+1
  let V := publicationGeometryWidth t band
  constructedBoundaryFactorCost p u l s t a b target rhsExp+
    (boundaryRhsPrepareCost V w B.card s+generatedBoundaryNormalizeCost q B.card+
      4*B.card*w+4*W*w+8+bandLinePassCost w B.card W)

theorem constructedBoundarySolve_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    let band := PhaseCellBand.width p u
    let W := 12*band+1
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let V := publicationGeometryWidth t band
    let K := factorNewtonSteps p q
    ∀ (C : ZMod s → GaussianInt) (rhsTail : List (Fin (A+4))),
    (∀ i ∈ B, |gv q (C i).re| ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
      (8*p+1) (couplingCountExponent p u) ∧
      |gv q (C i).im| ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
      (8*p+1) (couplingCountExponent p u)) →
    S.R 110 = cstream A w (chirpLine s C)++rhsTail →
    ∃ v' S' n, ∃ columns : List (ZMod s → GaussianInt),
      let AZ := factorRankIntegerMatrix B W columns
      let xs := ((List.range B.card).map (fun j => C (bFoldAt s B j))).map (normalizeBoundaryWord q (q/2-1))
      let solution := bandSolveVec q W (naturalLineLc q K W B.card AZ)
        (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ) xs
      v'.user = v.user ∧ n ≤ constructedBoundarySolveCost p u l s t a b target rhsExp ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
        (constructedBoundarySolve hR hQ) (mk v S) n (mk v' S') ∧
      columns.length = B.card ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
          (haloInterior s t band a b).toList).1 (1/(2 : ℝ)^bits) columns ∧
      ColumnFamilyFormat w columns ∧
      (bandTableWords A w B W columns 0).length ≤ B.card*(2*W+1)*w ∧
      (∀ i ∈ B, ∀ j ∈ B,
        |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
          (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
            (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^bits) ∧
      SchurDominance.StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
        (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits)) (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i : Fin 154, i ≠ 109 → i ≠ 115 → i ≠ 116 → i ≠ 132 →
        S'.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i)) ∧
      S'.R 109 = cstream A V ((bFoldOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))) ∧
      S'.R 115 = List.replicate V tick ∧ S'.R 116 = List.replicate B.card tick ∧
      S'.R 132 = bandTableWords A w B W columns 0++S.R 132 ∧
      (boundaryFactorState S') .bo = cstream A w ((naturalLineLc q K W B.card AZ).map colC).flatten ∧
      (boundaryFactorState S') .hf = cstream A w ((naturalLineUc q K W B.card AZ).map colC).flatten ∧
      (boundaryFactorState S') .df = cstream A w ((naturalLineRcs q K W B.card AZ).map fun x => (⟨x,0⟩ : GaussianInt)) ∧
      BoundarySolveReady (Function.update (boundaryFactorState S') .dout []) q w W B.card ∧
      S'.R 217 = cstream A w solution ∧ S'.R 206 = [] ∧
      RsbReady (boundaryFactorState S') w q ∧
      S'.R 184 = [] ∧ S'.R 223 = [] ∧ S'.R 220 = [] ∧ S'.R 221 = [] := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let band := PhaseCellBand.width p u
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let W := 12*band+1
  let V := publicationGeometryWidth t band
  let K := factorNewtonSteps p q
  intro C rhsTail hC hRhs
  obtain ⟨v₁,S₁,n₁,columns,hu₁,hn₁,he₁,hlen,hcolumns,hformat,hstorage,herror,hrank,hinp₁,hout₁,hL₁,
    hlegacy₁,hmul,h106,h139',h184,h223,h220,h221,h119,hready,hbo,hhf,hdf,hsrc,hm2n,hmwn,hsn,hdout,hvk,hrest⟩ :=
    constructedBoundaryFactor_spec (body := body) hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
      v S tail h109 h115 h116 hleft hready haMaster hbMaster h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew
  obtain ⟨hbo',hhf',hdf'⟩ := boundaryFactor_solve_tables q w K B W columns (boundaryFactorState S₁) hbo hhf hdf
  have hsV : s ≤ 2^V := by
    have hfit : 8*(t+1)^2+2*band+8 < 2^V := publicationGeometryWidth_fits t band
    nlinarith only [hfit,hst]
  have hN : (S₁.R 116).length = B.card := by
    have hh := hlegacy₁ 116 (by decide)
    simpa [embStk,boundaryFactorLegacyReg] using congrArg List.length hh
  have hV : (S₁.R 115).length = V := by
    have hh := hlegacy₁ 115 (by decide)
    simpa [embStk,boundaryFactorLegacyReg] using congrArg List.length hh
  have hcoordinates : S₁.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++[] := by
    have hh := hlegacy₁ 109 (by decide)
    simpa [embStk,boundaryFactorLegacyReg] using hh
  have hkeep (i : Fin 154) (hi109 : i ≠ 109) (hi115 : i ≠ 115) (hi116 : i ≠ 116)
      (hi132 : i ≠ 132) (hi140 : i ≠ 140) :
      S₁.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i) := by
    have hh := hlegacy₁ i hi140
    dsimp only at hh
    simpa [embStk,hi109,hi115,hi116,hi132,hi140] using hh
  have hRhs₁ : S₁.R 110 = cstream A w (chirpLine s C)++rhsTail :=
    (hkeep 110 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hRhs
  obtain ⟨v₂,S₂,n₂,hu₂,hn₂,he₂,hinp₂,hout₂,hL₂,hlegacy₂,hframe,hpost⟩ := generatedBoundaryGatherSolve_exec
    (body := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
    hQ hA p u l target rhsExp B W V columns hp hlen hsV hformat hrank C hC [] rhsTail v₁ S₁
    (by intro i; rw [hL₁]; exact hleft i) hmul hready h119 h223 h184 h220 h221 hN hV hcoordinates hRhs₁ h106 h139' hvk
    hbo' hhf' hdf'
  have h184' : S₂.R 184 = [] := (hframe.2.2.2 184 (fun r => (boundaryFactorReg_private r).1)).trans h184
  have h223' : S₂.R 223 = [] := (hframe.2.2.2 223 (fun r => (boundaryFactorReg_private r).2)).trans h223
  have h220' : S₂.R 220 = [] := (congrFun hpost .dtab).trans h220
  have h221' : S₂.R 221 = [] := (congrFun hpost .padc).trans h221
  have hready' : RsbReady (boundaryFactorState S₂) w q := by
    rw [hpost]
    exact (hready.ready.update .vk (fun _ => by simp) []).update .dout (fun _ => by simp) _
  have h109' : S₂.R 109 = cstream A V ((bFoldOrder s B).map
      (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))) := by
    exact (hlegacy₂ 109).trans (by simpa [boundaryFactorLegacyReg] using hcoordinates)
  have h115' : S₂.R 115 = List.replicate V tick := by
    have hh := hlegacy₁ 115 (by decide)
    exact (hlegacy₂ 115).trans (by simpa [embStk,boundaryFactorLegacyReg] using hh)
  have h116' : S₂.R 116 = List.replicate B.card tick := by
    have hh := hlegacy₁ 116 (by decide)
    exact (hlegacy₂ 116).trans (by simpa [embStk,boundaryFactorLegacyReg] using hh)
  have h132' : S₂.R 132 = bandTableWords A w B W columns 0++S.R 132 := by
    have hh := hlegacy₁ 132 (by decide)
    exact (hlegacy₂ 132).trans (by simpa [embStk,boundaryFactorLegacyReg] using hh)
  have hboFinal := (congrFun hpost .bo).trans hbo'
  have hhfFinal := (congrFun hpost .hf).trans hhf'
  have hdfFinal := (congrFun hpost .df).trans hdf'
  have hreset : Function.update (boundaryFactorState S₂) .dout [] = boundaryFactorState S₁ := by
    rw [hpost]
    funext r
    by_cases hr : r = .dout
    · subst r; simpa using hdout.symm
    by_cases hv : r = .vk
    · subst r; simpa using hvk.symm
    simp [hr,hv]
  have hresetReady : BoundarySolveReady (Function.update (boundaryFactorState S₂) .dout []) q w W B.card := by
    rw [hreset]
    exact hready
  refine ⟨v₂,S₂,n₁+n₂,columns,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,hlen,hcolumns,
    hformat,hstorage,herror,hrank,hinp₂.trans hinp₁,hout₂.trans hout₁,hL₂.trans hL₁,?_,h109',h115',h116',h132',hboFinal,hhfFinal,hdfFinal,hresetReady,congrFun hpost .dout,
    congrFun hpost .vk,hready',h184',h223',h220',h221'⟩
  intro i hi109 hi115 hi116 hi132
  by_cases hi140 : i = 140
  · subst i
    exact (hlegacy₂ 140).trans hsrc
  · exact (hlegacy₂ i).trans (hkeep i hi109 hi115 hi116 hi132 hi140)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
