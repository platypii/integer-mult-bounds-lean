module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConstructedCyclicFactor
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundarySolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorSolveTables
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Generate the cyclic factor page once in the existing reusable batch layout. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def preparedCyclicFactorFactory (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 226 Q A U :=
  embProg preparedBoundaryCoreReg id (constructedCyclicFactor hR hQ)

theorem preparedCyclicFactorFactory_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (has : a < s) (hbs : n ≤ s)
    (v : HS 226 Q A U) (S : Stacks 226 A) (tail : List (Fin (A+4)))
    (pageTail : List (Fin (A+4)))
    (hrows : (S.R 116).length = (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card)
    (hpageWidth : (S.R 115).length = publicationGeometryWidth t (PhaseCellBand.width p u))
    (hpage : S.R 109 = cstream A (publicationGeometryWidth t (PhaseCellBand.width p u))
      ((bFoldOrder s (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n)).map
        (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) l s t u (PhaseCellBand.width p u) 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg (embStk preparedBoundaryCoreReg S))))))
    (haSrc : (S.R 144).length = a) (hleftEnd : (S.R 145).length = a+min n (s-a))
    (hrightEnd : (S.R 146).length = n-min n (s-a))
    (h141 : S.R 141 = []) (h142 : S.R 142 = [])
    (h0 : S.R 0 = [])
    (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = [])
    (h151 : S.R 151 = []) (h152 : S.R 152 = []) (h153 : S.R 153 = [])
    (hleft : ∀ i : Fin 224, S.L (preparedBoundaryCoreReg i) = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R (preparedBoundaryCoreReg i) = []) :
    let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let W := 24*PhaseCellBand.width p u+1
    let K := factorNewtonSteps p q
    ∃ v' S' steps, ∃ columns : List (ZMod s → GaussianInt),
      let σ := boundaryFactorState (embStk preparedBoundaryCoreReg S')
      let AZ := factorRankIntegerMatrix B W columns
      v'.user = v.user ∧ steps ≤ constructedCyclicFactorCost p u l s t a n target rhsExp ∧
      Exec (embTab preparedBoundaryCoreReg (embTab boundaryFactorLegacyReg (embTab tableReg
        (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))))
        (preparedCyclicFactorFactory hR hQ) (mk v S) steps (mk v' S') ∧
      PreparedBoundaryColumns A p bits q w W B columns ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
          (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n).toList).1 (1/(2 : ℝ)^bits) columns ∧
      BoundarySolveReady σ q w W B.card ∧
      σ .bo = cstream A w ((naturalLineLc q K W B.card AZ).map colC).flatten ∧
      σ .hf = cstream A w ((naturalLineUc q K W B.card AZ).map colC).flatten ∧
      σ .df = cstream A w ((naturalLineRcs q K W B.card AZ).map fun x => (⟨x,0⟩ : GaussianInt)) ∧
      σ .vk = [] ∧ σ .dout = [] ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R 132 = bandTableWords A w B W columns 0++S.R 132 ∧
      S'.R 224 = S.R 224 ∧ S'.R 225 = S.R 225 ∧
      (∀ i : Fin 64, S'.R (preparedBoundaryCoreReg (boundaryFactorMulReg i)) = []) ∧
      (S'.R 119).length = q ∧ S'.R 223 = [] ∧ S'.R 184 = [] ∧ S'.R 220 = [] ∧ S'.R 221 = [] ∧ S'.R 116 = S.R 116 := by
  dsimp only
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let W := 24*PhaseCellBand.width p u+1
  let K := factorNewtonSteps p q
  let T := embStk preparedBoundaryCoreReg S
  let native := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
    (embTab componentReg (embTab groupReg body))))
  obtain ⟨v₁,T₁,m,columns,hu₁,hm,he,hlen,hacc,hformat,hprepared,hinp,hout,hL,hlegacy,
    hmul,h106,h139',h184,h223,h220,h221,h119,hsolve,hbo,hhf,hdf,hsrc,hm2n,hmwn,hsn,hdout,hvk,hrest⟩ :=
    constructedCyclicFactor_spec (body := body) hR hQ hA axis has hbs
      (embDn preparedBoundaryCoreReg v) T tail pageTail hrows hpageWidth hpage hready
      haSrc hleftEnd hrightEnd h141 h142 h0 h139 h127 h138 h143 h147 h151 h152 h153 hleft hnew
  obtain ⟨hbo',hhf',hdf'⟩ := boundaryFactor_solve_tables q w K B W columns (boundaryFactorState T₁) hbo hhf hdf
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (e := preparedBoundaryCoreReg) (ι := id)
    preparedBoundaryCoreReg_injective (body := native) (body' := embTab preparedBoundaryCoreReg native)
    (by intro f; rfl) he v rfl S rfl
  let F := embOvr preparedBoundaryCoreReg T₁.get S
  have hproj : embStk preparedBoundaryCoreReg F = T₁ := embStk_ovr preparedBoundaryCoreReg_injective T₁ S
  have hread (k : Fin 226) (hk : k.val < 224) : F.R k = T₁.R ⟨k.val,hk⟩ :=
    congrArg (fun G => G.R ⟨k.val,hk⟩) hproj
  have htable : T₁.R 132 = bandTableWords A w B W columns 0++T.R 132 := by
    simpa [embStk,boundaryFactorLegacyReg] using hlegacy 132 (by decide)
  refine ⟨v₂,F,m,columns,hu₂.trans hu₁,hm,he₂,hprepared,hacc,?_,?_,?_,?_,?_,?_,hinp,hout,
    embOvr_left_of_eq S T₁ hL,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hproj] using hsolve
  · simpa only [hproj] using hbo'
  · simpa only [hproj] using hhf'
  · simpa only [hproj] using hdf'
  · simpa only [hproj] using hvk
  · simpa only [hproj] using hdout
  · simpa [hread 132 (by decide),T,embStk,preparedBoundaryCoreReg] using htable
  · exact (embOvr_off T₁.get S (fun i => (preparedBoundaryCoreReg_private i).1)).2
  · exact (embOvr_off T₁.get S (fun i => (preparedBoundaryCoreReg_private i).2)).2
  · intro i
    have h := congrArg (fun G => G.R (boundaryFactorMulReg i)) hproj
    exact h.trans (hmul i)
  · simpa [hread 119 (by decide)] using h119
  · simpa [hread 223 (by decide)] using h223
  · simpa [hread 184 (by decide)] using h184
  · simpa [hread 220 (by decide)] using h220
  · simpa [hread 221 (by decide)] using h221

  · have h116 : T₁.R 116 = T.R 116 := by
      simpa [embStk,boundaryFactorLegacyReg] using hlegacy 116 (by decide)
    exact (hread 116 (by decide)).trans h116

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
