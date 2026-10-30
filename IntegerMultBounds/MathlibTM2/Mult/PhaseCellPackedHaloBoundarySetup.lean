module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingMasterHeaders

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactoryGeometryMode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedPackedHaloRealBoundaryData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryHaloPrecision
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolveWorkspace

/-! Execute setup and the complete halo RHS producer at a proved shared format. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

noncomputable def packedHaloBoundarySetup (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 242 Q A U :=
  .seq (packedBoundaryFactoryGeometry hR hQ) (placedPackedHaloRealBoundaryData hR hQ)

noncomputable def packedHaloBoundarySetupUsing (freshGeometry : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 242 Q A U :=
  .seq (packedBoundaryFactoryGeometryUsing freshGeometry hR hQ) (placedPackedHaloRealBoundaryData hR hQ)

theorem packedHaloBoundarySetupUsing_exec (freshGeometry : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C : ZMod s → GaussianInt) (tail E outputTail : List (Fin (A+4)))
    (v : HS 242 Q A U) (S : Stacks 242 A)
    (h109 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 109 = []) (h115 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 115 = []) (h116 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 116 = [])
    (hleft : ∀ i : Fin 224, (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).L (preparedBoundaryCoreReg i) = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u
      (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u
        (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
      l s t u (PhaseCellBand.width p u) 0 0 (cstream A (executionWidth p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (packedInterval a (b-a) C)++tail)
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S))))))))
    (haMaster : ((embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 141).length = a) (hbMaster : ((embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 142).length = b)
    (h0 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 0 = []) (h139 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 139 = []) (h127 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 127 = []) (h138 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 138 = [])
    (h143 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 143 = []) (h147 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 147 = []) (h151 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 151 = []) (h153 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 153 = [])
    (h152 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R (preparedBoundaryCoreReg i) = []) (h132left : S.L 132 = [])
    (hV : (S.R 163).length = V)
    (h155 : S.R 155 = binSyms V a) (h165 : S.R 165 = binSyms V (b-a))
    (hfitV : a+((b-a)+2*PhaseCellBand.width p u)+s < 2^V)
    (hgeometry : if freshGeometry then
      (∀ k ∈ [(145 : Fin 242),146,147,148,149,151,154,156,164], S.R k = [])
      else CouplingIntervalMetadata V s t (PhaseCellBand.width p u) a b a (b-a)
        (embStk packedHaloRuntimeReg S))
    (h239 : S.R 239 = [])
    (hab : a ≤ b) (haLt : a < s) (hsep : b-a+PhaseCellBand.width p u ≤ s)
    (hwide : 8*(t+1)^2+4*PhaseCellBand.width p u+8 < 2^V)
    (hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (2*(executionPrecision p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp)+8) t u)
    (hwV : (executionWidth p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) < 2^V) (hcoords : b < 2^V) (hunits : b*(executionWidth p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) < 2^V)
    (hC : ∀ k, ‖value (executionPrecision p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (h157 : (S.R 157).length ≤ V) (h158 : S.R 158 = []) (h167 : S.R 167 = [])
    (houtput : S.R 132 = E++outputTail) (hE : E.length = (b-a)*(executionWidth p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp))
    (hfresh : ∀ k ∈ [(125 : Fin 168),127,130,133,138,129,131,134,135,136,140,153,166],
      (embStk packedHaloRuntimeReg S).R k = [])
    (hrange : EncodedRange A (executionWidth p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (executionPrecision p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp)
      (interiorOutputExponent p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) E)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (C k)).re)) :
    let band := PhaseCellBand.width p u
    let B := haloBoundary s t band a b
    let j := boundaryHaloTarget p u target rhsExp B.card
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let W := 12*band+1
    let K := factorNewtonSteps p q
    ∃ v' F m, ∃ columns : List (ZMod s → GaussianInt), ∃ D : ZMod s → GaussianInt,
      let σ := boundaryFactorState (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg F))
      let AZ := factorRankIntegerMatrix B W columns
      let rows := (bFoldOrder s B).map (fun i => realPartWord
        (couplingRowField (2^15*p) q t u band a b false D C i))
      v'.user = v.user ∧
      m ≤ constructedBoundaryFactorCost p u l s t a b target rhsExp+
        (2*(B.card*publicationGeometryWidth t band+publicationGeometryWidth t band+B.card)+7)+
        (if freshGeometry then (s+t+band+a+b)*(4*V+10)+56*V+77 else 0)+
        packedHaloRealBoundaryDataCost p l s t u j rhsExp a b V ∧
      Exec body (packedHaloBoundarySetupUsing freshGeometry hR hQ) (mk v S) m (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      F.R 220 = bandTableWords A w B W columns 0++S.R 220 ∧
      BoundaryFactorStock (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg F)) (boundaryFactorStockBound q w band B.card) ∧
      columns.length = B.card ∧ ColumnFamilyFormat w columns ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (haloVertices s a b) (haloInterior s t band a b).toList).1
        (1/(2 : ℝ)^bits) columns ∧
      SchurDominance.StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
        (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits)) (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) ∧
      BoundarySolveReady σ q w W B.card ∧
      σ .bo = cstream A w ((naturalLineLc q K W B.card AZ).map colC).flatten ∧
      σ .hf = cstream A w ((naturalLineUc q K W B.card AZ).map colC).flatten ∧
      σ .df = cstream A w ((naturalLineRcs q K W B.card AZ).map fun z => (⟨z,0⟩ : GaussianInt)) ∧
      F.R 93 = S.R 93 ∧ F.R 143 = cstream A w rows ∧
      F.R 132 = cstream A w (packedInterval a (b-a) D)++outputTail ∧
      F.R 110 = cstream A w (packedInterval a (b-a)
        (guardedCouplingRowField (2^15*p) q t u band a b false D C))++
          (cstream A w (packedInterval a (b-a) C)++tail) ∧
      F.R 138 = cstream A w (couplingCoefficientPageInterval (2^15*p) q s t u band a b a (b-a)) ∧
      F.R 139 = List.replicate (couplingCoefficientPageInterval (2^15*p) q s t u band a b a (b-a)).length tick ∧
      F.R 140 = List.replicate (2*band+1) tick ∧
      CouplingIntervalMetadata V s t band a b a (b-a) (embStk packedHaloRuntimeReg F) ∧
      (∀ k, ‖value q (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l j rhsExp) ∧
      (∀ k, Fits w (D k)) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t band a b)
        (fun k => (value q (D k)).re) x (1/(2 : ℝ)^j) ∧
      (∀ z ∈ rows,
        (|gv q z.re| ≤ (2 : ℝ)^(q/2) ∧ |gv q z.im| ≤ (2 : ℝ)^(q/2)) ∧
        (|gv q (normalizeBoundaryWord q (q/2-1) z).re| ≤ 1/2 ∧
          |gv q (normalizeBoundaryWord q (q/2-1) z).im| ≤ 1/2)) ∧
      PackedBoundarySolveWorkspace q F ∧ F.R 116 = List.replicate B.card tick ∧
      F.R 167 = couplingSourceIntervalMaskSymbols true A s t band a b a (b-a) ∧
      (∀ i : Fin 117, i ≠ 93 → i ≠ 110 → i ≠ 116 → F.R ⟨i.val,by omega⟩ = []) ∧
      CouplingMasterHeaders (2^15*p) q w s t u band a b (embStk packedHaloRuntimeReg F) ∧
      (F.R 118).length = executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1 ∧
      (F.R 120).length = l ∧
      (∀ k ∈ ([125,128,127,129,131,133,134,135,136,153,158,166] : List (Fin 242)), F.R k = []) ∧ F.R 238 = S.R 238 ∧
      ∀ i ∈ B, ∀ k ∈ B, |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i k-
        (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
          (haloInterior s t band a b).toList).1 i k| ≤ 1/(2 : ℝ)^bits := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let j := boundaryHaloTarget p u target rhsExp B.card
  obtain ⟨hq,hstage,hw⟩ := boundaryHaloTarget_sizing p u l target rhsExp B.card
  obtain ⟨v₁,S₁,n₁,columns,hu₁,hn₁,he₁,hinputFrame,houtputFrame,hrawTable,hstock,hlen,hformat,hcolumns,hstageInv,hsolve,hbo,hhf,hdf,
    hvk,h224,h225,hleft',hmul,hmaster,h223,h184,h220,h221,herrorTable,hnative,hmeta,hbuffer,h93,hheader⟩ :=
    packedBoundaryFactoryGeometryUsing_spec (body := body) freshGeometry hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget
      hband has hbs hpad v S (cstream A (executionWidth p l j rhsExp) (packedInterval a (b-a) C)++tail)
      h109 h115 h116 hleft hready haMaster hbMaster h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew
      h132left hV h155 h165 hfitV hgeometry
  have hcarry (k : Fin 168) (hk : 117 ≤ k.val) (h143k : k ≠ 143)
      (hnot : packedHaloRuntimeReg k ∉ packedBoundaryGeometryPorts) :
      (embStk packedHaloRuntimeReg S₁).R k = (embStk packedHaloRuntimeReg S).R k := by
    exact hheader _ hk k.isLt
      (fun he => h143k (Fin.ext (congrArg (fun i : Fin 242 => i.val) he))) hnot
  have hmasters : ∀ r ∈ groupHeaderCopies,
      ((embStk packedHaloRuntimeReg S₁).R (packedHeaderReg r.1)).length =
        groupHeaderValue (2^15*p) (executionStagePrecision p l j rhsExp+1)
          (executionPrecision p l j rhsExp) l s t u (PhaseCellBand.width p u) 0 r.1 := by
    rw [hq,hstage]
    intro r hr
    have hh := hready.masters r hr
    simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      rw [hcarry _ (by decide) (by decide) (by decide)]
      simpa [embStk,packedHaloRuntimeReg,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,
        preparedBoundaryCoreReg,packedBoundaryFactorReg,packedBoundaryTableRouting,
        Equiv.swap_apply_def,packedHeaderReg,groupHeaderValue,hq,hstage] using hh
  have hfresh' : ∀ k ∈ [(125 : Fin 168),127,130,133,138,129,131,134,135,136,140,153,166],
      (embStk packedHaloRuntimeReg S₁).R k = [] := by
    intro k hk
    have he : (embStk packedHaloRuntimeReg S₁).R k = (embStk packedHaloRuntimeReg S).R k := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact hcarry _ (by decide) (by decide) (by decide)
    exact he.trans (hfresh k hk)
  have hleftHalo : ∀ k ∈ [(121 : Fin 168),122,123,124], (embStk packedHaloRuntimeReg S₁).L k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact hleft' 121
    · exact hleft' 122
    · exact hleft' 123
    · exact hleft' 124
  have hθpos : 0 < (t : ℝ)/s-1 := lt_of_lt_of_le (by positivity : 0 < 1/(4*(p : ℝ))) hθ
  obtain ⟨v₂,F,n₂,D,hu₂,hn₂,he₂,hdata,hhigh,hleftFinal⟩ := placedPackedHaloRealBoundaryData_exec
    (body := body) (target := j) (boundaryTarget := target) hR hQ hA (by omega) hst hu hαu hθpos hgap hbudget hpad
    C hC hab hbs hband hwide hVeq hwV hcoords hunits tail E outputTail v₁ S₁
    (by simpa [embStk,packedHaloRuntimeReg,packedBoundaryTableRouting,Equiv.swap_apply_def] using hnative)
    hmasters
    (by rw [hcarry 141 (by decide) (by decide) (by decide)]
        simpa [embStk,packedHaloRuntimeReg,packedBoundaryFactorReg,packedBoundaryTableRouting,Equiv.swap_apply_def] using haMaster)
    (by rw [hcarry 142 (by decide) (by decide) (by decide)]
        simpa [embStk,packedHaloRuntimeReg,packedBoundaryFactorReg,packedBoundaryTableRouting,Equiv.swap_apply_def] using hbMaster)
    hmeta
    (by rw [hcarry 157 (by decide) (by decide) (by decide)]; exact h157)
    (hbuffer.trans houtput) hE hfresh' haLt hfitV
    (by rw [hcarry 139 (by decide) (by decide) (by decide)]
        simpa [embStk,packedHaloRuntimeReg,packedBoundaryFactorReg,packedBoundaryTableRouting,Equiv.swap_apply_def] using h139)
    (by simpa [embStk,packedHaloRuntimeReg,packedBoundaryFactorReg,packedBoundaryTableRouting,Equiv.swap_apply_def] using hvk)
    hleftHalo hsep
    (by rw [hcarry 158 (by decide) (by decide) (by decide)]; exact h158)
    (by rw [hcarry 167 (by decide) (by decide) (by decide)]; exact h167)
    hrange hdom hq x hx
  rw [hq,hw] at hdata
  rcases hdata with ⟨h93',hfold,hcount,hmask,hsource,houtput',hproj,hDnorm,hDfits,hword,
    hpage,hpageCount,hrow,hgeometry,hqueue,hzero,h135,hframe,haccuracy,hbound,hleftView,hkeys⟩
  have hinp : F.inp = S₁.inp := congrArg (fun G : Stacks 117 A => G.inp) hproj
  have hout : F.out = S₁.out := congrArg (fun G : Stacks 117 A => G.out) hproj
  have hfactor := packedBoundaryFactorState_of_high_frame S₁ F (fun k hk => (hhigh k hk).2)
  have hpages := (PackedBoundaryFactorPages.mk hbo hhf hdf).of_solution_frame
    (fun k hk _ => (hhigh k hk).2)
  refine ⟨v₂,F,n₁+n₂,columns,D,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,hinp.trans hinputFrame,hout.trans houtputFrame,
    (hhigh 220 (by decide)).2.trans hrawTable,
    packedBoundaryFactorStock_of_high_frame S₁ F (fun i hi => (hhigh i hi).2) hstock,
    hlen,hformat,hcolumns,hstageInv,?_,?_,?_,?_,h93'.trans h93,hfold,houtput',hsource,hpage,hpageCount,
    hrow,hgeometry,hDnorm,hDfits,haccuracy,hbound,?_,?_,?_,?_,?_,?_,?_,?_,?_,herrorTable⟩
  · rw [hfactor]; exact hsolve.update_vk _
  · exact hpages.lower
  · exact hpages.upper
  · exact hpages.reciprocal

  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro i
      exact (congrFun hleftFinal _).trans (hleft' i)
    · intro i
      have hi := i.isLt
      have hh := congrArg (fun N : Stacks 117 A => N.R ⟨i.val,by omega⟩) hproj
      simpa [embStk,packedHaloRuntimeReg,packedCellCoreReg,countedReleasedCellBank,releasedCellBank,
        preparedBoundaryCoreReg,packedBoundaryFactorReg,boundaryFactorMulReg,Fin.ext_iff,
        show i.val ≠ 93 by omega,show i.val ≠ 110 by omega,show i.val ≠ 116 by omega,
        show i.val ≠ 140 by omega,show i.val ≠ 143 by omega,show i.val ≠ 206 by omega,
        show i.val < 154 by omega] using hh
    · have h119 : F.R 119 = S₁.R 119 := (hframe 119 (by decide) (by decide) (by decide)).2
      simpa [embStk,packedBoundaryFactorReg,packedBoundaryTableRouting,Equiv.swap_apply_def,h119] using hmaster
    · have hh := (hhigh 237 (by decide)).2
      simpa [embStk,packedBoundaryFactorReg,packedBoundaryTableRouting,Equiv.swap_apply_def,hh] using h223
    · have hh := (hhigh 198 (by decide)).2
      simpa [embStk,packedBoundaryFactorReg,packedBoundaryTableRouting,Equiv.swap_apply_def,hh] using h184
    · have hh := (hhigh 234 (by decide)).2
      simpa [embStk,packedBoundaryFactorReg,packedBoundaryTableRouting,Equiv.swap_apply_def,hh] using h220
    · have hh := (hhigh 235 (by decide)).2
      simpa [embStk,packedBoundaryFactorReg,packedBoundaryTableRouting,Equiv.swap_apply_def,hh] using h221
    · have hh := (hhigh 239 (by decide)).2
      simpa [embStk,packedBoundaryFactorReg,packedBoundaryTableRouting,Equiv.swap_apply_def,hh,h239] using h225

  · simpa [embStk,packedHaloRuntimeReg] using hcount
  · simpa [embStk,packedHaloRuntimeReg] using hmask
  · intro i h93i h110i h116i
    have hh := congrArg (fun N : Stacks 117 A => N.R i) hproj
    simpa [embStk,packedHaloRuntimeReg,packedCellCoreReg,countedReleasedCellBank,releasedCellBank,
      Function.update_of_ne h116i,show i.val ≠ 93 from fun he => h93i (Fin.ext he),
      show i.val ≠ 110 from fun he => h110i (Fin.ext he)] using hh
  · constructor
    · rw [(hframe 117 (by decide) (by decide) (by decide)).2]
      simpa [packedHeaderReg,groupHeaderValue,j,hq] using hmasters (117,114) (by decide)
    · rw [(hframe 119 (by decide) (by decide) (by decide)).2]
      simpa [packedHeaderReg,groupHeaderValue,j,hq] using hmasters (119,112) (by decide)
    · rw [(hframe 121 (by decide) (by decide) (by decide)).2]
      simpa [packedHeaderReg,groupHeaderValue,j,hq] using hmasters (121,97) (by decide)
    · rw [(hframe 122 (by decide) (by decide) (by decide)).2]
      simpa [packedHeaderReg,groupHeaderValue,j,hq] using hmasters (122,98) (by decide)
    · rw [(hframe 123 (by decide) (by decide) (by decide)).2]
      simpa [packedHeaderReg,groupHeaderValue,j,hq] using hmasters (123,99) (by decide)
    · rw [(hframe 124 (by decide) (by decide) (by decide)).2]
      simpa [packedHeaderReg,groupHeaderValue,j,hq] using hmasters (124,100) (by decide)
    · rw [(hframe 141 (by decide) (by decide) (by decide)).2,
        hcarry 141 (by decide) (by decide) (by decide)]
      simpa [embStk,packedHaloRuntimeReg,packedBoundaryFactorReg,packedBoundaryTableRouting,
        Equiv.swap_apply_def] using haMaster
    · rw [(hframe 142 (by decide) (by decide) (by decide)).2,
        hcarry 142 (by decide) (by decide) (by decide)]
      simpa [embStk,packedHaloRuntimeReg,packedBoundaryFactorReg,packedBoundaryTableRouting,
        Equiv.swap_apply_def] using hbMaster
    · exact hword
  · change ((embStk packedHaloRuntimeReg F).R 118).length = _
    rw [(hframe 118 (by decide) (by decide) (by decide)).2]
    simpa [packedHeaderReg,groupHeaderValue,j,hstage] using hmasters (118,101) (by decide)
  · change ((embStk packedHaloRuntimeReg F).R 120).length = _
    rw [(hframe 120 (by decide) (by decide) (by decide)).2]
    simpa [packedHeaderReg,groupHeaderValue] using hmasters (120,109) (by decide)
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hkeys.1
    · exact hkeys.2
    · exact hzero
    · exact ((hframe 129 (by decide) (by decide) (by decide)).2).trans (hfresh' 129 (by decide))
    · exact ((hframe 131 (by decide) (by decide) (by decide)).2).trans (hfresh' 131 (by decide))
    · exact ((hframe 133 (by decide) (by decide) (by decide)).2).trans (hfresh' 133 (by decide))
    · exact ((hframe 134 (by decide) (by decide) (by decide)).2).trans (hfresh' 134 (by decide))
    · exact h135
    · exact ((hframe 136 (by decide) (by decide) (by decide)).2).trans (hfresh' 136 (by decide))
    · exact ((hframe 153 (by decide) (by decide) (by decide)).2).trans (hfresh' 153 (by decide))
    · change (embStk packedHaloRuntimeReg F).R 158 = []
      rw [(hframe 158 (by decide) (by decide) (by decide)).2,
        hcarry 158 (by decide) (by decide) (by decide)]
      exact h158
    · exact ((hframe 166 (by decide) (by decide) (by decide)).2).trans (hfresh' 166 (by decide))
  · have hh := (hhigh 238 (by decide)).2
    simpa [embStk,packedBoundaryFactorReg,packedBoundaryTableRouting,Equiv.swap_apply_def,hh] using h224

theorem packedHaloBoundarySetup_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C : ZMod s → GaussianInt) (tail E outputTail : List (Fin (A+4)))
    (v : HS 242 Q A U) (S : Stacks 242 A)
    (h109 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 109 = []) (h115 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 115 = []) (h116 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 116 = [])
    (hleft : ∀ i : Fin 224, (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).L (preparedBoundaryCoreReg i) = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u
      (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u
        (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
      l s t u (PhaseCellBand.width p u) 0 0 (cstream A (executionWidth p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (packedInterval a (b-a) C)++tail)
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S))))))))
    (haMaster : ((embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 141).length = a) (hbMaster : ((embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 142).length = b)
    (h0 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 0 = []) (h139 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 139 = []) (h127 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 127 = []) (h138 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 138 = [])
    (h143 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 143 = []) (h147 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 147 = []) (h151 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 151 = []) (h153 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 153 = [])
    (h152 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R (preparedBoundaryCoreReg i) = []) (h132left : S.L 132 = [])
    (hV : (S.R 163).length = V)
    (h155 : S.R 155 = binSyms V a) (h165 : S.R 165 = binSyms V (b-a))
    (hfitV : a+((b-a)+2*PhaseCellBand.width p u)+s < 2^V)
    (hgeometryBlank : ∀ k ∈ [(145 : Fin 242),146,147,148,149,151,154,156,164], S.R k = [])
    (h239 : S.R 239 = [])
    (hab : a ≤ b) (haLt : a < s) (hsep : b-a+PhaseCellBand.width p u ≤ s)
    (hwide : 8*(t+1)^2+4*PhaseCellBand.width p u+8 < 2^V)
    (hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (2*(executionPrecision p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp)+8) t u)
    (hwV : (executionWidth p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) < 2^V) (hcoords : b < 2^V) (hunits : b*(executionWidth p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) < 2^V)
    (hC : ∀ k, ‖value (executionPrecision p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (h157 : (S.R 157).length ≤ V) (h158 : S.R 158 = []) (h167 : S.R 167 = [])
    (houtput : S.R 132 = E++outputTail) (hE : E.length = (b-a)*(executionWidth p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp))
    (hfresh : ∀ k ∈ [(125 : Fin 168),127,130,133,138,129,131,134,135,136,140,153,166],
      (embStk packedHaloRuntimeReg S).R k = [])
    (hrange : EncodedRange A (executionWidth p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (executionPrecision p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp)
      (interiorOutputExponent p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) E)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l (boundaryHaloTarget p u target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (C k)).re)) :
    let band := PhaseCellBand.width p u
    let B := haloBoundary s t band a b
    let j := boundaryHaloTarget p u target rhsExp B.card
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let W := 12*band+1
    let K := factorNewtonSteps p q
    ∃ v' F m, ∃ columns : List (ZMod s → GaussianInt), ∃ D : ZMod s → GaussianInt,
      let σ := boundaryFactorState (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg F))
      let AZ := factorRankIntegerMatrix B W columns
      let rows := (bFoldOrder s B).map (fun i => realPartWord
        (couplingRowField (2^15*p) q t u band a b false D C i))
      v'.user = v.user ∧
      m ≤ constructedBoundaryFactorCost p u l s t a b target rhsExp+
        (2*(B.card*publicationGeometryWidth t band+publicationGeometryWidth t band+B.card)+7)+
        ((s+t+band+a+b)*(4*V+10)+56*V+77)+
        packedHaloRealBoundaryDataCost p l s t u j rhsExp a b V ∧
      Exec body (packedHaloBoundarySetup hR hQ) (mk v S) m (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      F.R 220 = bandTableWords A w B W columns 0++S.R 220 ∧
      BoundaryFactorStock (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg F)) (boundaryFactorStockBound q w band B.card) ∧
      columns.length = B.card ∧ ColumnFamilyFormat w columns ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (haloVertices s a b) (haloInterior s t band a b).toList).1
        (1/(2 : ℝ)^bits) columns ∧
      SchurDominance.StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
        (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits)) (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) ∧
      BoundarySolveReady σ q w W B.card ∧
      σ .bo = cstream A w ((naturalLineLc q K W B.card AZ).map colC).flatten ∧
      σ .hf = cstream A w ((naturalLineUc q K W B.card AZ).map colC).flatten ∧
      σ .df = cstream A w ((naturalLineRcs q K W B.card AZ).map fun z => (⟨z,0⟩ : GaussianInt)) ∧
      F.R 93 = S.R 93 ∧ F.R 143 = cstream A w rows ∧
      F.R 132 = cstream A w (packedInterval a (b-a) D)++outputTail ∧
      F.R 110 = cstream A w (packedInterval a (b-a)
        (guardedCouplingRowField (2^15*p) q t u band a b false D C))++
          (cstream A w (packedInterval a (b-a) C)++tail) ∧
      F.R 138 = cstream A w (couplingCoefficientPageInterval (2^15*p) q s t u band a b a (b-a)) ∧
      F.R 139 = List.replicate (couplingCoefficientPageInterval (2^15*p) q s t u band a b a (b-a)).length tick ∧
      F.R 140 = List.replicate (2*band+1) tick ∧
      CouplingIntervalMetadata V s t band a b a (b-a) (embStk packedHaloRuntimeReg F) ∧
      (∀ k, ‖value q (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l j rhsExp) ∧
      (∀ k, Fits w (D k)) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t band a b)
        (fun k => (value q (D k)).re) x (1/(2 : ℝ)^j) ∧
      (∀ z ∈ rows,
        (|gv q z.re| ≤ (2 : ℝ)^(q/2) ∧ |gv q z.im| ≤ (2 : ℝ)^(q/2)) ∧
        (|gv q (normalizeBoundaryWord q (q/2-1) z).re| ≤ 1/2 ∧
          |gv q (normalizeBoundaryWord q (q/2-1) z).im| ≤ 1/2)) ∧
      PackedBoundarySolveWorkspace q F ∧ F.R 116 = List.replicate B.card tick ∧
      F.R 167 = couplingSourceIntervalMaskSymbols true A s t band a b a (b-a) ∧
      (∀ i : Fin 117, i ≠ 93 → i ≠ 110 → i ≠ 116 → F.R ⟨i.val,by omega⟩ = []) ∧
      CouplingMasterHeaders (2^15*p) q w s t u band a b (embStk packedHaloRuntimeReg F) ∧
      (F.R 118).length = executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1 ∧
      (F.R 120).length = l ∧
      (∀ k ∈ ([125,128,127,129,131,133,134,135,136,153,158,166] : List (Fin 242)), F.R k = []) ∧ F.R 238 = S.R 238 ∧
      ∀ i ∈ B, ∀ k ∈ B, |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i k-
        (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
          (haloInterior s t band a b).toList).1 i k| ≤ 1/(2 : ℝ)^bits := by
  exact packedHaloBoundarySetupUsing_exec (body := body) true
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
    C tail E outputTail v S h109 h115 h116 hleft hready haMaster hbMaster h0 h139 h127 h138
    h143 h147 h151 h153 h152 hnew h132left hV h155 h165 hfitV hgeometryBlank h239
    hab haLt hsep hwide hVeq hwV hcoords hunits hC h157 h158 h167 houtput hE hfresh hrange hdom x hx

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
