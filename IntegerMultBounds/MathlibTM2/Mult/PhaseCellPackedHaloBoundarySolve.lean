module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBoundarySetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloResidualSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloBoundarySolutionAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolutionField
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

noncomputable def packedHaloBoundarySolve (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 242 Q A U :=
  .seq (packedHaloBoundarySetup hR hQ) (packedPreparedResidualSolve hQ)

theorem packedHaloBoundarySolve_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
      let AZ := factorRankIntegerMatrix B W columns
      let Lc := naturalLineLc q K W B.card AZ
      let Uc := naturalLineUc q K W B.card AZ
      let rcs := naturalLineRcs q K W B.card AZ
      let rows := (bFoldOrder s B).map (fun i => realPartWord
        (couplingRowField (2^15*p) q t u band a b false D C i))
      let ys := (bandSolveVec q W Lc Uc rcs (rows.map (normalizeBoundaryWord q (q/2-1)))).map
        (unscaleBoundaryWord q)
      v'.user = v.user ∧
      m ≤ constructedBoundaryFactorCost p u l s t a b target rhsExp+
        (2*(B.card*publicationGeometryWidth t band+publicationGeometryWidth t band+B.card)+7)+
        ((s+t+band+a+b)*(4*V+10)+56*V+77)+
        packedHaloRealBoundaryDataCost p l s t u j rhsExp a b V+
        preparedResidualSolveCost q w B.card W ∧
      Exec body (packedHaloBoundarySolve hR hQ) (mk v S) m (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      F.R 220 = bandTableWords A w B W columns 0++S.R 220 ∧
      BoundaryFactorStock (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg F)) (boundaryFactorStockBound q w band B.card) ∧
      columns.length = B.card ∧ ColumnFamilyFormat w columns ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (haloVertices s a b) (haloInterior s t band a b).toList).1
        (1/(2 : ℝ)^bits) columns ∧
      SchurDominance.StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
        (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits)) (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) ∧
      BoundarySolveReady (boundaryFactorState (embStk preparedBoundaryCoreReg
        (embStk packedBoundaryFactorReg F))) q w W B.card ∧
      F.R 143 = [] ∧ F.R 238 = cstream A w ys++S.R 238 ∧ F.R 93 = S.R 93 ∧
      F.R 132 = cstream A w (packedInterval a (b-a) D)++outputTail ∧
      F.R 110 = cstream A w (packedInterval a (b-a)
        (guardedCouplingRowField (2^15*p) q t u band a b false D C))++
          (cstream A w (packedInterval a (b-a) C)++tail) ∧
      F.R 138 = cstream A w (couplingCoefficientPageInterval (2^15*p) q s t u band a b a (b-a)) ∧
      F.R 139 = List.replicate (couplingCoefficientPageInterval (2^15*p) q s t u band a b a (b-a)).length tick ∧
      F.R 140 = List.replicate (2*band+1) tick ∧
      CouplingIntervalMetadata V s t band a b a (b-a) (embStk packedHaloRuntimeReg F) ∧
      PackedBoundarySolveWorkspace q F ∧ F.R 116 = List.replicate B.card tick ∧
      F.R 167 = couplingSourceIntervalMaskSymbols true A s t band a b a (b-a) ∧
      (∀ i : Fin 117, i ≠ 93 → i ≠ 110 → i ≠ 116 → F.R ⟨i.val,by omega⟩ = []) ∧
      CouplingMasterHeaders (2^15*p) q w s t u band a b (embStk packedHaloRuntimeReg F) ∧
      (F.R 118).length = executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1 ∧
      (F.R 120).length = l ∧
      (∀ k ∈ ([127,129,131,133,134,135,136,153,158,166] : List (Fin 242)), F.R k = []) ∧
      (∀ k, ‖value q (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l j rhsExp) ∧
      (∀ k, Fits w (D k)) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t band a b)
        (fun k => (value q (D k)).re) x (1/(2 : ℝ)^j) ∧
      ys.length = B.card ∧ (∀ z ∈ ys, Fits w z) ∧
      ∀ (y : ZMod s → ℝ),
        SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) y
          (fun k => (value q (C k)).re) →
        (∀ i < B.card, ‖value q (ys.getD i 0)-(y (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^target ∧
          ‖value q (ys.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp) ∧
        PhaseCellInterface.ErrorOn B (fun i => (boundaryFoldedRead q w B (F.R 238) i).re) y
          (3/(2 : ℝ)^target) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let j := boundaryHaloTarget p u target rhsExp B.card
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let W := 12*PhaseCellBand.width p u+1
  let K := factorNewtonSteps p q
  obtain ⟨v₁,S₁,n₁,columns,D,hu₁,hn₁,he₁,hinputFrame,houtputFrame,hrawTable,hstock,hlen,hformat,hcolumns,hstage,hsolve,hbo,hhf,hdf,
    h93,hfold,hpacked,hsource,hpage,hcount,hrows,hmeta,hDnorm,hDfits,haccuracy,hbound,hwork,hboundaryCount,hboundaryMask,hnativeBlank,hcouplingHeaders,hstageMaster,hlevelMaster,hcouplingScratch,h238,htable⟩ :=
    packedHaloBoundarySetup_exec (body := body) hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget
      hband has hbs hpad C tail E outputTail v S h109 h115 h116 hleft hready haMaster hbMaster
      h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew h132left hV h155 h165 hfitV hgeometryBlank
      h239 hab haLt hsep hwide hVeq hwV hcoords hunits hC h157 h158 h167 houtput hE hfresh hrange hdom x hx
  obtain ⟨hq,_,_⟩ := boundaryHaloTarget_sizing p u l target rhsExp B.card
  dsimp only [B] at hq
  have hC' : ∀ k, ‖value q (C k)‖ ≤ (2 : ℝ)^rhsExp := by simpa only [hq] using hC
  have hx' : SchurDominance.Solves (realMatrix s t p u)
      (haloInterior s t (PhaseCellBand.width p u) a b) x (fun k => (value q (C k)).re) := by
    simpa only [hq] using hx
  have hθpos : 0 < (t : ℝ)/s-1 := lt_of_lt_of_le (by positivity : 0 < 1/(4*(p : ℝ))) hθ
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := packedHaloResidualSolve_exec (body := body) hQ hA
    p u l target rhsExp B W columns hp hlen a b j hst hαu hθpos hgap hbudget hdom
    hformat hstage C D x hC' hx' haccuracy v₁ S₁ hwork.left hwork.mul hsolve hfold hbo hhf hdf
    hwork.precision hwork.exponent hwork.scalar hwork.table hwork.padding hwork.swap
  let AZ := factorRankIntegerMatrix B W columns
  let rows := (bFoldOrder s B).map (fun i => realPartWord
    (couplingRowField (2^15*p) q t u (PhaseCellBand.width p u) a b false D C i))
  let ys := (bandSolveVec q W (naturalLineLc q K W B.card AZ) (naturalLineUc q K W B.card AZ)
    (naturalLineRcs q K W B.card AZ) (rows.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q)
  let output := cstream A w ys
  let F : Stacks 242 A := {S₁ with R := (Function.update (Function.update S₁.R 143 []) 238 (output++S₁.R 238))}
  have hreadyFinal := packedPreparedResidualSolve_ready S₁ output hsolve
  have hmetaFinal : CouplingIntervalMetadata V s t (PhaseCellBand.width p u) a b a (b-a)
      (embStk packedHaloRuntimeReg F) := by
    constructor
    · simpa [F,embStk,packedHaloRuntimeReg] using hmeta.width
    · intro k hk
      have hn : k ≠ 143 := by
        simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hv143 : k.val ≠ 143 := fun he => hn (Fin.ext he)
      have hv238 : k.val ≠ 238 := by have hi := k.isLt; omega
      simpa [F,embStk,packedHaloRuntimeReg,Function.update_apply,Fin.ext_iff,hv143,hv238] using hmeta.encoded k hk
  have hcouplingFinal := hcouplingHeaders.of_frame (F := embStk packedHaloRuntimeReg F) (by
    intro k hk
    have hn : k ≠ 143 := by
      simp only [couplingMasterPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hv143 : k.val ≠ 143 := fun he => hn (Fin.ext he)
    have hv238 : k.val ≠ 238 := by have hi := k.isLt; omega
    simp [F,embStk,packedHaloRuntimeReg,Fin.ext_iff,hv143,hv238])
  have hsemantic (y : ZMod s → ℝ)
      (hy : SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) y
        (fun k => (value q (C k)).re)) :=
    haloBoundary_solution_accuracy A p u l target rhsExp a b W columns (by omega)
      hp hst hα hwidth hαu hθ hgap hbudget hdom hlen hformat hstage htable C D x y hC' hx' haccuracy hy
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  obtain ⟨y,hy⟩ := SchurDominance.solves_exists (realMatrix s t p u) (haloVertices s a b)
    (1/(8*(p : ℝ))) (by positivity)
    (SchurDominance.dominates_mono _ Finset.univ _ _ (Finset.subset_univ _) hdom)
    (fun k => (value q (C k)).re)
  have hformatSol := hsemantic y hy
  refine ⟨v₂,F,n₁+n₂,columns,D,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,(by simpa [F] using hinputFrame),
    (by simpa [F] using houtputFrame),(by simpa [F] using hrawTable),
    (by
      apply hstock.of_frame
      intro i hi hn
      have he206 : preparedBoundaryCoreReg i ≠ (206 : Fin 226) := by
        intro he; exact hn (Fin.ext (congrArg (fun k : Fin 226 => k.val) he))
      have hrange := packedBoundaryFactorReg_high_range (preparedBoundaryCoreReg i) hi he206
      have hi224 := i.isLt
      simp [embStk,preparedBoundaryCoreReg,packedBoundaryFactorReg,F,Fin.ext_iff,
        show i.val ≠ 140 by omega,show i.val ≠ 143 by omega,
        show i.val ≠ 206 from fun he => hn (Fin.ext he),show ¬ i.val < 154 by omega,
        show i.val+14 ≠ 143 by omega,show i.val+14 ≠ 238 by omega]),
    hlen,hformat,hcolumns,hstage,hreadyFinal,?_,?_,?_,?_,?_,?_,?_,?_,hmetaFinal,hwork.publish output,(by simpa [F] using hboundaryCount),(by simpa [F] using hboundaryMask),?_,hcouplingFinal,(by simpa [F] using hstageMaster),(by simpa [F] using hlevelMaster),?_,hDnorm,hDfits,haccuracy,hformatSol.1,hformatSol.2.1,?_⟩
  · simp [F]
  · simp [F,output,ys,rows,h238]
    rfl
  · simpa [F] using h93
  · simpa [F] using hpacked
  · simpa [F] using hsource
  · simpa [F] using hpage
  · simpa [F] using hcount
  · simpa [F] using hrows

  · intro i h93i h110i h116i
    have hi := i.isLt
    simpa [F,Function.update_apply,Fin.ext_iff,show i.val ≠ 143 by omega,
      show i.val ≠ 238 by omega] using hnativeBlank i h93i h110i h116i

  · intro k hk
    have hn : k ≠ 143 ∧ k ≠ 238 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [F,Function.update_of_ne hn.1,Function.update_of_ne hn.2] using hcouplingScratch k hk

  · intro y hy
    refine ⟨(hsemantic y hy).2.2,?_⟩
    have hsrc : F.R 238 = cstream A w ys++S.R 238 := by simp [F,output,h238]
    rw [hsrc]
    exact boundaryFoldedRead_error (by omega) q w (by dsimp [w,executionWidth]; omega)
      B ys hformatSol.1 hformatSol.2.1 (S.R 238) y (3/(2 : ℝ)^target)
      (fun i hi => ((hsemantic y hy).2.2 i hi).1)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
