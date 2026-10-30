module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingMasterHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryAccuracy

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedPackedHaloRealBoundaryData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloResidualSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBoundaryWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolveWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloRealBoundaryData
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Run the complete halo RHS producer beside the retained factor workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

noncomputable def packedHaloPreparedBoundary (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 242 Q A U :=
  .seq (placedPackedHaloRealBoundaryData hR hQ) (packedPreparedResidualSolve hQ)

theorem packedHaloPreparedBoundary_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target rhsExp a b V boundaryTarget : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hα : 0 < α) (hwidth : 8*p ≤ 2^u) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (hab : a ≤ b) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (hwide : 8*(t+1)^2+4*PhaseCellBand.width p u+8 < 2^V)
    (hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (2*executionPrecision p l target rhsExp+8) t u)
    (hwV : executionWidth p l target rhsExp < 2^V)
    (hcoords : b < 2^V) (hunits : b*executionWidth p l target rhsExp < 2^V)
    (tail E outputTail : List (Fin (A+4)))
    (v : HS 242 Q A U) (S : Stacks 242 A)
    (hnative : embStk packedCellCoreReg (embStk packedHaloRuntimeReg S) = releasedCellBank []
      (cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail) ((embStk packedHaloRuntimeReg S).R 93) (embStk packedHaloRuntimeReg S).inp (embStk packedHaloRuntimeReg S).out)
    (hmasters : ∀ r ∈ groupHeaderCopies, ((embStk packedHaloRuntimeReg S).R (packedHeaderReg r.1)).length =
      groupHeaderValue (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 r.1)
    (ha : ((embStk packedHaloRuntimeReg S).R 141).length = a) (hb' : ((embStk packedHaloRuntimeReg S).R 142).length = b)
    (hmeta : CouplingIntervalMetadata V s t (PhaseCellBand.width p u) a b a (b-a) (embStk packedHaloRuntimeReg S))
    (h157 : ((embStk packedHaloRuntimeReg S).R 157).length ≤ V)
    (houtput : (embStk packedHaloRuntimeReg S).R 132 = E++outputTail) (hE : E.length = (b-a)*executionWidth p l target rhsExp)
    (hfresh : ∀ k ∈ [(125 : Fin 168),127,130,133,138,129,131,134,135,136,140,153,166], (embStk packedHaloRuntimeReg S).R k = [])
    (haLt : a < s) (hfitV : a+((b-a)+2*PhaseCellBand.width p u)+s < 2^V)
    (h139 : (embStk packedHaloRuntimeReg S).R 139 = []) (h143 : (embStk packedHaloRuntimeReg S).R 143 = [])
    (hleft : ∀ k ∈ [(121 : Fin 168),122,123,124], (embStk packedHaloRuntimeReg S).L k = [])
    (hsep : b-a+PhaseCellBand.width p u ≤ s) (h158 : (embStk packedHaloRuntimeReg S).R 158 = []) (h167 : (embStk packedHaloRuntimeReg S).R 167 = [])
    (hrange : EncodedRange A (executionWidth p l target rhsExp) (executionPrecision p l target rhsExp)
      (interiorOutputExponent p l target rhsExp) E)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (hq : executionPrecision p l target rhsExp = executionPrecision p l
      (initialSchurTarget p u (boundaryTableBits p boundaryTarget rhsExp
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re)) :
    let band := PhaseCellBand.width p u
    let B := haloBoundary s t band a b
    let bits := boundaryTableBits p boundaryTarget rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let W := 12*PhaseCellBand.width p u+1
    ∀ columns : List (ZMod s → GaussianInt),
    PreparedBoundaryColumns A p bits q w W B columns →
    target = boundaryHaloTarget p u boundaryTarget rhsExp B.card →
    (∀ i ∈ B, ∀ j ∈ B, |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
      (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
        (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^bits) →
    PackedPreparedBank q w W B.card S →
    let AZ := factorRankIntegerMatrix B W columns
    let K := factorNewtonSteps p q
    let Lc := naturalLineLc q K W B.card AZ
    let Uc := naturalLineUc q K W B.card AZ
    let rcs := naturalLineRcs q K W B.card AZ
    PackedBoundaryFactorPages (cstream A w (Lc.map colC).flatten)
      (cstream A w (Uc.map colC).flatten)
      (cstream A w (rcs.map fun z => (⟨z,0⟩ : GaussianInt))) S →
    ∃ v', ∃ T : Stacks 242 A, ∃ m, ∃ D : ZMod s → GaussianInt,
      let rows := (bFoldOrder s B).map (fun i => realPartWord
        (couplingRowField (2^15*p) q t u (PhaseCellBand.width p u) a b false D C i))
      let Z := cstream A w (packedInterval a (b-a)
        (guardedCouplingRowField (2^15*p) q t u band a b false D C))
      let folded := cstream A w rows
      let ys := ((bandSolveVec q W Lc Uc rcs
        (rows.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q))
      let output := cstream A w ys
      let F := {T with R := Function.update (Function.update T.R 143 []) 238 (output++T.R 238)}
      v'.user = v.user ∧
      m ≤ packedHaloRealBoundaryDataCost p l s t u target rhsExp a b V+
        preparedResidualSolveCost q w B.card W ∧
      Exec body (packedHaloPreparedBoundary hR hQ)
        (mk v S) m (mk v' F) ∧
      PackedPreparedBank q w W B.card F ∧
      (
      (embStk packedHaloRuntimeReg T).R 93 = (embStk packedHaloRuntimeReg S).R 93 ∧ (embStk packedHaloRuntimeReg T).R 143 = folded ∧ (embStk packedHaloRuntimeReg T).R 116 = List.replicate B.card tick ∧
      (embStk packedHaloRuntimeReg T).R 167 = couplingSourceIntervalMaskSymbols true A s t band a b a (b-a) ∧
      (embStk packedHaloRuntimeReg T).R 110 = Z++(cstream A w (packedInterval a (b-a) C)++tail) ∧
      (embStk packedHaloRuntimeReg T).R 132 = cstream A w (packedInterval a (b-a) D)++outputTail ∧
      embStk packedCellCoreReg (embStk packedHaloRuntimeReg T) = countedReleasedCellBank B.card Z
        (cstream A w (packedInterval a (b-a) C)++tail) ((embStk packedHaloRuntimeReg S).R 93) (embStk packedHaloRuntimeReg S).inp (embStk packedHaloRuntimeReg S).out ∧
      (∀ k, ‖value q (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp) ∧
      (∀ k, Fits w (D k)) ∧ ((embStk packedHaloRuntimeReg T).R 130).length = w ∧
      (embStk packedHaloRuntimeReg T).R 138 = cstream A w (couplingCoefficientPageInterval (2^15*p) q s t u band a b a (b-a)) ∧
      (embStk packedHaloRuntimeReg T).R 139 = List.replicate (couplingCoefficientPageInterval (2^15*p) q s t u band a b a (b-a)).length tick ∧
      (embStk packedHaloRuntimeReg T).R 140 = List.replicate (2*band+1) tick ∧
      CouplingIntervalMetadata V s t band a b a (b-a) (embStk packedHaloRuntimeReg T) ∧ (embStk packedHaloRuntimeReg T).R 126 = (embStk packedHaloRuntimeReg S).R 126 ∧ (embStk packedHaloRuntimeReg T).R 127 = [] ∧ (embStk packedHaloRuntimeReg T).R 135 = [] ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ∉ packedHaloInteriorPagePorts → k ≠ 167 → (embStk packedHaloRuntimeReg T).L k = (embStk packedHaloRuntimeReg S).L k ∧ (embStk packedHaloRuntimeReg T).R k = (embStk packedHaloRuntimeReg S).R k) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t band a b)
        (fun k => (value q (D k)).re) x (1/(2 : ℝ)^target) ∧
      (∀ z ∈ rows,
        (|gv q z.re| ≤ (2 : ℝ)^(q/2) ∧ |gv q z.im| ≤ (2 : ℝ)^(q/2)) ∧
        (|gv q (normalizeBoundaryWord q (q/2-1) z).re| ≤ 1/2 ∧
          |gv q (normalizeBoundaryWord q (q/2-1) z).im| ≤ 1/2)) ∧
      (embStk packedHaloRuntimeReg T).L = (embStk packedHaloRuntimeReg S).L ∧
      (embStk packedHaloRuntimeReg T).R 125 = [] ∧ (embStk packedHaloRuntimeReg T).R 128 = [] ) ∧
      PackedBoundaryFactorPages (cstream A w (Lc.map colC).flatten)
        (cstream A w (Uc.map colC).flatten)
        (cstream A w (rcs.map fun z => (⟨z,0⟩ : GaussianInt))) F ∧
      F.L = S.L ∧
      (∀ k : Fin 242, 168 ≤ k.val → k ≠ 238 → F.R k = S.R k) ∧
      (ys.length = B.card ∧ (∀ z ∈ ys, Fits w z) ∧
        ∀ y : ZMod s → ℝ, SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) y
          (fun k => (value q (C k)).re) →
          ∀ i < B.card, ‖value q (ys.getD i 0)-(y (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^boundaryTarget ∧
            ‖value q (ys.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp) ∧
      CouplingMasterHeaders (2^15*p) q w s t u band a b (embStk packedHaloRuntimeReg F) ∧
      (F.R 118).length = executionStagePrecision p l target rhsExp+1 ∧ (F.R 120).length = l ∧
      (∀ i : Fin 117, i ≠ 93 → i ≠ 110 → i ≠ 116 → F.R ⟨i.val,by omega⟩ = []) ∧
      (∀ k ∈ ([127,129,131,133,134,135,136,153,158,166] : List (Fin 242)), F.R k = []) ∧
      CouplingIntervalMetadata V s t band a b a (b-a) (embStk packedHaloRuntimeReg F) ∧
      T.R 238 = S.R 238 := by
  dsimp only
  intro columns hcolumns hcell htable hbank hpages
  have hθpos : 0 < (t : ℝ)/s-1 := lt_of_lt_of_le (by positivity : 0 < 1/(4*(p : ℝ))) hθ
  obtain ⟨v₁,T,n₁,D,hu₁,hn₁,he₁,hdata,hhigh,hleftFinal,hbankCarry,hpagesCarry⟩ :=
    placedPackedHaloRealBoundaryData_exec (body := body) hR hQ hA (by omega) hst hu hαu hθpos hgap
      hbudget hpad C hC hab hb hband hwide hVeq hwV hcoords hunits tail E outputTail v S
      hnative hmasters ha hb' hmeta h157 houtput hE hfresh haLt hfitV h139 h143 hleft
      hsep h158 h167 hrange hdom hq x hx
  have hproduced := hdata
  rcases hdata with ⟨h93,hfold,hcount,hmask,hsource,houtput',hproj,hDnorm,hDfits,hword,
    hpage,hpageCount,hrow,hgeometry,hqueue,hzero,h135,hframe,haccuracy,hbound,hleftView,hkeys⟩
  have hC' := hC
  have hx' := hx
  have hw : executionWidth p l target rhsExp = executionWidth p l
      (initialSchurTarget p u (boundaryTableBits p boundaryTarget rhsExp
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2 := by
    have he := hq
    unfold executionPrecision at he
    unfold executionWidth
    omega
  rw [hq] at hC' hx' haccuracy hfold
  rw [hw] at hfold
  rw [hq,hw] at hproduced
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := packedHaloResidualSolve_exec (body := body) hQ hA
    p u l boundaryTarget rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b)
    (12*PhaseCellBand.width p u+1) columns hp a b target hst hαu hθpos hgap hbudget hdom
    hcolumns C D x hC' hx' haccuracy v₁ T (hbankCarry _ _ _ _ hbank) hfold
    (hpagesCarry _ _ _ hpages)
  refine ⟨v₂,T,n₁+n₂,D,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,?_,hproduced,?_,hleftFinal,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (hbankCarry _ _ _ _ hbank).publish _
  · exact (hpagesCarry _ _ _ hpages).publish _
  · intro k hk hne
    have h143 : k ≠ 143 := by intro he; subst k; omega
    simpa only [Function.update_of_ne h143,Function.update_of_ne hne]
      using (hhigh k hk).2
  · have hsemantic (y : ZMod s → ℝ)
        (hy : SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) y
          (fun k => (value (executionPrecision p l (initialSchurTarget p u
            (boundaryTableBits p boundaryTarget rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) (C k)).re)) :=
      preparedBoundary_solution_accuracy A p u l boundaryTarget rhsExp a b
        (12*PhaseCellBand.width p u+1) columns (by omega) hp hst hα hwidth hαu hθ hgap hbudget hdom
        hcolumns htable C D x y hC' hx' (by simpa only [hcell] using haccuracy) hy
    obtain ⟨y,hy⟩ := SchurDominance.solves_exists (realMatrix s t p u) (haloVertices s a b)
      (1/(8*(p : ℝ))) (by positivity)
      (SchurDominance.dominates_mono _ Finset.univ _ _ (Finset.subset_univ _) hdom)
      (fun k => (value _ (C k)).re)
    exact ⟨(hsemantic y hy).1,(hsemantic y hy).2.1,fun y hy => (hsemantic y hy).2.2⟩
  · constructor
    · change ((embStk packedHaloRuntimeReg T).R 117).length = 2^15*p
      rw [(hframe 117 (by decide) (by decide) (by decide)).2]
      simpa [packedHeaderReg,groupHeaderValue,hq] using hmasters (117,114) (by decide)
    · change ((embStk packedHaloRuntimeReg T).R 119).length = _
      rw [(hframe 119 (by decide) (by decide) (by decide)).2]
      simpa [packedHeaderReg,groupHeaderValue,hq] using hmasters (119,112) (by decide)
    · change ((embStk packedHaloRuntimeReg T).R 121).length = s
      rw [(hframe 121 (by decide) (by decide) (by decide)).2]
      simpa [packedHeaderReg,groupHeaderValue,hq] using hmasters (121,97) (by decide)
    · change ((embStk packedHaloRuntimeReg T).R 122).length = t
      rw [(hframe 122 (by decide) (by decide) (by decide)).2]
      simpa [packedHeaderReg,groupHeaderValue,hq] using hmasters (122,98) (by decide)
    · change ((embStk packedHaloRuntimeReg T).R 123).length = u
      rw [(hframe 123 (by decide) (by decide) (by decide)).2]
      simpa [packedHeaderReg,groupHeaderValue,hq] using hmasters (123,99) (by decide)
    · change ((embStk packedHaloRuntimeReg T).R 124).length = PhaseCellBand.width p u
      rw [(hframe 124 (by decide) (by decide) (by decide)).2]
      simpa [packedHeaderReg,groupHeaderValue,hq] using hmasters (124,100) (by decide)
    · change ((embStk packedHaloRuntimeReg T).R 141).length = _
      rw [(hframe 141 (by decide) (by decide) (by decide)).2]
      exact ha
    · change ((embStk packedHaloRuntimeReg T).R 142).length = _
      rw [(hframe 142 (by decide) (by decide) (by decide)).2]
      exact hb'
    · change ((embStk packedHaloRuntimeReg T).R 130).length = _
      simpa only [hw] using hword
  · change ((embStk packedHaloRuntimeReg T).R 118).length = _
    rw [(hframe 118 (by decide) (by decide) (by decide)).2]
    simpa [packedHeaderReg,groupHeaderValue] using hmasters (118,101) (by decide)
  · change ((embStk packedHaloRuntimeReg T).R 120).length = _
    rw [(hframe 120 (by decide) (by decide) (by decide)).2]
    simpa [packedHeaderReg,groupHeaderValue] using hmasters (120,109) (by decide)
  · intro i hi93 hi110 hi116
    have hi := i.isLt
    have hh := congrArg (fun G : Stacks 117 A => G.R i) hproj
    simpa [embStk,packedHaloRuntimeReg,packedCellCoreReg,countedReleasedCellBank,releasedCellBank,
      Function.update_apply,Fin.ext_iff,
      show i.val ≠ 93 from fun he => hi93 (Fin.ext he),
      show i.val ≠ 110 from fun he => hi110 (Fin.ext he),
      show i.val ≠ 116 from fun he => hi116 (Fin.ext he),
      show i.val ≠ 143 by omega,show i.val ≠ 238 by omega] using hh
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (embStk packedHaloRuntimeReg T).R 127 = []
      exact hzero
    · change (embStk packedHaloRuntimeReg T).R 129 = []
      rw [(hframe 129 (by decide) (by decide) (by decide)).2]
      exact hfresh 129 (by decide)
    · change (embStk packedHaloRuntimeReg T).R 131 = []
      rw [(hframe 131 (by decide) (by decide) (by decide)).2]
      exact hfresh 131 (by decide)
    · change (embStk packedHaloRuntimeReg T).R 133 = []
      rw [(hframe 133 (by decide) (by decide) (by decide)).2]
      exact hfresh 133 (by decide)
    · change (embStk packedHaloRuntimeReg T).R 134 = []
      rw [(hframe 134 (by decide) (by decide) (by decide)).2]
      exact hfresh 134 (by decide)
    · change (embStk packedHaloRuntimeReg T).R 135 = []
      exact h135
    · change (embStk packedHaloRuntimeReg T).R 136 = []
      rw [(hframe 136 (by decide) (by decide) (by decide)).2]
      exact hfresh 136 (by decide)
    · change (embStk packedHaloRuntimeReg T).R 153 = []
      rw [(hframe 153 (by decide) (by decide) (by decide)).2]
      exact hfresh 153 (by decide)
    · change (embStk packedHaloRuntimeReg T).R 158 = []
      rw [(hframe 158 (by decide) (by decide) (by decide)).2]
      exact h158
    · change (embStk packedHaloRuntimeReg T).R 166 = []
      rw [(hframe 166 (by decide) (by decide) (by decide)).2]
      exact hfresh 166 (by decide)
  · apply hgeometry.of_frame
    · rfl
    · intro k hk
      simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · exact (hhigh 238 (by decide)).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
