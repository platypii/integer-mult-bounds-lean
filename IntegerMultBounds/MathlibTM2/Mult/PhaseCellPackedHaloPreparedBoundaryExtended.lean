module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloPreparedBoundary
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecoveryUnfold

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U} {body' : P → Pr P 248 Q A U}

theorem packedHaloPreparedBoundary_extended_exec (hbody : ∀ f, body' f = embProg packedBoundaryRecoveryBase id (body f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (v : HS 248 Q A U) (S : Stacks 242 A)
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
      Exec body' (embProg packedBoundaryRecoveryBase id
        (packedHaloPreparedBoundary hR hQ))
        (mk v (extendStacks (by decide) S)) m (mk v' (extendStacks (by decide) F)) ∧
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
      (∀ k : Fin 248, 242 ≤ k.val →
        (extendStacks (by decide) F).L k = [] ∧ (extendStacks (by decide) F).R k = []) := by
  dsimp only
  intro columns hcolumns hcell htable hbank hpages
  obtain ⟨v₁,T,n,D,hu,hn,he,hbankFinal,hdata,hpagesFinal,hleftFinal,hframe,haccuracy⟩ :=
    packedHaloPreparedBoundary_exec (body := body) hR hQ hA hp hα hwidth hst hu hαu hθ hgap
      hbudget hpad C hC hab hb hband hwide hVeq hwV hcoords hunits tail E outputTail
      (embDn packedBoundaryRecoveryBase v) S hnative hmasters ha hb' hmeta h157 houtput hE hfresh
      haLt hfitV h139 h143 hleft hsep h158 h167 hrange hdom hq x hx
      columns hcolumns hcell htable hbank hpages
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_extendStacks (by decide : 242 ≤ 248) hbody he v rfl
  exact ⟨v₂,T,n,D,hu₂.trans hu,hn,he₂,hbankFinal,hdata,hpagesFinal,hleftFinal,hframe,haccuracy,
    fun k hk => extendStacks_fresh (by decide) _ k hk⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
