module

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

theorem packedHaloPreparedBoundary_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target rhsExp a b V boundaryTarget : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
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
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p boundaryTarget rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let W := 12*PhaseCellBand.width p u+1
    ∀ columns : List (ZMod s → GaussianInt),
    PreparedBoundaryColumns A p bits q w W B columns →
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
      let output := cstream A w ((bandSolveVec q W Lc Uc rcs
        (rows.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q))
      let F := {T with R := Function.update (Function.update T.R 143 []) 238 (output++T.R 238)}
      v'.user = v.user ∧
      m ≤ packedHaloRealBoundaryDataCost p l s t u target rhsExp a b V+
        preparedResidualSolveCost q w B.card W ∧
      Exec body (.seq (placedPackedHaloRealBoundaryData hR hQ) (packedPreparedResidualSolve hQ))
        (mk v S) m (mk v' F) ∧
      PackedPreparedBank q w W B.card F := by
  dsimp only
  intro columns hcolumns hbank hpages
  obtain ⟨v₁,T,n₁,D,hu₁,hn₁,he₁,hdata,hhigh,hleftFinal,hbankCarry,hpagesCarry⟩ :=
    placedPackedHaloRealBoundaryData_exec (body := body) hR hQ hA (by omega) hst hu hαu hθ hgap
      hbudget hpad C hC hab hb hband hwide hVeq hwV hcoords hunits tail E outputTail v S
      hnative hmasters ha hb' hmeta h157 houtput hE hfresh haLt hfitV h139 h143 hleft
      hsep h158 h167 hrange hdom hq x hx
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
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := packedHaloResidualSolve_exec (body := body) hQ hA
    p u l boundaryTarget rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b)
    (12*PhaseCellBand.width p u+1) columns hp a b target hst hαu hθ hgap hbudget hdom
    hcolumns C D x hC' hx' haccuracy v₁ T (hbankCarry _ _ _ _ hbank) hfold
    (hpagesCarry _ _ _ hpages)
  refine ⟨v₂,T,n₁+n₂,D,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,?_⟩
  exact (hbankCarry _ _ _ _ hbank).publish _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
