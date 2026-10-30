module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloPreparedInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBetweenInputs

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloPreparedRecovery

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedPreparedReleaseReady

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloPreparedBoundaryExtended
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecoveryBuffers

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

theorem packedHaloPreparedInput_between_exec (hbody : ∀ f, body' f = embProg packedBoundaryRecoveryBase id (body f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target finalTarget rhsExp a b V boundaryTarget : ℕ} [NeZero s] {α d : ℝ}
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
 :
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
    boundaryTarget = boundaryRecoveryTarget p finalTarget →
    ∀ y : ZMod s → ℝ,
    SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) y
      (fun k => (value q (C k)).re) →
    (∀ j < b-a, ∀ z ∈ couplingCoefficientWords (2^15*p) q s t u band (a+j), Fits w z ∧ z.im = 0) →
    ∃ v' F n, ∃ D : ZMod s → GaussianInt,
      v'.user = v.user ∧ n ≤ packedHaloPreparedInputCost p u l finalTarget rhsExp s t a b V ∧
      Exec body' (packedHaloPreparedInput hR hQ) (mk v (extendStacks (by decide) S)) n (mk v' F) ∧
      F.R 132 = cstream A w (packedInterval a (b-a) D)++outputTail ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => (packedIntervalRead q w a (F.R 132) i).re) y (1/(2 : ℝ)^finalTarget) ∧
      F.R 110 = tail ∧
      PackedHaloBetweenInputs (2^15*p) (executionStagePrecision p l target rhsExp+1)
        q l s t u band a b V w W B.card F ∧
      (∀ bo hf df, PackedBoundaryFactorPages bo hf df S →
        PackedBoundaryFactorPages bo hf df (embStk packedBoundaryRecoveryBase F)) ∧
      (∀ k : Fin 242, 168 ≤ k.val → k ≠ 238 →
        (embStk packedBoundaryRecoveryBase F).R k = S.R k) ∧
      F.L = (extendStacks (by decide : 242 ≤ 248) S).L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k : Fin 168, k ∈ haloAuxiliaryPorts → F.R (packedRecoveryRuntimeReg k) = S.R (packedHaloRuntimeReg k)) ∧ F.R 93 = S.R 93 := by
  dsimp only
  intro columns hcolumns hcell htable hbank hpages hboundary y hy hcoeff
  obtain ⟨v',F,n,D,hu,hn,he,hout,herror,hbank',hsource,h130,h138,h139',h140,hnative',hpages',hprivate',hheaders',h127,h143',h158',h167',hscratch,h125,h128,h157',hsetup',hleft',hinput',houtput',hauxiliary',h93'⟩ :=
    packedHaloPreparedInput_exec (body := body) (body' := body') hbody hR hQ hA hp hα hwidth hst hu hαu hθ hgap
      hbudget hpad C hC hab hb hband hwide hVeq hwV hcoords hunits tail E outputTail
      v S hnative hmasters ha hb' hmeta h157 houtput hE hfresh haLt hfitV h139 h143 hleft
      hsep h158 h167 hrange hdom hq columns hcolumns hcell htable hbank hpages hboundary y hy hcoeff
  refine ⟨v',F,n,D,hu,hn,he,hout,herror,hsource,⟨hbank',hheaders',hnative',?_,h157',hprivate'⟩,hpages',hsetup',hleft',hinput',houtput',hauxiliary',h93'⟩
  intro k hk
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h125
  · exact h127
  · exact h128
  · exact hscratch 129 (by decide)
  · exact h130
  · exact hscratch 131 (by decide)
  · exact hscratch 133 (by decide)
  · exact hscratch 134 (by decide)
  · exact hscratch 135 (by decide)
  · exact hscratch 136 (by decide)
  · exact h138
  · exact h139'
  · exact h140
  · exact h143'
  · exact hscratch 153 (by decide)
  · exact h158'
  · exact hscratch 166 (by decide)
  · exact h167'

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
