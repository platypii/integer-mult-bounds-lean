module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloNextInputExec

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloPreparedInputBetween
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloNextInput

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

theorem packedHaloTwoInputs_exec (hbody : ∀ f, body' f = embProg packedBoundaryRecoveryBase id (body f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target finalTarget rhsExp a b V boundaryTarget : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hα : 0 < α) (hwidth : 8*p ≤ 2^u) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C C₂ : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (hC₂ : ∀ k, ‖value (executionPrecision p l target rhsExp) (C₂ k)‖ ≤ (2 : ℝ)^rhsExp)
    (hab : a ≤ b) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (hwide : 8*(t+1)^2+4*PhaseCellBand.width p u+8 < 2^V)
    (hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (2*executionPrecision p l target rhsExp+8) t u)
    (hwV : executionWidth p l target rhsExp < 2^V)
    (hcoords : b < 2^V) (hunits : b*executionWidth p l target rhsExp < 2^V)
    (tail : List (Fin (A+4)))
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (hsource : S.R 110 = cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++
      (cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C₂)++tail))

    (haLt : a < s) (hfitV : a+((b-a)+2*PhaseCellBand.width p u)+s < 2^V)

    (hsep : b-a+PhaseCellBand.width p u ≤ s)

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
    PackedHaloBetweenInputs (2^15*p) (executionStagePrecision p l target rhsExp+1)
      q l s t u band a b V w W B.card S →
    ∀ columns : List (ZMod s → GaussianInt),
    PreparedBoundaryColumns A p bits q w W B columns →
    target = boundaryHaloTarget p u boundaryTarget rhsExp B.card →
    (∀ i ∈ B, ∀ j ∈ B, |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
      (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
        (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^bits) →
    let AZ := factorRankIntegerMatrix B W columns
    let K := factorNewtonSteps p q
    let Lc := naturalLineLc q K W B.card AZ
    let Uc := naturalLineUc q K W B.card AZ
    let rcs := naturalLineRcs q K W B.card AZ
    PackedBoundaryFactorPages (cstream A w (Lc.map colC).flatten)
      (cstream A w (Uc.map colC).flatten)
      (cstream A w (rcs.map fun z => (⟨z,0⟩ : GaussianInt))) (embStk packedBoundaryRecoveryBase S) →
    boundaryTarget = boundaryRecoveryTarget p finalTarget →
    ∀ y y₂ : ZMod s → ℝ,
    SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) y
      (fun k => (value q (C k)).re) →
    SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) y₂
      (fun k => (value q (C₂ k)).re) →
    (∀ j < b-a, ∀ z ∈ couplingCoefficientWords (2^15*p) q s t u band (a+j), Fits w z ∧ z.im = 0) →
    ∃ v' F n, ∃ D₁ D₂ : ZMod s → GaussianInt,
      v'.user = v.user ∧
      n ≤ 2*(packedFreshOutputCost V (b-a) w+packedHaloPreparedInputCost p u l finalTarget rhsExp s t a b V) ∧
      Exec body' (.seq (.seq packedFreshOutput (packedHaloPreparedInput hR hQ))
        (.seq packedFreshOutput (packedHaloPreparedInput hR hQ))) (mk v S) n (mk v' F) ∧
      F.R 132 = cstream A w (packedInterval a (b-a) D₂)++
        (cstream A w (packedInterval a (b-a) D₁)++S.R 132) ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => (packedIntervalRead q w a (cstream A w (packedInterval a (b-a) D₁)++S.R 132) i).re)
        y (1/(2 : ℝ)^finalTarget) ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => (packedIntervalRead q w a (F.R 132) i).re) y₂ (1/(2 : ℝ)^finalTarget) ∧
      F.R 110 = tail ∧
      PackedHaloBetweenInputs (2^15*p) (executionStagePrecision p l target rhsExp+1)
        q l s t u band a b V w W B.card F := by
  dsimp only
  intro hbetween columns hcolumns hcell htable hpages hboundary y y₂ hy hy₂ hcoeff
  obtain ⟨v₁,F₁,n₁,D₁,hu₁,hn₁,he₁,hout₁,herror₁,hsource₁,hbetween₁,hpages₁⟩ :=
    packedHaloNextInput_exec (body := body) (body' := body') hbody hR hQ hA hp hα hwidth hst hu hαu hθ hgap
      hbudget hpad C hC hab hb hband hwide hVeq hwV hcoords hunits
      (cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C₂)++tail)
      v S hsource haLt hfitV hsep hdom hq hbetween columns hcolumns hcell htable hpages hboundary y hy hcoeff
  obtain ⟨v₂,F₂,n₂,D₂,hu₂,hn₂,he₂,hout₂,herror₂,hsource₂,hbetween₂,hpages₂⟩ :=
    packedHaloNextInput_exec (body := body) (body' := body') hbody hR hQ hA hp hα hwidth hst hu hαu hθ hgap
      hbudget hpad C₂ hC₂ hab hb hband hwide hVeq hwV hcoords hunits tail
      v₁ F₁ hsource₁ haLt hfitV hsep hdom hq hbetween₁ columns hcolumns hcell htable
      (hpages₁ _ _ _ hpages) hboundary y₂ hy₂ hcoeff
  refine ⟨v₂,F₂,n₁+n₂,D₁,D₂,hu₂.trans hu₁,by omega,Exec.seq he₁ he₂,?_,?_,herror₂,hsource₂,hbetween₂⟩
  · rw [hout₂,hout₁]
  · simpa only [hout₁] using herror₁

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
