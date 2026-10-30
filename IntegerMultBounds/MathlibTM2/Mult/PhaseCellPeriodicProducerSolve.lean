module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicPackedResidualSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicResidualBoundary242
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingExecutionWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicPreparedBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedBoundaryFold

/-! The packed solve consumes the computed coupling RHS with derived size and bounds. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {A Q : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

open ScalarPlacement IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Node

structure PeriodicProducerInput {A s : ℕ} [NeZero s] (p q w t u band a b V : ℕ)
    (C R : ZMod s → GaussianInt) (pageTail rhsTail raw : List (Fin (A+4))) (S : Stacks 168 A) : Prop where
  hready : RetainedCouplingReady (2^15*p) q w s t u band a b raw (embStk groupReg (embStk intervalPageReg S))
  hsource : S.R 141 = cstream A w (chirpLine s C)
  hclean : ∀ k ∈ ([107,160] : List (Fin 168)), S.R k = []
  hrows : (S.R 140).length = 2*band+1
  hpage : S.R 138 = cstream A w (couplingCoefficientPageInterval (2^15*p) q s t u band a b 0 s)++pageTail
  hrhs : S.R 93 = cstream A w (packedInterval 0 s R)++rhsTail
  h143 : S.R 143 = []
  h166 : S.R 166 = []
  h139 : (S.R 139).length = (couplingCoefficientPageInterval (2^15*p) q s t u band a b 0 s).length
  haS : a ≤ s
  hbS : b ≤ s
  hbandS : band ≤ s
  hwide : 8*(t+1)^2+4*band+8 < 2^V
  hfitV : 0+(s+2*band)+s < 2^V
  hV : (S.R 163).length = V
  hbase : ∀ k ∈ [(145 : Fin 168),146,147,149,151,155,165],
      S.R k = binSyms V (couplingIntervalValue s t band a b 0 s k)
  hderived : ∀ k ∈ [(148 : Fin 168),154,156,164], S.R k = []
  h158 : S.R 158 = []
  h135 : S.R 135 = []
  h167 : S.R 167 = []
  hwidth : (S.R 130).length = w

noncomputable def periodicProducerCost (p q w s t u band a b V : ℕ) [NeZero s] : ℕ :=
  (2*((s+2*band)*w)+2)+((padCouplingSourceCost s band w+4*((s+2*band)*w)+4)+(36*V+36+(((8*s+8*band+11*V+12+(152*V+153+((32*(s+2*band)+2)*tblC V 1+68*V+2*(s+2*band)+72)+maskCouplingSourceCost (s+2*band) w)) +
        (12*((s+2*band)*w)+17*s+26*band+11*V+24) +
        (144*V+145+((46*s+2)*tblC V 1+66*V+2*s+70)+(6*s+11*V+6+(retainedPageSpatialIntervalLoopCost false q w s t band a b 0 s+
        (22*s+22*V+22+transferCountedLineCost s w+
          transferCountedLineCost (couplingCoefficientPageInterval (2^15*p) q s t u band a b 0 s).length w))))) + (28*s*w+36*s+11*V+26))))+packedBoundaryDataCost V s (haloBoundary s t band a b).card w

theorem periodicProducerSolve_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p u l target : ℕ) {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hp : 2 ≤ p)
    (V t band a b : ℕ) (C R : ZMod s → GaussianInt) {α d : ℝ}
    (hBset : B = haloBoundary s t band a b) (hst : s < t) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p) :
    let bits := boundaryTableBits p target 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    let AZ := factorRankIntegerMatrix B W columns
    let Lc := naturalLineLc q K W B.card AZ
    let Uc := naturalLineUc q K W B.card AZ
    let rcs := naturalLineRcs q K W B.card AZ
    PreparedBoundaryColumns A p bits q w W B columns →
    2*band+1 ≤ 2^couplingCountExponent p u →
    (∀ j, ‖value q (R j)‖ ≤ (2 : ℝ)^2) →
    (∀ j ∈ haloInterior s t band a b, ‖value q (C j)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2) →
    let rhs := (bFoldOrder s B).map (couplingRowField (2^15*p) q t u band a b false C R)
    ∀ (v : HS 242 Q A U) (S : Stacks 242 A),
    ∀ rhsTail pageTail raw : List (Fin (A+4)),
    let e : Fin 168 → Fin 242 := Fin.castLE (by decide)
    let F := embOvr e (ScalarPlacement.periodicBoundaryResult (embStk e S) V s t band a b w
      (ScalarPlacement.guardedCouplingRowField (2^15*p) q t u band a b false C R)
      (couplingRowField (2^15*p) q t u band a b false C R) rhsTail).get S
    let G := {F with R := (Function.update (Function.update F.R 143 []) 238
          (cstream A w ((bandSolveVec q W Lc Uc rcs (rhs.map (normalizeBoundaryWord q (q/2-1)))).map
            (unscaleBoundaryWord q))++F.R 238))}
    PeriodicProducerInput p q w t u band a b V C R pageTail rhsTail raw (embStk e S) →
    PackedPreparedBank q w W B.card S →
    PackedBoundaryFactorPages (cstream A w (Lc.map colC).flatten)
      (cstream A w (Uc.map colC).flatten)
      (cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt))) S →
    ∃ v' n, v'.user = v.user ∧ n ≤ periodicProducerCost p q w s t u band a b V+preparedResidualSolveCost q w B.card W ∧
      Exec body (.seq (embProg e Empty.elim (.seq (.seq (.seq ScalarPlacement.prepareFullLineRibbon
        (ScalarPlacement.completedGatheredFeedCouplingInterval hQ false)) (uclear 160)) packedBoundaryData))
        (packedPreparedResidualSolve hQ)) (mk v S) n
        (mk v' G) ∧ PackedPreparedBank q w W B.card G ∧
      PackedBoundaryFactorPages (cstream A w (Lc.map colC).flatten)
        (cstream A w (Uc.map colC).flatten)
        (cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt))) G := by
  dsimp only
  intro hcolumns hcount hR hC v S rhsTail pageTail raw hin hbank hpages
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := periodicResidualAndBoundaryData242_exec (body := body) hQ hA
    (by dsimp [executionWidth]; omega) (by dsimp [executionWidth,executionPrecision]; omega)
    hst C R pageTail rhsTail raw v _ S rfl hin.hready hin.hsource hin.hclean hin.hrows hin.hpage hin.hrhs hin.h143
    (execution_couplingInput_width ..) hC (by omega) hαu hθ hgap hbudget (execution_couplingCoefficient_width ..)
    V hin.h166 hin.h139 hin.haS hin.hbS hin.hbandS hin.hwide hin.hfitV hin.hV hin.hbase hin.hderived
    hin.h158 hin.h135 hin.h167 hin.hwidth
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := periodicPackedResidualSolve_exec (body := body) hQ hA p u l target 2 B W
    columns hp V t band a b C R hBset hst hαu hθ hgap hbudget hcolumns hcount hR hC v₁ S rhsTail hbank hpages
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,?_,?_⟩
  · exact (periodicBoundaryResult_preparedBank S V t band a b _ _ rhsTail hbank).publish _
  · exact (periodicBoundaryResult_factorPages S V t band a b _ _ _ rhsTail _ _ _ hpages).publish _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
