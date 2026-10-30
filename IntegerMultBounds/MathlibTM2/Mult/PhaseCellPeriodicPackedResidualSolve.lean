module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCouplingResidualSolve
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

theorem periodicPackedResidualSolve_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p u l target rhsExp : ℕ) {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hp : 2 ≤ p)
    (V t band a b : ℕ) (C R : ZMod s → GaussianInt) {α d : ℝ}
    (hBset : B = haloBoundary s t band a b) (hst : s < t) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p) :
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    let AZ := factorRankIntegerMatrix B W columns
    let Lc := naturalLineLc q K W B.card AZ
    let Uc := naturalLineUc q K W B.card AZ
    let rcs := naturalLineRcs q K W B.card AZ
    PreparedBoundaryColumns A p bits q w W B columns →
    2*band+1 ≤ 2^couplingCountExponent p u →
    (∀ j, ‖value q (R j)‖ ≤ (2 : ℝ)^rhsExp) →
    (∀ j ∈ haloInterior s t band a b, ‖value q (C j)‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp) →
    let rhs := (bFoldOrder s B).map (couplingRowField (2^15*p) q t u band a b false C R)
    ∀ (v : HS 242 Q A U) (S : Stacks 242 A),
    ∀ rhsTail : List (Fin (A+4)),
    let e : Fin 168 → Fin 242 := Fin.castLE (by decide)
    let F := embOvr e (ScalarPlacement.periodicBoundaryResult (embStk e S) V s t band a b w
      (ScalarPlacement.guardedCouplingRowField (2^15*p) q t u band a b false C R)
      (couplingRowField (2^15*p) q t u band a b false C R) rhsTail).get S
    PackedPreparedBank q w W B.card S →
    PackedBoundaryFactorPages (cstream A w (Lc.map colC).flatten)
      (cstream A w (Uc.map colC).flatten)
      (cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt))) S →
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedResidualSolveCost q w B.card W ∧
      Exec body (packedPreparedResidualSolve hQ) (mk v F) n
        (mk v' {F with R := (Function.update (Function.update F.R 143 []) 238
          (cstream A w ((bandSolveVec q W Lc Uc rcs (rhs.map (normalizeBoundaryWord q (q/2-1)))).map
            (unscaleBoundaryWord q))++F.R 238))}) := by
  dsimp only
  intro hcolumns hcount hR hC v S rhsTail hbank hpages
  apply packedPreparedResidualSolve_coupling_exec (body := body) hQ hA p u l target rhsExp B W columns hp
    t band a b C R hBset hst hαu hθ hgap hbudget hcolumns hcount hR hC v _
    (ScalarPlacement.periodicBoundaryResult_preparedBank S V t band a b _ _ rhsTail hbank) ?_
    (ScalarPlacement.periodicBoundaryResult_factorPages S V t band a b _ _ _ rhsTail _ _ _ hpages)
  rw [hBset]
  exact ScalarPlacement.periodicBoundaryResult_solverRhs S V t band a b _ _ _ rhsTail

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
