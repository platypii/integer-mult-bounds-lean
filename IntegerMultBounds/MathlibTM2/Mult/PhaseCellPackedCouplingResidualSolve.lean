module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolveWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedBoundaryFold

/-! The packed solve consumes the computed coupling RHS with derived size and bounds. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {A Q : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

theorem packedPreparedResidualSolve_coupling_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p u l target rhsExp : ℕ) {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hp : 2 ≤ p)
    (t band a b : ℕ) (C R : ZMod s → GaussianInt) {α d : ℝ}
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
    let b := (bFoldOrder s B).map (couplingRowField (2^15*p) q t u band a b false C R)
    ∀ (v : HS 242 Q A U) (S : Stacks 242 A),
    let T := embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S)
    let σ := boundaryFactorState T
    PackedPreparedBank q w W B.card S →
    σ .vk = cstream A w b →
    PackedBoundaryFactorPages (cstream A w (Lc.map colC).flatten)
      (cstream A w (Uc.map colC).flatten)
      (cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt))) S →
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedResidualSolveCost q w B.card W ∧
      Exec body (packedPreparedResidualSolve hQ) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 143 []) 238
          (cstream A w ((bandSolveVec q W Lc Uc rcs (b.map (normalizeBoundaryWord q (q/2-1)))).map
            (unscaleBoundaryWord q))++S.R 238))}) := by
  dsimp only
  intro hcolumns hcount hR hC v S hbank hvk hpages
  apply packedPreparedResidualSolve_bank_exec (body := body) hQ hA p u l target rhsExp B W columns hp hcolumns
    _ (by simp [bFoldOrder]) ?_ v S hbank hvk hpages
  rw [hBset] at hR hC ⊢
  exact ScalarPlacement.couplingRowField_boundaryFold_bounds (by omega) hst hαu hθ hgap hbudget C R hcount hR hC

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
