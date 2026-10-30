module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloBoundarySolutionAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolveWorkspace

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloResidualAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryResidualErrorBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidualBoundaryFormat
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySchurAdapters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryExactBounds

/-! Accuracy and recovery format for the boundary solution of the actual halo
residual. Exact interior inversion is chosen from dominance, not supplied. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.SchurDominance

theorem preparedBoundary_solution_accuracy (A p u l target rhsExp a b W : ℕ)
    {s t : ℕ} [NeZero s] {α d : ℝ} (columns : List (ZMod s → GaussianInt))
    (hA : 4 ≤ A) (hp : 2 ≤ p) (hst : s < t) (hα : 0 < α) (hwidth : 8*p ≤ 2^u)
    (hαu : α^2 = (u : ℝ)) (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hdom : DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ)))) :
    let band := PhaseCellBand.width p u
    let I := haloInterior s t band a b
    let B := haloBoundary s t band a b
    let cellTarget := boundaryHaloTarget p u target rhsExp B.card
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    let AZ := factorRankIntegerMatrix B W columns
    PreparedBoundaryColumns A p bits q w W B columns →
    (∀ i ∈ B, ∀ j ∈ B, |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
      (run (realMatrix s t p u) (haloVertices s a b) I.toList).1 i j| ≤ 1/(2 : ℝ)^bits) →
    ∀ (C D : ZMod s → GaussianInt) (x₀ x : ZMod s → ℝ),
    (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^rhsExp) →
    Solves (realMatrix s t p u) I x₀ (fun i => (value q (C i)).re) →
    PhaseCellInterface.ErrorOn I (fun i => (value q (D i)).re) x₀ (1/(2 : ℝ)^cellTarget) →
    Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (C i)).re) →
    let rows := (bFoldOrder s B).map (fun i => realPartWord
      (couplingRowField (2^15*p) q t u band a b false D C i))
    let normalized := bandSolveVec q W (naturalLineLc q K W B.card AZ)
      (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ)
      (rows.map (normalizeBoundaryWord q (q/2-1)))
    let solution := normalized.map (unscaleBoundaryWord q)
    solution.length = B.card ∧ (∀ z ∈ solution, Fits w z) ∧
      ∀ i < B.card, ‖value q (solution.getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^target ∧
        ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp := by
  dsimp only
  intro hcolumns htable C D x₀ x hC hx₀ herror hx
  exact haloBoundary_solution_accuracy A p u l target rhsExp a b W columns
    hA hp hst hα hwidth hαu hθ hgap hbudget hdom
    hcolumns.length hcolumns.format hcolumns.stage htable C D x₀ x hC hx₀ herror hx

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
