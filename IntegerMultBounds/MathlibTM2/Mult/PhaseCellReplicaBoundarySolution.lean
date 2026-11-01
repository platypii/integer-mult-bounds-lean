module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloBoundarySolutionAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedBoundaryFold

/-! Shared boundary factors solve the folded rows of the actual replica archive.
The recovery target explicitly aligns the interior and boundary word formats. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s : ℕ} [NeZero s]

theorem ReplicaHaloProblem.boundary_sizing (H : ReplicaHaloProblem s) (target : ℕ)
    (htarget : H.target = boundaryHaloTarget H.p H.u target H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card) :
    let T := initialSchurTarget H.p H.u (boundaryTableBits H.p target H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card) 2
    H.precision = executionPrecision H.p H.l T 2 ∧
      H.stage = executionStagePrecision H.p H.l T 2 ∧ H.wordWidth = executionWidth H.p H.l T 2 := by
  simpa only [ReplicaHaloProblem.precision,ReplicaHaloProblem.stage,ReplicaHaloProblem.wordWidth,htarget]
    using boundaryHaloTarget_sizing H.p H.u H.l target H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card

noncomputable def replicaBoundarySolution (H : ReplicaHaloProblem s) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (D : ZMod s → GaussianInt) : List GaussianInt :=
  let B := haloBoundary s H.t H.band H.origin (H.origin+H.span)
  let q := H.precision
  let K := factorNewtonSteps H.p q
  let AZ := factorRankIntegerMatrix B W columns
  let rows := (bFoldOrder s B).map (fun i => realPartWord (D i))
  (bandSolveVec q W (naturalLineLc q K W B.card AZ) (naturalLineUc q K W B.card AZ)
    (naturalLineRcs q K W B.card AZ) (rows.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q)

theorem ReplicaCouplingResidualSpec.boundary_solution (H : ReplicaHaloProblem s)
    (A target W : ℕ) (columns : List (ZMod s → GaussianInt))
    (hA : 4 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u) :
    let I := haloInterior s H.t H.band H.origin (H.origin+H.span)
    let B := haloBoundary s H.t H.band H.origin (H.origin+H.span)
    let bits := boundaryTableBits H.p target H.rhsExp B.card
    H.target = boundaryHaloTarget H.p H.u target H.rhsExp B.card →
    columns.length = B.card → ColumnFamilyFormat H.wordWidth columns →
    StageInv (factorRankMatrix A H.precision H.wordWidth B W columns) (Finset.range B.card)
      (1/(8*(H.p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits)) (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) →
    (∀ i ∈ B, ∀ j ∈ B, |bandBoundaryTable B W (computedBoundaryTable A H.precision H.wordWidth B columns) i j-
      (SchurDominance.run (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) I.toList).1 i j| ≤ 1/(2 : ℝ)^bits) →
    ∀ r < H.Fs.length, ∀ D, ReplicaCouplingResidualSpec H r D →
    ∀ x, Solves (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) x
      (fun i => (value H.precision (H.Fs.reverse.getD r (fun _ => 0) i)).re) →
    let solution := replicaBoundarySolution H W columns D
    solution.length = B.card ∧ (∀ z ∈ solution, Fits H.wordWidth z) ∧
      ∀ i < B.card, ‖value H.precision (solution.getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^target ∧
        ‖value H.precision (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent H.p H.rhsExp := by
  dsimp only
  intro htarget hlen hformat hstage htable r hr D hD x hx
  obtain ⟨C,hC,rfl⟩ := hD
  have hsizing := H.boundary_sizing target htarget
  have hq := hsizing.1
  have hw := hsizing.2.2
  have hα : 0 < |H.α| := by
    have hu : (1 : ℝ) ≤ H.u := by exact_mod_cast H.u_pos
    have he := H.alpha_sq
    exact abs_pos.mpr (by intro hz; rw [hz] at he; norm_num at he; linarith)
  have hbase := haloBoundary_solution_accuracy A H.p H.u H.l target H.rhsExp H.origin (H.origin+H.span) W
    columns hA hp H.s_lt_t hα hwidth (by simpa only [sq_abs] using H.alpha_sq)
    H.theta_lower H.gap (by simpa only [sq_abs] using H.budget) (H.dominates hp hwidth)
  dsimp only at hbase
  simp only [ReplicaHaloProblem.band] at hq hw htarget
  rw [← hq,← hw,← htarget] at hbase
  have hsol := hbase hlen hformat hstage htable (H.Fs.reverse.getD r (fun _ => 0)) C (H.x r) x
    (H.rhs_bound r hr) (H.solves r hr) hC.2.2.2 hx
  have hrows := congrArg (List.map realPartWord)
    (guardedCouplingRowField_boundaryFold (2^15*H.p) H.precision H.u H.band H.origin (H.origin+H.span)
      H.s_lt_t H.span_fit C (H.Fs.reverse.getD r (fun _ => 0)))
  simp only [List.map_map,Function.comp_def,ReplicaHaloProblem.band] at hrows
  simpa only [replicaBoundarySolution,ReplicaHaloProblem.band,hrows] using hsol

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
