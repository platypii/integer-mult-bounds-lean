module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundarySolution
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloResidualSolveStock

/-! Execute the existing reusable boundary kernel on an archived replica row.
Factor pages are shared; only the RHS and returned solution are row-specific. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 242 Q A U}

theorem ReplicaCouplingResidualSpec.boundary_solve_exec_within (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (target W : ℕ) (columns : List (ZMod s → GaussianInt))
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) :
    let B := haloBoundary s H.t H.band H.origin (H.origin+H.span)
    let q := H.precision
    let w := H.wordWidth
    let K := factorNewtonSteps H.p q
    let AZ := factorRankIntegerMatrix B W columns
    H.target = boundaryHaloTarget H.p H.u target H.rhsExp B.card →
    PreparedBoundaryColumns A H.p (boundaryTableBits H.p target H.rhsExp B.card) q w W B columns →
    ∀ r < H.Fs.length, ∀ D, ReplicaCouplingResidualSpec H r D →
    ∀ (v : HS 242 Q A U) (S : Stacks 242 A),
    PackedPreparedBank q w W B.card S →
    (boundaryFactorState (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S))) .vk =
      cstream A w ((bFoldOrder s B).map (fun i => realPartWord (D i))) →
    PackedBoundaryFactorPages (cstream A w ((naturalLineLc q K W B.card AZ).map colC).flatten)
      (cstream A w ((naturalLineUc q K W B.card AZ).map colC).flatten)
      (cstream A w ((naturalLineRcs q K W B.card AZ).map fun x => (⟨x,0⟩ : GaussianInt))) S →
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedResidualSolveCost q w B.card W ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        push.workspace q w B.card W) depth (packedPreparedResidualSolve hQ) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 143 []) 238
          (cstream A w (replicaBoundarySolution H W columns D)++S.R 238))}) := by
  dsimp only
  intro htarget hcolumns r hr D hD v S hbank hvk hpages
  obtain ⟨C,hC,rfl⟩ := hD
  have hsizing := H.boundary_sizing target htarget
  have hq := hsizing.1
  have hw := hsizing.2.2
  have he := packedHaloResidualSolve_exec_within (body := body) hQ hA H.p H.u H.l target H.rhsExp
    (haloBoundary s H.t H.band H.origin (H.origin+H.span)) W columns hp H.origin (H.origin+H.span) H.target
    H.s_lt_t H.alpha_sq H.theta_pos H.gap H.budget (H.dominates hp hwidth) push
  dsimp only at he
  rw [← hq,← hw] at he
  have hrows := congrArg (List.map realPartWord)
    (guardedCouplingRowField_boundaryFold (2^15*H.p) H.precision H.u H.band H.origin (H.origin+H.span)
      H.s_lt_t H.span_fit C (H.Fs.reverse.getD r (fun _ => 0)))
  simp only [List.map_map,Function.comp_def] at hrows
  rw [hrows] at hvk
  have hex := he hcolumns (H.Fs.reverse.getD r (fun _ => 0)) C (H.x r) (H.rhs_bound r hr)
    (H.solves r hr) hC.2.2.2 v S hbank hvk hpages
  simp only [ReplicaHaloProblem.band] at hrows
  simpa only [replicaBoundarySolution,ReplicaHaloProblem.band,hrows] using hex

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
