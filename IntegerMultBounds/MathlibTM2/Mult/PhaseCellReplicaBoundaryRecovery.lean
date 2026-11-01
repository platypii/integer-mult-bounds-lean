module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundarySolution

/-! Apply actual local recovery to the boundary solution of an archived replica.
The problem and shared column certificate discharge numerical prerequisites. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 248 Q A U}

theorem ReplicaCouplingResidualSpec.recovery_exec (H : ReplicaHaloProblem s)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hsep : H.span+H.band ≤ s)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (target W : ℕ) (columns : List (ZMod s → GaussianInt)) :
    let I := haloInterior s H.t H.band H.origin (H.origin+H.span)
    let B := haloBoundary s H.t H.band H.origin (H.origin+H.span)
    let bits := boundaryTableBits H.p (boundaryRecoveryTarget H.p target) H.rhsExp B.card
    H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp B.card →
    PreparedBoundaryColumns A H.p bits H.precision H.wordWidth W B columns →
    (∀ i ∈ B, ∀ j ∈ B, |bandBoundaryTable B W (computedBoundaryTable A H.precision H.wordWidth B columns) i j-
      (SchurDominance.run (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) I.toList).1 i j| ≤ 1/(2 : ℝ)^bits) →
    ∀ r < H.Fs.length, ∀ D, ReplicaCouplingResidualSpec H r D →
    ∀ x, Solves (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) x
      (fun i => (value H.precision (H.Fs.reverse.getD r (fun _ => 0) i)).re) →
    ∀ (solutionTail words outputTail residual rhsTail : List (Fin (A+4))),
    words.length = H.span*H.wordWidth → residual.length = H.span*H.wordWidth →
    ∀ (v : HS 248 Q A U) (S : Stacks 248 A), ReplicaRecoveryReady H W S →
    S.R 238 = cstream A H.wordWidth (replicaBoundarySolution H W columns D)++solutionTail →
    S.R 132 = words++outputTail →
    S.R 110 = residual++(cstream A H.wordWidth (packedInterval H.origin H.span (H.Fs.reverse.getD r (fun _ => 0)))++rhsTail) →
    ∃ v' F n, ∃ E : ZMod s → GaussianInt, v'.user = v.user ∧
      n ≤ packedBoundaryRecoveryCost H.p H.u H.l target H.rhsExp s H.t H.origin (H.origin+H.span) H.metadataWidth H.precision H.wordWidth ∧
      Exec body (packedBoundaryRecovery hR hQ) (mk v S) n (mk v' F) ∧
      F.R 93 = S.R 93 ∧ F.R 139 = S.R 139 ∧ F.R 238 = solutionTail ∧ F.inp = S.inp ∧ F.out = S.out ∧
      F.R 132 = cstream A H.wordWidth (packedInterval H.origin H.span E)++outputTail ∧ (∀ i, Fits H.wordWidth (E i)) ∧
      PhaseCellInterface.ErrorOn (haloVertices s H.origin (H.origin+H.span)) (fun i => (packedIntervalRead H.precision H.wordWidth H.origin (F.R 132) i).re) x (1/(2 : ℝ)^target) ∧
      (∃ residual : List (Fin (A+4)), residual.length = H.span*H.wordWidth ∧
        F.R 110 = residual++(cstream A H.wordWidth (packedInterval H.origin H.span (H.Fs.reverse.getD r (fun _ => 0)))++rhsTail)) ∧
      (∀ i : Fin 117, i ≠ 93 → i ≠ 110 → F.R ⟨i.val,by omega⟩ = []) ∧
      F.L = S.L ∧ (∀ k ∈ packedRecoveryRetainedPorts, F.R k = S.R k) ∧
      PackedBoundarySolveWorkspace H.precision (embStk packedBoundaryRecoveryBase F) ∧
      BoundarySolveReady (boundaryFactorState (embStk preparedBoundaryCoreReg
        (embStk packedBoundaryFactorReg (embStk packedBoundaryRecoveryBase F)))) H.precision H.wordWidth W
        (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card ∧
      (∀ k : Fin 248, 242 ≤ k.val → F.L k = [] ∧ F.R k = []) ∧
      (∀ k : Fin 248, 168 ≤ k.val → k.val < 242 → k ≠ 238 → F.R k = S.R k) ∧
      (∀ bo hf df, PackedBoundaryFactorPages bo hf df (embStk packedBoundaryRecoveryBase S) →
        PackedBoundaryFactorPages bo hf df (embStk packedBoundaryRecoveryBase F)) ∧
      F.R 127 = [] ∧ F.R 143 = [] ∧ F.R 158 = [] ∧ F.R 167 = [] ∧
      (∀ k ∈ ([129,131,133,134,135,136,153,166] : List (Fin 248)), F.R k = []) ∧ F.R 126 = S.R 126 := by
  dsimp only
  intro htarget hcolumns htable r hr D hD x hx solutionTail words outputTail residual rhsTail
    hwords hresidual v S h hsrc houtput hrhsSource
  have hsol := ReplicaCouplingResidualSpec.boundary_solution H A (boundaryRecoveryTarget H.p target) W columns
    (by omega : 4 ≤ A) hp hwidth htarget hcolumns.length hcolumns.format hcolumns.stage htable r hr D hD x hx
  have hsizing := H.boundary_sizing (boundaryRecoveryTarget H.p target) htarget
  have hα : 0 < |H.α| := by
    have hu : (1 : ℝ) ≤ H.u := by exact_mod_cast H.u_pos
    have he := H.alpha_sq
    exact abs_pos.mpr (by intro hz; rw [hz] at he; norm_num at he; linarith)
  have hword : H.wordWidth = 2*H.precision+8 := by
    unfold ReplicaHaloProblem.wordWidth ReplicaHaloProblem.precision executionWidth executionPrecision
    omega
  have hVeq : H.metadataWidth = weightWorkspaceWidth (2^15*H.p) H.precision (2*H.precision+8) H.t H.u := by
    unfold ReplicaHaloProblem.metadataWidth
    rw [hword]
  have hfits := weightWorkspaceWidth_packed_fits (P := 2^15*H.p) (q := H.precision) (w := H.wordWidth)
    (by have hh := H.p_pos; omega) (NeZero.pos s) H.s_lt_t H.u_pos H.band_fit
    (Nat.le_add_right H.origin H.span) H.span_fit
  have hN : S.R 165 = binSyms H.metadataWidth H.span := by
    simpa [embStk,packedRecoveryRuntimeReg,couplingIntervalValue] using h.geometry.encoded 165 (by decide)
  have he := packedBoundaryRecovery_spec (body := body) (p := H.p) (u := H.u) (l := H.l)
    (target := target) (rhsExp := H.rhsExp) (s := s) (t := H.t) (a := H.origin) (b := H.origin+H.span)
    (V := H.metadataWidth) (q := H.precision) (w := H.wordWidth) (W := W)
    hR hQ hA hp H.u_pos hwidth hα H.s_lt_t (by simpa only [sq_abs] using H.alpha_sq) H.theta_lower H.gap
    (by simpa only [sq_abs] using H.budget) (H.dominates hp hwidth)
    (Nat.le_add_right H.origin H.span) H.span_fit H.band_fit
    (by simpa only [Nat.add_sub_cancel_left,ReplicaHaloProblem.band] using hsep) hpad hsizing.1 hsizing.2.2
    (H.Fs.reverse.getD r (fun _ => 0)) (replicaBoundarySolution H W columns D) x (H.rhs_bound r hr)
    hsol.1 hsol.2.1 hsol.2.2 hx solutionTail words outputTail residual rhsTail
    (by simpa only [Nat.add_sub_cancel_left,ReplicaHaloProblem.band] using hwords) (by simpa only [Nat.add_sub_cancel_left,ReplicaHaloProblem.band] using hresidual)
    v S h.bank.workspace h.bank.ready h.rhs h.count hsrc
    (by simpa only [Nat.add_sub_cancel_left,ReplicaHaloProblem.band] using hN) (by simpa only [Nat.add_sub_cancel_left,ReplicaHaloProblem.band] using h.mask)
    houtput (by simpa only [Nat.add_sub_cancel_left,ReplicaHaloProblem.band] using hrhsSource) h.freshLeft h.freshRight h.masters
    (by simpa only [hsizing.2.1,ReplicaHaloProblem.band] using h.stage) h.level h.native h.clean h.rows
    (by simpa only [Nat.add_sub_cancel_left,ReplicaHaloProblem.band] using h.page) (by simpa only [Nat.add_sub_cancel_left,ReplicaHaloProblem.band] using h.pageCount)
    (by intro j hj; exact H.coupling_coefficients (H.origin+j)) H.coupling_geometry.2
    (by simpa only [Nat.add_sub_cancel_left,ReplicaHaloProblem.band] using H.coupling_geometry.1) hVeq
    hfits.2.2.1 hfits.2.2.2.1 hfits.2.2.2.2 (by simpa only [Nat.add_sub_cancel_left,ReplicaHaloProblem.band] using h.geometry)
  simpa only [Nat.add_sub_cancel_left,ReplicaHaloProblem.band] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
