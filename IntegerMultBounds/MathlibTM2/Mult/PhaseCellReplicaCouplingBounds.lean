module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaHaloProblem
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedGeometryWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientAccuracy

/-! The replica problem's analytic and sizing data already provide every binary
geometry and generated coefficient-word fit required by coupling. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s : ℕ} [NeZero s]

theorem ReplicaHaloProblem.coupling_geometry (H : ReplicaHaloProblem s) :
    H.origin+(H.span+2*H.band)+s < 2^H.metadataWidth ∧
      8*(H.t+1)^2+4*H.band+8 < 2^H.metadataWidth := by
  have hP : 13 ≤ 2^15*H.p := by have hp := H.p_pos; omega
  have hfit := weightWorkspaceWidth_packed_fits (P := 2^15*H.p) (q := H.precision) (w := H.wordWidth)
    hP (NeZero.pos s) H.s_lt_t H.u_pos H.band_fit (Nat.le_add_right H.origin H.span) H.span_fit
  exact ⟨by simpa only [Nat.add_sub_cancel_left,ReplicaHaloProblem.metadataWidth,ReplicaHaloProblem.band] using hfit.1,hfit.2.1⟩

omit [NeZero s] in
theorem ReplicaHaloProblem.coupling_coefficient_width (H : ReplicaHaloProblem s) :
    H.precision+(8*H.p+1)+2 ≤ H.wordWidth := by
  unfold ReplicaHaloProblem.precision ReplicaHaloProblem.wordWidth executionPrecision executionWidth
    executionExponent inputExponent sourceExponent
  omega

theorem ReplicaHaloProblem.coupling_coefficients (H : ReplicaHaloProblem s) (i : ℕ) :
    ∀ z ∈ couplingCoefficientWords (2^15*H.p) H.precision s H.t H.u H.band i,
      Fits H.wordWidth z ∧ z.im = 0 :=
  couplingCoefficientWords_fits H.p_pos (NeZero.pos s) H.s_lt_t H.alpha_sq H.theta_pos H.gap H.budget H.coupling_coefficient_width

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
