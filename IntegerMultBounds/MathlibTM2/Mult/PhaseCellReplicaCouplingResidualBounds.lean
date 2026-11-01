module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedCouplingRowValue

/-! Uniform magnitude and word-fit bounds for the actual archived residuals.
The existing precision reserve pays for a simple dyadic stencil-count bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s : ℕ} [NeZero s]

def replicaResidualExponent (H : ReplicaHaloProblem s) := H.rhsExp+32*H.p+6

omit [NeZero s] in
theorem ReplicaHaloProblem.coupling_count (H : ReplicaHaloProblem s) :
    2*H.band+1 ≤ 2^(16*H.p+3) := by
  have hsqrt := Nat.sqrt_le' (16*H.p/H.u)
  have hdiv := Nat.div_le_self (16*H.p) H.u
  have hbound : Nat.sqrt (16*H.p/H.u) ≤ 8*H.p := by
    by_contra hn
    have hle : 8*H.p+1 ≤ Nat.sqrt (16*H.p/H.u) := by omega
    have hsq := Nat.pow_le_pow_left hle 2
    nlinarith
  apply (show 2*H.band+1 ≤ 16*H.p+3 by unfold ReplicaHaloProblem.band NLogN.PhaseCellBand.width; omega).trans
  exact (Nat.lt_two_pow_self (n := 16*H.p+3)).le

omit [NeZero s] in
theorem ReplicaHaloProblem.coupling_residual_exponent (H : ReplicaHaloProblem s) :
    couplingRowExponent H.rhsExp (stableInteriorExponent H.p H.rhsExp) (8*H.p+1) (16*H.p+3) = replicaResidualExponent H := by
  unfold couplingRowExponent stableInteriorExponent replicaResidualExponent
  omega

omit [NeZero s] in
theorem ReplicaHaloProblem.coupling_residual_width (H : ReplicaHaloProblem s) :
    H.precision+replicaResidualExponent H+2 ≤ H.wordWidth := by
  unfold ReplicaHaloProblem.precision ReplicaHaloProblem.wordWidth executionPrecision executionWidth
    executionExponent inputExponent sourceExponent replicaResidualExponent
  omega

theorem ReplicaCouplingResidualSpec.bounds (H : ReplicaHaloProblem s) (r : ℕ) (hr : r < H.Fs.length)
    (D : ZMod s → GaussianInt) (h : ReplicaCouplingResidualSpec H r D) :
    (∀ i, ‖value H.precision (D i)‖ ≤ (2 : ℝ)^replicaResidualExponent H) ∧
      (∀ i, Fits H.wordWidth (D i)) := by
  obtain ⟨C,hC,rfl⟩ := h
  have hnorm := guardedCouplingRowField_norm (q := H.precision) false H.p_pos H.s_lt_t H.alpha_sq H.theta_pos H.gap H.budget
    C (H.Fs.reverse.getD r (fun _ => 0)) H.coupling_count (H.rhs_bound r hr)
    (by simpa [ReplicaHaloProblem.precision] using hC.2.2.1)
  have hnorm' : ∀ i, ‖value H.precision (guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band
      H.origin (H.origin+H.span) false C (H.Fs.reverse.getD r (fun _ => 0)) i)‖ ≤ (2 : ℝ)^replicaResidualExponent H := by
    simpa only [H.coupling_residual_exponent,ReplicaHaloProblem.precision] using hnorm
  exact ⟨hnorm',fun i => fits_of_value_power H.coupling_residual_width _ (hnorm' i)⟩

theorem replicaCouplingResiduals_bounds (H : ReplicaHaloProblem s) (Ds : List (ZMod s → GaussianInt))
    (hlen : Ds.length = H.Fs.length)
    (hgood : ∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) (Ds[j.val]'j.isLt)) :
    ∀ D ∈ Ds, (∀ i, ‖value H.precision (D i)‖ ≤ (2 : ℝ)^replicaResidualExponent H) ∧
      (∀ i, Fits H.wordWidth (D i)) := by
  intro D hD
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hD
  exact ReplicaCouplingResidualSpec.bounds H (H.Fs.length-1-j) (by omega) _ (hgood ⟨j,hj⟩)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
