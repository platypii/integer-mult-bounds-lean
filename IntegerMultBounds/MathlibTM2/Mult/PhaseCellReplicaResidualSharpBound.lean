module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingResidualBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupportBudget

/-! Retain the actual stencil-count exponent when feeding the Schur solver.
The coarser archive-width reserve is not an extra RHS magnitude assumption. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s : ℕ} [NeZero s]

theorem ReplicaCouplingResidualSpec.sharp_norm (H : ReplicaHaloProblem s)
    (r : ℕ) (hr : r < H.Fs.length) (D : ZMod s → GaussianInt)
    (h : ReplicaCouplingResidualSpec H r D) :
    ∀ i, ‖value H.precision (D i)‖ ≤
      (2 : ℝ)^couplingRowExponent H.rhsExp (stableInteriorExponent H.p H.rhsExp)
        (8*H.p+1) (couplingCountExponent H.p H.u) := by
  obtain ⟨C,hC,rfl⟩ := h
  exact guardedCouplingRowField_norm false H.p_pos H.s_lt_t H.alpha_sq H.theta_pos H.gap H.budget
    C (H.Fs.reverse.getD r (fun _ => 0)) (couplingCountExponent_spec H.p H.u)
    (H.rhs_bound r hr) (by simpa [ReplicaHaloProblem.precision] using hC.2.2.1)

theorem replicaCouplingResiduals_sharp_norm (H : ReplicaHaloProblem s)
    (Ds : List (ZMod s → GaussianInt)) (hlen : Ds.length = H.Fs.length)
    (hgood : ∀ j : Fin Ds.length,
      ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) (Ds[j.val]'j.isLt)) :
    ∀ D ∈ Ds, ∀ i, ‖value H.precision (D i)‖ ≤
      (2 : ℝ)^couplingRowExponent H.rhsExp (stableInteriorExponent H.p H.rhsExp)
        (8*H.p+1) (couplingCountExponent H.p H.u) := by
  intro D hD
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hD
  exact ReplicaCouplingResidualSpec.sharp_norm H (H.Fs.length-1-j)
    (by omega) _ (hgood ⟨j,hj⟩)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
