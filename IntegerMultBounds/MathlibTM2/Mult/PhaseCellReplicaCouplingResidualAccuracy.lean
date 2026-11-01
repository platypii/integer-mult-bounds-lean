module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingResidualBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloResidualAccuracy

/-! The actual archived guarded rows approximate the exact Schur residual on
its boundary. The numerical estimate is independent of the replica schedule. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s : ℕ} [NeZero s]

theorem ReplicaCouplingResidualSpec.error (H : ReplicaHaloProblem s) (hp : 2 ≤ H.p)
    (hwidth : 8*H.p ≤ 2^H.u) (r : ℕ) (hr : r < H.Fs.length)
    (D : ZMod s → GaussianInt) (h : ReplicaCouplingResidualSpec H r D)
    (R : (ZMod s → ℝ) → ZMod s → ℝ)
    (hR : ∀ c, Solves (realMatrix s H.t H.p H.u)
      (haloInterior s H.t H.band H.origin (H.origin+H.span)) (R c) c) :
    ∀ i ∈ haloBoundary s H.t H.band H.origin (H.origin+H.span),
      ‖value H.precision (realPartWord (D i))-
        (residual (realMatrix s H.t H.p H.u)
          (haloInterior s H.t H.band H.origin (H.origin+H.span)) R
          (fun k => (value H.precision (H.Fs.reverse.getD r (fun _ => 0) k)).re) i : ℂ)‖ ≤
        haloResidualError H.p H.u H.precision H.rhsExp H.target := by
  obtain ⟨C,hC,rfl⟩ := h
  have hα : 0 < |H.α| := by
    have hu : (1 : ℝ) ≤ H.u := by exact_mod_cast H.u_pos
    have he := H.alpha_sq
    exact abs_pos.mpr (by intro hz; rw [hz] at he; norm_num at he; linarith)
  have hαu : |H.α|^2 = (H.u : ℝ) := by simpa only [sq_abs] using H.alpha_sq
  have hbudget : |H.α|^2*H.d ≤ H.p := by simpa only [sq_abs] using H.budget
  have hw := stableInteriorResidual_width H.p H.u H.l H.target H.rhsExp
  have he := haloResidual_error_bound (q := H.precision) (w := H.wordWidth)
    hp H.s_lt_t hα hwidth hαu H.theta_lower H.gap hbudget hw (H.dominates hp hwidth)
    (H.Fs.reverse.getD r (fun _ => 0)) C (H.rhs_bound r hr) (H.x r) (H.solves r hr) hC.2.2.2 R hR
  intro i hi
  rw [guardedCouplingRowField_eq H.s_lt_t _ _ _ _ _ _ false H.span_fit C _ i (Or.inr hi)]
  exact he i

/-- One exact interior inverse serves every row of the physical residual archive. -/
def ReplicaCouplingResidualsAccurate (H : ReplicaHaloProblem s)
    (Ds : List (ZMod s → GaussianInt)) : Prop :=
  ∃ R : (ZMod s → ℝ) → ZMod s → ℝ,
    (∀ c, Solves (realMatrix s H.t H.p H.u)
      (haloInterior s H.t H.band H.origin (H.origin+H.span)) (R c) c) ∧
    ∀ j : Fin Ds.length, ∀ i ∈ haloBoundary s H.t H.band H.origin (H.origin+H.span),
      ‖value H.precision (realPartWord ((Ds[j.val]'j.isLt) i))-
        (residual (realMatrix s H.t H.p H.u)
          (haloInterior s H.t H.band H.origin (H.origin+H.span)) R
          (fun k => (value H.precision (H.Fs.reverse.getD (H.Fs.length-1-j.val) (fun _ => 0) k)).re) i : ℂ)‖ ≤
        haloResidualError H.p H.u H.precision H.rhsExp H.target

theorem replicaCouplingResiduals_accurate (H : ReplicaHaloProblem s)
    (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u) (Ds : List (ZMod s → GaussianInt))
    (hlen : Ds.length = H.Fs.length)
    (hgood : ∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) (Ds[j.val]'j.isLt)) :
    ReplicaCouplingResidualsAccurate H Ds := by
  classical
  let I := haloInterior s H.t H.band H.origin (H.origin+H.span)
  have hμ : (0 : ℝ) < 1/(8*(H.p : ℝ)) := by
    have hpR : (0 : ℝ) < H.p := by exact_mod_cast H.p_pos
    positivity
  have hdom := dominates_mono (realMatrix s H.t H.p H.u) Finset.univ I _
    (Finset.subset_univ I) (H.dominates hp hwidth)
  let R := fun c => Classical.choose (solves_exists (realMatrix s H.t H.p H.u) I _ hμ hdom c)
  have hR c : Solves (realMatrix s H.t H.p H.u) I (R c) c :=
    Classical.choose_spec (solves_exists (realMatrix s H.t H.p H.u) I _ hμ hdom c)
  refine ⟨R,hR,?_⟩
  intro j
  exact ReplicaCouplingResidualSpec.error H hp hwidth _ (by have hj := j.isLt; omega) _ (hgood j) R hR

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
