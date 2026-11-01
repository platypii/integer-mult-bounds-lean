module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryProblem
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryFactory

/-! Actual residuals and generated boundary factors determine the recovery
batch. All numerical contracts are proved once at an arbitrary replica index. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s A : ℕ} [NeZero s]

theorem ReplicaBoundaryFactorData.recovery_batch (H : ReplicaHaloProblem s) (target : ℕ)
    (columns : List (ZMod s → GaussianInt)) {S : Stacks 242 A}
    (hfactor : ReplicaBoundaryFactorData H target columns S)
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (hA : 4 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (Ds : List (ZMod s → GaussianInt)) (hlen : Ds.length = H.Fs.length)
    (hgood : ∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) Ds[j.val])
    (X : ℕ → ZMod s → ℝ)
    (hX : ∀ r < H.Fs.length, Solves (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) (X r)
      (fun i => (value H.precision (H.Fs.reverse.getD r (fun _ => 0) i)).re)) :
    ∃ B : ReplicaRecoveryBatch H target X, ∀ r : Fin H.Fs.length,
      B.boundary r = boundarySolutionField (haloBoundary s H.t H.band H.origin (H.origin+H.span))
        (replicaBoundarySolution H (12*H.band+1) columns (Ds.getD (H.Fs.length-1-r.val) (fun _ => 0))) := by
  let Y (r : Fin H.Fs.length) := boundarySolutionField (haloBoundary s H.t H.band H.origin (H.origin+H.span))
    (replicaBoundarySolution H (12*H.band+1) columns (Ds.getD (H.Fs.length-1-r.val) (fun _ => 0)))
  have hrows (r : Fin H.Fs.length) : Nonempty (ReplicaRecoveryRow H target r.val (Y r) (X r.val)) := by
    let j := H.Fs.length-1-r.val
    have hj : j < Ds.length := by have hr := r.isLt; dsimp only [j]; omega
    have hD : ReplicaCouplingResidualSpec H r.val (Ds.getD j (fun _ => 0)) := by
      have hh := hgood ⟨j,hj⟩
      have hrj : H.Fs.length-1-j = r.val := by have hr := r.isLt; dsimp only [j]; omega
      rw [hrj] at hh
      rw [List.getD_eq_getElem _ _ hj]
      exact hh
    obtain ⟨hlenS,hfits,haccuracy⟩ := ReplicaCouplingResidualSpec.boundary_solution H A
      (boundaryRecoveryTarget H.p target) (12*H.band+1) columns hA hp hwidth htarget
      hfactor.prepared.length hfactor.prepared.format hfactor.prepared.stage hfactor.error
      r.val r.isLt (Ds.getD j (fun _ => 0)) hD (X r.val) (hX r.val r.isLt)
    exact replicaRecoveryRow_of_boundary_solution H target r.val htarget hp hwidth r.isLt _ _
      hlenS hfits haccuracy (hX r.val r.isLt)
  refine ⟨⟨Y,fun r => Classical.choice (hrows r)⟩,?_⟩
  intro r
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
