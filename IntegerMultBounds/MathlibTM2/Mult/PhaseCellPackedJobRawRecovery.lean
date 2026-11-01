module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedJob
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryJobBounds

/-! The established ordered core-job language determines the raw recovery job
and every owned-core crop dimension, without additional format witnesses. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace PackedNormalizedJob
variable {A s : ℕ} [NeZero s]

/-- Reuse the actual halo constructor with the job's established precision and
common input width. The job contains no execution or recovery-output witness. -/
noncomputable def rawRecoveryJob (r : PackedNormalizedJob A s) : RawRecoveryJob s :=
  RawRecoveryJob.ofComplexBounds r.bounds r.Fs r.hF r.W (by
    have hq : r.q = packedHaloPrecision r.p r.l s r.t r.u (r.targetOut+1) 2 r.a r.b := r.hqSizing
    rw [← hq]
    exact r.hW)

theorem rawRecoveryJob_profile (r : PackedNormalizedJob A s) :
    r.rawRecoveryJob.problem.precision = r.q ∧ r.rawRecoveryJob.problem.origin = r.a ∧
      r.rawRecoveryJob.problem.span = r.b-r.a ∧ r.rawRecoveryJob.problem.wordWidth = 2*r.q+8 ∧
      r.rawRecoveryJob.W = r.W ∧ r.rawRecoveryJob.inputFields = complexComponentFields r.Fs ∧
      r.rawRecoveryJob.target = r.targetOut+1 := by
  have hq : r.rawRecoveryJob.problem.precision = r.q := r.hqSizing.symm
  have hw : r.rawRecoveryJob.problem.wordWidth = 2*r.rawRecoveryJob.problem.precision+8 := by
    unfold ReplicaHaloProblem.wordWidth ReplicaHaloProblem.precision executionWidth executionPrecision
    omega
  exact ⟨hq,rfl,rfl,hw.trans (by rw [hq]),rfl,rfl,rfl⟩

/-- Ordinary core geometry discharges the generated crop's containment premise. -/
theorem rawRecoveryJob_core_geometry (r : PackedNormalizedJob A s) :
    r.rawRecoveryJob.problem.origin+r.radius = coreStart r.coreWidth r.k ∧
      r.radius+coreLength s r.coreWidth r.k ≤ r.rawRecoveryJob.problem.span := by
  have ha := r.haEq
  have hl := r.hleft
  have hspan := r.haloLength
  obtain ⟨_,horigin,hsize,_,_,_,_⟩ := r.rawRecoveryJob_profile
  rw [horigin,hsize]
  omega

/-- The generated crop returns exactly the established owned-core packet. -/
theorem rawRecoveryJob_core_words (r : PackedNormalizedJob A s) (D : ZMod s → GaussianInt) :
    packedInterval (r.rawRecoveryJob.problem.origin+r.radius) (coreLength s r.coreWidth r.k) D =
      ownedCoreWords r.coreWidth r.k D := by
  rw [r.rawRecoveryJob_core_geometry.1]
  rfl

theorem rawRecoveryJob_core_vertices (r : PackedNormalizedJob A s) :
    haloVertices s (r.rawRecoveryJob.problem.origin+r.radius)
      (r.rawRecoveryJob.problem.origin+r.radius+coreLength s r.coreWidth r.k) = ownedCore s r.coreWidth r.k := by
  rw [r.rawRecoveryJob_core_geometry.1]
  rfl

end PackedNormalizedJob
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
