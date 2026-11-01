module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedJobRawRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoverySolutionOrder
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedComponentLocality

/-! The raw constructor's local solution map uses the existing generated-window
locality proof and the established normalized row contract. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {A s : ℕ} [NeZero s]

noncomputable def localSolution (r : PackedNormalizedJob A s) (F : ZMod s → GaussianInt) : ZMod s → ℝ :=
  GeneratedRecoveryJob.solutionMap r.bounds (fun i => (2 : GaussianInt)^(r.q-r.p-1)*F i)

theorem localSolution_solves (r : PackedNormalizedJob A s) (F : ZMod s → GaussianInt) :
    Solves (realMatrix s r.t r.p r.u) (haloVertices s r.a r.b) (r.localSolution F)
      (fun i => (value r.q ((2 : GaussianInt)^(r.q-r.p-1)*F i)).re) := by
  have hq : packedHaloPrecision r.p r.l s r.t r.u (r.targetOut+1) 2 r.a r.b = r.q := r.hqSizing.symm
  simpa only [localSolution,hq] using GeneratedRecoveryJob.solutionMap_solves r.bounds
    (fun i => (2 : GaussianInt)^(r.q-r.p-1)*F i)

/-- The core job's chosen local solution is precisely the target order of the
actual raw constructor, including its reverse-indexed scalar replicas. -/
theorem rawRecoveryJob_solutionOrder (r : PackedNormalizedJob A s) :
    (List.finRange r.rawRecoveryJob.problem.Fs.length).reverse.map
      (fun j => r.rawRecoveryJob.solution j.val) =
      complexComponentTargets (r.Fs.map (componentSolution r.localSolution)) := by
  have hq : packedHaloPrecision r.p r.l s r.t r.u (r.targetOut+1) 2 r.a r.b = r.q := r.hqSizing.symm
  have hfit : 2*packedHaloPrecision r.p r.l s r.t r.u (r.targetOut+1) 2 r.a r.b+8 ≤ r.W := by
    rw [hq]
    exact r.hW
  have hy : (fun F : ZMod s → GaussianInt => GeneratedRecoveryJob.solutionMap r.bounds
      (fun i => (2 : GaussianInt)^(r.q-r.p-1)*F i)) = r.localSolution := rfl
  simpa only [rawRecoveryJob,hq,hy] using
    RawRecoveryJob.ofComplexBounds_solutionOrder r.bounds r.Fs r.hF r.W hfit

/-- After ordinary final rounding, reuse the manuscript's locality estimate to
obtain precisely the existing global row target and error budget. -/
theorem normalized_recovery_core_accuracy (r : PackedNormalizedJob A s)
    (Ds : List (ZMod s → GaussianInt)) (tail : List (Fin (A+4)))
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (ownedCore s r.coreWidth r.k)
      (packedIntervalRead r.p r.W (coreStart r.coreWidth r.k)
        (cstream A r.W (ownedCoreWords r.coreWidth r.k D)++tail)) z
      (2/(2 : ℝ)^r.p+(1/(2 : ℝ)^r.targetOut)/(2 : ℝ)^inverseNormalizationShift r.p))
      ((r.Fs.map (componentSolution r.localSolution)).map
        (fun z i => ((2 : ℂ)^inverseNormalizationShift r.p)⁻¹*z i)) Ds) :
    List.Forall₂ (fun F D => PhaseCellInterface.ErrorOn (ownedCore s r.coreWidth r.k)
      (packedIntervalRead r.p r.W (coreStart r.coreWidth r.k)
        (cstream A r.W (ownedCoreWords r.coreWidth r.k D)++tail)) (r.rowTarget F) r.rowError) r.Fs Ds := by
  have ht (F : ZMod s → GaussianInt) :
      (fun i => ((2 : ℂ)^inverseNormalizationShift r.p)⁻¹*componentSolution r.Y F i) = r.rowTarget F := rfl
  simpa only [ht,rowError] using normalizedPackedComponents_generated_accuracy r.bounds.hst r.bounds.hα
    r.coreWidth r.p r.u r.localityTarget r.k r.q (inverseNormalizationShift r.p) r.W
    r.bounds.hp r.hpq r.bounds.hwidth r.bounds.hαu r.bounds.hθ r.bounds.hgap r.bounds.hbudget
    r.Fs r.hF r.localSolution r.Y (by intro F _; rw [← r.hhalo]; exact r.localSolution_solves F)
    r.hY Ds tail (2/(2 : ℝ)^r.p+(1/(2 : ℝ)^r.targetOut)/(2 : ℝ)^inverseNormalizationShift r.p) hgood

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
