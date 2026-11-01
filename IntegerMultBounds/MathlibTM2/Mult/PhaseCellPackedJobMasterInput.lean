module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseMasterInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedJobRawRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryMasterValues

/-! Use the ordered core job's existing scalar width and fit proofs for master
setup, so recovery and normalization can share one physical scalar bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {A s : ℕ} [NeZero s]

def masterInput (r : PackedNormalizedJob A s) : InverseMasterInput s :=
  { B := r.Bcore, p := r.p, u := r.u, l := r.l, target := r.targetOut, t := r.t, a := r.a, b := r.b
    hst := r.bounds.hst, has := r.bounds.has, hbs := r.bounds.hbs, hband := r.bounds.hband
    band_room := r.hbandRoom, geometry_room := r.hgeometryRoom, precision_room := r.hprecisionRoom
    values_fit := r.hvaluesFit }

theorem rawRecoveryJob_masterValues (r : PackedNormalizedJob A s) :
    recoveryMasterValues r.rawRecoveryJob.problem = r.masterInput.masters := by
  have hfit : 2*packedHaloPrecision r.p r.l s r.t r.u (r.targetOut+1) 2 r.a r.b+8 ≤ r.W := by
    have hq : packedHaloPrecision r.p r.l s r.t r.u (r.targetOut+1) 2 r.a r.b = r.q := r.hqSizing.symm
    rw [hq]; exact r.hW
  simpa only [rawRecoveryJob,masterInput,InverseMasterInput.masters] using
    RawRecoveryJob.ofComplexBounds_masterValues r.bounds r.Fs r.hF r.W hfit

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
