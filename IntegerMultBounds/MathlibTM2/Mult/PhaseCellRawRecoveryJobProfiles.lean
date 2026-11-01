module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryJobBounds

/-! Ordinary unit-grid complex fields determine a raw executable recovery job.
The inherited mathematical job derives normalized magnitudes and solutions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RawRecoveryJob
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s p u l target rhsExp t a b V : ℕ} [NeZero s] {α gap : ℝ} {C : ZMod s → GaussianInt}

theorem ofComplexBounds_profile
    (h : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α gap C)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (W : ℕ) (hW : 2*packedHaloPrecision p l s t u target rhsExp a b+8 ≤ W) :
    let r := ofComplexBounds h Fs hF W hW
    r.problem.p = p ∧ r.problem.l = l ∧ r.problem.t = t ∧ r.problem.u = u ∧
      r.problem.rhsExp = rhsExp ∧ r.problem.origin = a ∧ r.problem.span = b-a ∧
      r.problem.band = PhaseCellBand.width p u ∧ r.problem.Fs.length = 2*Fs.length ∧
      r.target = target ∧ r.W = W ∧ r.inputFields.length = 2*Fs.length ∧
      r.problem.target = boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp
        (haloBoundary s t (PhaseCellBand.width p u) a b).card := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,
    (GeneratedRecoveryJob.ofComplexBounds_fields h Fs hF).2,rfl,rfl,
    complexComponentFields_length Fs,rfl⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RawRecoveryJob
