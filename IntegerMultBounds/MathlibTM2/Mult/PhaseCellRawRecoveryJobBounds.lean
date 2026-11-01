module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryJob

/-! Ordinary unit-grid complex fields determine a raw executable recovery job.
The inherited mathematical job derives normalized magnitudes and solutions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RawRecoveryJob
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s p u l target rhsExp t a b V : ℕ} [NeZero s] {α gap : ℝ} {C : ZMod s → GaussianInt}

noncomputable def ofComplexBounds
    (h : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α gap C)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (W : ℕ) (hW : 2*packedHaloPrecision p l s t u target rhsExp a b+8 ≤ W) : RawRecoveryJob s := by
  let r := GeneratedRecoveryJob.ofComplexBounds h Fs hF
  have hf := GeneratedRecoveryJob.ofComplexBounds_fields h Fs hF
  refine { toGeneratedRecoveryJob := r
           inputFields := complexComponentFields Fs
           W := W
           fields := hf.1
           precision_fit := ?_
           format_fit := ?_ }
  · change p+1 ≤ packedHaloPrecision p l s t u target rhsExp a b
    dsimp [packedHaloPrecision,executionPrecision,executionExponent,inputExponent,sourceExponent]
    omega
  · have hw : r.problem.wordWidth = 2*r.problem.precision+8 := by
      unfold ReplicaHaloProblem.wordWidth ReplicaHaloProblem.precision executionWidth executionPrecision
      omega
    rw [hw]
    exact hW

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RawRecoveryJob
