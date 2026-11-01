module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCommonCoreJob
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedJobRawRecovery

/-! Proper-core mathematical jobs use exactly the established raw constructor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {A s : ℕ} [NeZero s]

theorem ofCoreCommon_rawRecoveryJob (p u l targetOut t width k V : ℕ) (α gap : ℝ)
    (C : ZMod s → GaussianInt) (Fs : List (ZMod s → GaussianInt))
    (bounds : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u)
      (target := targetOut+1) (rhsExp := 2)
      (a := (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p targetOut)).1)
      (b := (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p targetOut)).2) (V := V) α gap C)
    (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1) :
    (ofCoreCommon (A := A) p u l targetOut t width k V α gap C Fs bounds hF).rawRecoveryJob =
      RawRecoveryJob.ofComplexBounds bounds Fs hF (packedHaloCommonWidth p l s u (targetOut+1) 2)
        (packedHaloCommonWidth_fits p l s t u (targetOut+1) 2 _ _) := by
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
