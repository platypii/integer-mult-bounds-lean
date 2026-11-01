module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizedRecoveryFields
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreClassParameterBounds

/-! Ordinary unit-grid complex fields construct ordered core recovery jobs.
Both component expansion and precision normalization use their existing ABI. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.GeneratedRecoveryJob
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {p u l targetOut s t width L : ℕ} [NeZero s] {α gap : ℝ} {C : ZMod s → GaussianInt}

noncomputable def complexCoreClassJobs (hp : 2 ≤ p) (hpacket : 8*p ≤ 2^u) (hα : 0 < α)
    (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ gap*((t : ℝ)/s-1))
    (hbudget : α^2*gap ≤ p) (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (hC : ∀ a b, a ≤ b → b ≤ s → a < s →
      ∀ j, ‖value (packedHaloPrecision p l s t u (targetOut+1) 2 a b) (C j)‖ ≤ (2 : ℝ)^2)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (hwidth : 0 < width) (hsep : L+PhaseCellBand.width p u ≤ s)
    (Fs : List (ZMod s → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1) :
    Fin (coreGatherIndices s width (localityDepth p targetOut*PhaseCellBand.width p u) L).length → GeneratedRecoveryJob s :=
  fun i =>
    let k := (coreGatherIndices s width (localityDepth p targetOut*PhaseCellBand.width p u) L)[i.val]
    ofComplexBounds (coreClassParameterBounds hp hpacket hα hst hu hαu hθ hgap hbudget hband hpad hC hdom
      hwidth hsep k (List.getElem_mem i.isLt)) Fs hF

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.GeneratedRecoveryJob
