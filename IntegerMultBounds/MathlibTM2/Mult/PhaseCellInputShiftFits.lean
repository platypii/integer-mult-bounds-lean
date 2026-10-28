module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoreInputShift

/-! The unit input bound supplies both directions' signed word fits. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem inputShift_fits (p d w : ℕ) (hw : p+1+d+5 ≤ w) (z : GaussianInt)
    (hz : ‖value p z‖ ≤ 1) :
    TopFitsZ (w-d) z ∧ TopFitsZ w ((2 : GaussianInt)^d*z) := by
  have htop (k : ℕ) (x : GaussianInt) (hx : Fits k x) : TopFitsZ k x :=
    ⟨⟨(abs_lt.mp hx.1).1.le,(abs_lt.mp hx.1).2⟩,
      ⟨(abs_lt.mp hx.2).1.le,(abs_lt.mp hx.2).2⟩⟩
  refine ⟨htop (w-d) z ?_,htop w _ (halfGrid_fits p d w hw z hz)⟩
  apply fits_chirpOutput_bound p 0 0 (w-d) z _ (by omega)
  norm_num
  linarith

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
