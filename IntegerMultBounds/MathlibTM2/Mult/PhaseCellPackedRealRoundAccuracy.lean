module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRoundAccuracy

/-! Actual real recovery fields feed packed normalization directly. The active
set may be either physical piece of a cyclic window, or its cropped core. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.LayerMachine

theorem packedRealRead_accuracy {A s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (q w a L : ℕ) (hw : 1 ≤ w)
    (D : ZMod s → GaussianInt) (hreal : ∀ i, (D i).im = 0)
    (hfits : ∀ i, Fits w (D i)) (active : Finset (ZMod s))
    (hfit : a+L ≤ s) (hactive : ∀ i ∈ active, a ≤ i.val ∧ i.val < a+L)
    (x : ZMod s → ℝ) (e : ℝ) (tail : List (Fin (A+4)))
    (herror : PhaseCellInterface.ErrorOn active (fun i => (value q (D i)).re) x e) :
    PhaseCellInterface.ErrorOn active
      (packedIntervalRead q w a (cstream A w (packedInterval a L D)++tail))
      (fun i => (x i : ℂ)) e := by
  intro i hi
  dsimp only
  rw [packedIntervalRead_decode q w a L D tail hfit i (hactive i hi).1 (hactive i hi).2,
    decodeWord_of_fits hA hw (D i) (hfits i)]
  have hv : value q (D i) = ((value q (D i)).re : ℂ) := by
    apply Complex.ext <;>
      simp only [value,hreal i,Int.cast_zero,zero_div,Complex.ofReal_re,Complex.ofReal_im]
  rw [hv,←Complex.ofReal_sub,Complex.norm_real]
  exact herror i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
