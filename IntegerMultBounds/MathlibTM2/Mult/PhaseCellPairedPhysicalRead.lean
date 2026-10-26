module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairComponentsAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreRead

/-! Pair actual decoded component words, without a new integer-fit assumption. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem pairedCellRead_parts {A q w s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (X Y : ZMod s → GaussianInt) (tail tailX tailY : List (Fin (A+4))) (i : ZMod s) :
    let G := fun j => pairComponentWord (X j) (Y j)
    (pairedCellRead q w (cstream A w (chirpLine s G)++tail) i).re =
        publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s X)++tailX) i ∧
      (pairedCellRead q w (cstream A w (chirpLine s G)++tail) i).im =
        publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s Y)++tailY) i := by
  dsimp only
  have hword (C : ZMod s → GaussianInt) (rest : List (Fin (A+4))) :
      ((cstream A w (chirpLine s C)++rest).drop (i.val*w)).take w = csyms A w (C i) := by
    rw [cstream_word w (chirpLine s C) rest i.val (by simpa using i.val_lt)]
    simp [chirpLine]
  simp only [pairedCellRead,publishedCellRead,ZMod.val_zero,Nat.sub_zero,hword,
    decodeWord_csyms hA,pairComponentWord,value]
  trivial

theorem pairedComponents_physical_accuracy {A q w s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (X Y : ZMod s → GaussianInt) (active : Finset (ZMod s)) (z : ZMod s → ℂ) (eX eY : ℝ)
    (tail tailX tailY : List (Fin (A+4)))
    (hX : PhaseCellInterface.ErrorOn active
      (fun i => publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s X)++tailX) i) (fun i => (z i).re) eX)
    (hY : PhaseCellInterface.ErrorOn active
      (fun i => publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s Y)++tailY) i) (fun i => (z i).im) eY) :
    PhaseCellInterface.ErrorOn active
      (pairedCellRead q w (cstream A w (chirpLine s (fun i => pairComponentWord (X i) (Y i)))++tail))
      z (eX+eY) := by
  intro i hi
  have hparts := pairedCellRead_parts (q := q) (w := w) hA X Y tail tailX tailY i
  have hnorm := Complex.norm_le_abs_re_add_abs_im
    (pairedCellRead q w (cstream A w (chirpLine s (fun i => pairComponentWord (X i) (Y i)))++tail) i-z i)
  have hx := hX i hi
  have hy := hY i hi
  simp only [Complex.sub_re,Complex.sub_im,hparts.1,hparts.2,Real.norm_eq_abs] at hnorm hx hy
  exact hnorm.trans (add_le_add hx hy)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
