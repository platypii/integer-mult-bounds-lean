module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairComponentsAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval

/-! Pair decoded local outputs without assuming their integer representatives fit.
This is the interface supplied by the actual real numerical batch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem value_decodePair_components {A : ℕ} (hA : 4 ≤ A) (q w : ℕ) (x y : GaussianInt) :
    (value q (decodeWord (csyms A w (pairComponentWord x y)))).re =
        (value q (decodeWord (csyms A w x))).re ∧
      (value q (decodeWord (csyms A w (pairComponentWord x y)))).im =
        (value q (decodeWord (csyms A w y))).re := by
  simp [decodeWord_csyms hA,value,pairComponentWord]

/-- Read the stored representative, including any fixed-width reduction. -/
theorem packedIntervalRead_decode {A s : ℕ} [NeZero s] (q w a L : ℕ)
    (F : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (hfit : a+L ≤ s) (i : ZMod s) (ha : a ≤ i.val) (hi : i.val < a+L) :
    packedIntervalRead q w a (cstream A w (packedInterval a L F)++tail) i =
      value q (decodeWord (csyms A w (F i))) := by
  rw [packedIntervalRead_eq q w a L F tail [] hfit i ha hi]
  simp only [pairedCellRead]
  rw [cstream_word w (chirpLine s F) [] i.val (by simpa using i.val_lt)]
  simp only [chirpLine,List.getElem_map,List.getElem_range,ZMod.natCast_zmod_val]

theorem packedIntervalRead_pair_components {A s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (q w a L : ℕ) (X Y : ZMod s → GaussianInt)
    (tailX tailY tail : List (Fin (A+4))) (hfit : a+L ≤ s)
    (i : ZMod s) (ha : a ≤ i.val) (hi : i.val < a+L) :
    let raw := cstream A w (packedInterval a L (fun j => pairComponentWord (X j) (Y j)))++tail
    (packedIntervalRead q w a raw i).re =
        (packedIntervalRead q w a (cstream A w (packedInterval a L X)++tailX) i).re ∧
      (packedIntervalRead q w a raw i).im =
        (packedIntervalRead q w a (cstream A w (packedInterval a L Y)++tailY) i).re := by
  dsimp only
  rw [packedIntervalRead_decode q w a L _ tail hfit i ha hi,
    packedIntervalRead_decode q w a L X tailX hfit i ha hi,
    packedIntervalRead_decode q w a L Y tailY hfit i ha hi]
  exact value_decodePair_components hA q w (X i) (Y i)

/-- The two scalar errors add once, independently of interval length and the
number of replicas. The hypotheses concern the actual decoded real packets. -/
theorem pairedPackedComponents_accuracy {A s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (q w a L : ℕ) (X Y : ZMod s → GaussianInt) (active : Finset (ZMod s))
    (hfit : a+L ≤ s) (hactive : ∀ i ∈ active, a ≤ i.val ∧ i.val < a+L)
    (z : ZMod s → ℂ) (eX eY : ℝ) (tailX tailY tail : List (Fin (A+4)))
    (hX : PhaseCellInterface.ErrorOn active
      (fun i => (packedIntervalRead q w a (cstream A w (packedInterval a L X)++tailX) i).re)
      (fun i => (z i).re) eX)
    (hY : PhaseCellInterface.ErrorOn active
      (fun i => (packedIntervalRead q w a (cstream A w (packedInterval a L Y)++tailY) i).re)
      (fun i => (z i).im) eY) :
    PhaseCellInterface.ErrorOn active
      (packedIntervalRead q w a
        (cstream A w (packedInterval a L (fun i => pairComponentWord (X i) (Y i)))++tail)) z (eX+eY) := by
  intro i hi
  obtain ⟨ha,hb⟩ := hactive i hi
  obtain ⟨hre,him⟩ := packedIntervalRead_pair_components hA q w a L X Y tailX tailY tail hfit i ha hb
  have hnorm := Complex.norm_le_abs_re_add_abs_im
    (packedIntervalRead q w a
      (cstream A w (packedInterval a L (fun j => pairComponentWord (X j) (Y j)))++tail) i-z i)
  have hx := hX i hi
  have hy := hY i hi
  simp only [Complex.sub_re,Complex.sub_im,hre,him,Real.norm_eq_abs] at hnorm hx hy
  exact hnorm.trans (add_le_add hx hy)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
