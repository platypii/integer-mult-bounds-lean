module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
public import IntegerMultBounds.NLogN.PhaseCellCyclicPrincipalGeometry

/-! Cyclic cropping changes storage indices, not decoded ambient coordinates. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix

noncomputable def cyclicIntervalRead {A s : ℕ} [NeZero s] (q w a : ℕ)
    (raw : List (Fin (A+4))) (i : ZMod s) : ℂ :=
  packedIntervalRead q w 0 raw (i-(a : ZMod s))

theorem cyclicIntervalRead_eq {A s : ℕ} [NeZero s] (q w a n : ℕ)
    (hA : 4 ≤ A) (hw : 0 < w) (ha : a < s)
    (G : ZMod s → GaussianInt) (hfits : ∀ i, Fits w (G i))
    (tail : List (Fin (A+4))) (i : ZMod s) (hi : i ∈ cyclicPrincipalVertices s a n) :
    cyclicIntervalRead q w a (cstream A w (cyclicInterval a n G)++tail) i = value q (G i) := by
  have hpos : (i-(a : ZMod s)).val < n := by
    rw [cyclicPrincipalVertices_eq a n ha] at hi
    simpa [mem_cyclicHaloLayer,haloLayer,mem_haloVertices] using hi
  have hindex : ((a+(i-(a : ZMod s)).val : ℕ) : ZMod s) = i := by
    rw [Nat.cast_add,ZMod.natCast_zmod_val,add_comm,sub_add_cancel]
  unfold cyclicIntervalRead packedIntervalRead
  rw [Nat.sub_zero,cstream_word w _ tail _ (by simpa only [cyclicInterval_length] using hpos),
    cyclicInterval_get G hpos,hindex,decodeWord_of_fits hA hw _ (hfits i)]

theorem cyclicIntervalRead_error {A s : ℕ} [NeZero s] (q w a n : ℕ)
    (hA : 4 ≤ A) (hw : 0 < w) (ha : a < s)
    (G : ZMod s → GaussianInt) (hfits : ∀ i, Fits w (G i))
    (tail : List (Fin (A+4))) (x : ZMod s → ℝ) (epsilon : ℝ)
    (herror : PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (fun i => (value q (G i)).re) x epsilon) :
    PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (fun i => (cyclicIntervalRead q w a (cstream A w (cyclicInterval a n G)++tail) i).re) x epsilon := by
  intro i hi
  dsimp only
  rw [cyclicIntervalRead_eq q w a n hA hw ha G hfits tail i hi]
  exact herror i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
