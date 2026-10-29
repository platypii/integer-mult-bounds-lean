module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBoundaryFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolutionField

/-! Transfer recovery's field-level error to reads of the actual final local
buffer. Interior values come from the solve; boundary words retain their input. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem packedRecovery_read_error {A s t band a b q w : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hw : 0 < w) (hab : a ≤ b) (hb : b ≤ s)
    (Y D : ZMod s → GaussianInt) (hY : ∀ i, Fits w (Y i)) (hD : ∀ i, Fits w (D i))
    (tail after : List (Fin (A+4)))
    (hafter : after = cstream A w (packedInterval a (b-a) D)++tail)
    (hframe : PackedHaloWordFrame s t band a b w
      (cstream A w (packedInterval a (b-a) Y)++tail) after)
    (x : ZMod s → ℝ) (ε : ℝ)
    (herror : PhaseCellInterface.ErrorOn (haloVertices s a b)
      (fun i => if i ∈ haloInterior s t band a b then (value q (D i)).re else (value q (Y i)).re) x ε) :
    PhaseCellInterface.ErrorOn (haloVertices s a b) (fun i => (packedIntervalRead q w a after i).re) x ε := by
  have hfit : a+(b-a) ≤ s := by omega
  intro i hi
  obtain ⟨ha,hb'⟩ := (mem_haloVertices a b i).mp hi
  have hread (F : ZMod s → GaussianInt) (hF : ∀ j, Fits w (F j)) :
      packedIntervalRead q w a (cstream A w (packedInterval a (b-a) F)++tail) i = value q (F i) := by
    rw [packedIntervalRead_eq q w a (b-a) F tail [] hfit i ha (by omega)]
    exact pairedCellRead_encodedField hA hw F [] i (hF i)
  have he := herror i hi
  by_cases hiI : i ∈ haloInterior s t band a b
  · dsimp only
    rw [hafter,hread D hD]
    simpa only [ite_eq_left hiI] using he
  · dsimp only
    rw [hframe.read i ha hb' hiI,hread Y hY]
    simpa only [ite_eq_right hiI] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
