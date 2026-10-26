module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEncodedAmbient
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundedEncodedStream
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreRead
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputDecode

/-! The bounded integer field and decoded physical line agree exactly. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem encodedRange_ambient {A w q e s : ℕ} [NeZero s] (hw : 0 < w)
    (E : List (Fin (A+4))) (hE : E.length = s*w) (hbounded : EncodedRange A w q e E) :
    ∃ C : ZMod s → GaussianInt, E = cstream A w (chirpLine s C) ∧
      ∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^e := by
  obtain ⟨zs,rfl,hzs⟩ := hbounded
  have hlen : zs.length = s := Nat.mul_right_cancel hw (by simpa using hE)
  refine ⟨ambientOfWords zs hlen,by rw [chirpLine_ambientOfWords],?_⟩
  intro i
  exact hzs _ (ambientOfWords_mem zs hlen i)

theorem publishedCellRead_encodedField {A w q s : ℕ} [NeZero s] (hA : 4 ≤ A) (hw : 0 < w)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4))) (hfit : ∀ i, Fits w (C i)) (i : ZMod s) :
    publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s C)++tail) i = (value q (C i)).re := by
  simp only [publishedCellRead,ZMod.val_zero,Nat.sub_zero]
  rw [cstream_word w (chirpLine s C) tail i.val (by simpa using i.val_lt)]
  simp only [chirpLine,List.getElem_map,List.getElem_range,ZMod.natCast_zmod_val]
  rw [decodeWord_of_fits hA hw _ (hfit i)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
